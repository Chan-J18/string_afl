/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <unordered_map>
#include <unordered_set>


#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugInfo.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      std::unordered_map<BasicBlock *, u32> basicBlockMap;
      std::unordered_map<u32,u32> passSet;
      std::unordered_set<std::string> handledFunc;
      std::unordered_set<Value*> stringValue;
     
      AFLCoverage() : ModulePass(ID) { }

      bool doInitialization(Module &M) override;
      bool runOnModule(Module &M) override;

      void handleInst(Instruction *inst,  std::unordered_set<Value*> &localStringValue);
      void handleFunc(Function *func);
      bool isOprendStringRelated(Value* value,std::unordered_set<Value*> &localStringValue);
      bool isMetadateStringRelated(Value* value);
      bool isTypeStringRelated(DIType* dtype);
      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;


bool AFLCoverage::doInitialization(Module &M) {
  /* Initialize id for each basic block */
  u32 rand_seed;
  char *rand_seed_str = getenv("AFL_RAND_SEED");

  if (rand_seed_str && sscanf(rand_seed_str, "%u", &rand_seed))
    srand(rand_seed);

  for (auto &F : M)
    for (auto &BB : F) {
      u32 cur_loc = AFL_R(MAP_SIZE);
      basicBlockMap.insert(std::pair<BasicBlock *, u32>(&BB, cur_loc));
    }

  for (GlobalVariable &gvar : M.globals()) {

    Metadata* md = gvar.getMetadata("dbg");
    
    if(md){
      if(isa<DIGlobalVariableExpression>(md)){
      
        DIGlobalVariableExpression *divExpr = dyn_cast<DIGlobalVariableExpression>(md);
        DIGlobalVariable *divGvar = divExpr->getVariable();
      
        if(isTypeStringRelated(divGvar->getType())){
          stringValue.insert(&gvar);
        }
      }
    }
  }

  return true;
}

bool AFLCoverage::isOprendStringRelated(Value *value,std::unordered_set<Value*> &localStringValue){

  if(localStringValue.find(value)!=localStringValue.end()||stringValue.find(value)!=stringValue.end()){
    return true;
  }else if(isa<ConstantExpr>(value)){
    ConstantExpr* constExpr = dyn_cast<ConstantExpr>(value);
    if(constExpr->getOpcode() == Instruction::GetElementPtr){
      Value *basePtr =constExpr->getOperand(0);
      return isOprendStringRelated(basePtr,localStringValue);
    }
  }

  return false;
}

bool AFLCoverage::isMetadateStringRelated(Value* value){

  if(isa<MetadataAsValue>(value)){

    Metadata* md = cast<MetadataAsValue>(*value).getMetadata();
    
    if (isa<DILocalVariable>(*md)) {
      
      DIType* dtype = cast<DILocalVariable>(*md).getType();

      if(nullptr == dtype){
        md->print(errs());
        errs()<<"\n";
      }

      if(nullptr!=dtype && (dtype)) return true;
    }
  }
  return false;
}

bool AFLCoverage::isTypeStringRelated(DIType* dtype){

  /* handle dtype because compositeType */
  if(isa<DICompositeType>(dtype)){
    
    DICompositeType* dctype = dyn_cast<DICompositeType>(dtype);
    
    //没有baseType，查看name
    if(!dctype->getBaseType()){
      if(0==dctype->getName().str().compare("basic_string<char, std::char_traits<char>, std::allocator<char> >")){
        return true;
      }else return false;
    }
    
    if(!dctype->getBaseType()->getName().str().compare("char")) return true;

  }else if(isa<DIDerivedType>(dtype)){

    DIDerivedType * ddtype = dyn_cast<DIDerivedType>(dtype);
    DIType *baseType = ddtype->getBaseType();

    while(isa<DIDerivedType>(baseType)){
      ddtype = dyn_cast<DIDerivedType>(baseType);
      baseType = ddtype->getBaseType();
    }
    if(ddtype->getName().str().compare("string")) return true;
    //得到的baseType可能是DICompositeType
    return isTypeStringRelated(baseType);
    // if(!baseType->getName().str().compare("char")) return true;
  }else if(isa<DIBasicType>(dtype)){

    if(!dyn_cast<DIBasicType>(dtype)->getName().str().compare("char")) return true;
  }
  return false;
}

void AFLCoverage::handleInst(Instruction *inst,  std::unordered_set<Value*> &localStringValue){
  /* check the oprends of the Instruction is in the string related table ?
    yes: check which king of the Instruction:
      -Call: handleFunc(calledFunc) while inserting the string related arguments into the table;
      -Store: insert the second oprend value into the table;
      -Load: insert ...   return true;
    no: return false;
  */
  if(isa<CallInst>(inst)){

    CallInst* calle = dyn_cast<CallInst>(inst);
    Function* calledFunc = calle->getCalledFunction();

    /* if the function name is dbg.declare 
        insert the variable into stringValue 
    */
    if(calledFunc){
        /* if function arguments is string related, insert the responsitive 
      argument into stringValue 
      if function is string api (fucntion name is strcmp ...), then insert
      the the call result value into stringValue.
      */
      /* Avoid repeating, insert the handled function into handledFunc */
      int argIndex = 0;
      bool isHandle = false;

      // default str api not need to trace function args
      for (Argument &arg : calledFunc->args()) {

        Value *actualArg = calle->getArgOperand(argIndex);
      
        if(isOprendStringRelated(actualArg,localStringValue)){
          
          isHandle = true;
          localStringValue.insert(calle);
        }

        argIndex++;
      }

      if(isHandle&&!calledFunc->getName().empty()){  
      
        std::string funcName = calledFunc->getName().str();

        if(handledFunc.find(funcName)==handledFunc.end()){
          
          handledFunc.insert(funcName);
          handleFunc(calledFunc);
        }
      }
   }
  }
  else if(isa<StoreInst>(inst)){

    StoreInst* storeInst = dyn_cast<StoreInst>(inst);
    
    Value* value = storeInst->getValueOperand();
    Value* address = storeInst->getPointerOperand();

    if(isOprendStringRelated(value,localStringValue))
      localStringValue.insert(address);
  
  }else if(isa<LoadInst>(inst)){

    LoadInst* loadInst = dyn_cast<LoadInst>(inst);
    Value* address = loadInst->getPointerOperand();

    if(isOprendStringRelated(address,localStringValue))
      localStringValue.insert(loadInst);
    
  }else if(isa<ICmpInst>(inst)||isa<BinaryOperator>(inst)){   
    
    Value* op1 = inst->getOperand(0);
    Value* op2 = inst->getOperand(1);

    
    if(isOprendStringRelated(op1,localStringValue)||isOprendStringRelated(op2,localStringValue))
      localStringValue.insert(inst);
        
  }else if(isa<BranchInst>(inst)){
    
    BranchInst* brInst = dyn_cast<BranchInst>(inst);
    
    if(brInst->isConditional()){
      Value* cond = brInst->getCondition();

      if(isOprendStringRelated(cond,localStringValue))
        localStringValue.insert(brInst);
    }

  }else if(isa<GetElementPtrInst>(inst)){

    GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(inst);

    Value *basePtr = gepInst->getPointerOperand();

    if(isOprendStringRelated(basePtr,localStringValue))
      localStringValue.insert(inst);

  }else if(isa<SExtInst>(inst)){

    SExtInst *sextInst = dyn_cast<SExtInst>(inst);

    if(isOprendStringRelated(sextInst->getOperand(0),localStringValue))
      localStringValue.insert(inst);

  }else if(isa<ZExtInst>(inst)){
    
    ZExtInst *zextInst = dyn_cast<ZExtInst>(inst);

    if(isOprendStringRelated(zextInst->getOperand(0),localStringValue))
      localStringValue.insert(inst);

  }else if(isa<TruncInst>(inst)){

    TruncInst *truncInst = dyn_cast<TruncInst>(inst);

    if(isOprendStringRelated(truncInst->getOperand(0),localStringValue))
      localStringValue.insert(inst);

  }else if(isa<InvokeInst>(inst)){
    
    InvokeInst *invokeInst = dyn_cast<InvokeInst>(inst);
    Function* calledFunc = invokeInst->getCalledFunction();  
    bool isHandle = false;

    for (unsigned i = 0; i < invokeInst->getNumArgOperands(); i++) {
      
      Value *arg = invokeInst->getArgOperand(i);
  
      if(isOprendStringRelated(arg,localStringValue)){

        isHandle = true;
        localStringValue.insert(invokeInst);
      }
    }

    if(calledFunc){

      if(isHandle&&!calledFunc->getName().empty()){  
      
        std::string funcName = calledFunc->getName().str();

        if(handledFunc.find(funcName)==handledFunc.end()){

          handledFunc.insert(funcName);
          handleFunc(calledFunc);
        }
      }
    }

  }else if(isa<PHINode>(inst)){
    
    PHINode *phiNode = dyn_cast<PHINode>(inst);

    for (unsigned i = 0; i < phiNode->getNumIncomingValues(); ++i) {

      Value *incomingValue = phiNode->getIncomingValue(i);

      if(isOprendStringRelated(incomingValue, localStringValue))
      {  
        localStringValue.insert(phiNode);
        break;
      }
    }
  }
}

void AFLCoverage::handleFunc(Function *func){

  std::unordered_set<Value*> localStringValue;

  for(BasicBlock &blk:*func){
    for(Instruction &inst:blk){
      if(isa<CallInst>(inst)){

        CallInst* calle = dyn_cast<CallInst>(&inst);
        Function* calledFunc = calle->getCalledFunction(); 

        if(calledFunc&&!calledFunc->getName().empty()){
          
          if(calledFunc->getName() == "llvm.dbg.declare"||
            calledFunc->getName() == "llvm.dbg.value"){
            
            Value* value = calle->getArgOperand(0);
            Value *scope = calle->getArgOperand(1);

            if(isMetadateStringRelated(scope)){

              MetadataAsValue *mav = dyn_cast<MetadataAsValue>(value);

              if (mav) {

                ValueAsMetadata* vam = dyn_cast<ValueAsMetadata>(mav->getMetadata());
                
                if (vam) {

                  Value* val = vam->getValue();
                  
                  if (val) localStringValue.insert(val); 
                }
              }         
            }
          }
        } 
      }
    }
  }

  for(BasicBlock &blk: *func){
    for(Instruction &inst: blk){   
      handleInst(&inst,localStringValue);
    }
  }

  for(Value* value:localStringValue){
    if(isa<BranchInst>(value)){
      stringValue.insert(dyn_cast<BranchInst>(value));
    }
  }
}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  Type *voidType = Type::getVoidTy(C);
  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  FunctionCallee TraceBB = (&M)->getOrInsertFunction(
      "__trace_visit_string",
      FunctionType::get(voidType, {Int32Ty,Int32Ty}, false));

  FunctionCallee PassFunc = (&M)->getOrInsertFunction(
      "__trace_pass_string",
      FunctionType::get(voidType, {Int32Ty,Int32Ty,Int32Ty}, false));


  /* Instrument all the things! */

  int instBrNum = 0;
  int brNum = 0 ;
  Function* mainFunc =  M.getFunction("main");
  StringRef soureceFileName;

  for (auto CU : M.debug_compile_units()) {

    StringRef fileName = CU->getFilename();
   
    if(soureceFileName.empty())  soureceFileName = fileName;
    else if(fileName == soureceFileName) break;
    else return false;

  }


  /* handleFunc ：handle BasicBlocks of the Function A Set keep handledFunction avoid repeating
    finish, get a table about the string related values.
  */
  
  
  handleFunc(mainFunc);
  
  // FILE* file = freopen("output.log", "w", stderr);
  // if (!file) {
  //   errs() << "Failed to open log file\n";
  //   return 1;
  // }


  for (auto &F : M){
    for (auto &BB : F) {
      
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */
      
      unsigned int cur_loc = basicBlockMap[&BB];
      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);
      Instruction *lastInst = BB.getTerminator();
      
      /* Insert string related counter:
      Check brInst, If is string related, insert couter */
      if(nullptr != lastInst){
        if(isa<BranchInst>(lastInst)){

          BranchInst *brInst = dyn_cast<BranchInst>(lastInst);

          if (brInst->isConditional()){

            /* If brInst is string related, insert visit couter, insert pass_loc */
            if(stringValue.find(brInst)!=stringValue.end()){

              /* Debug Msg */
              Metadata *md = brInst->getMetadata("dbg");
              if(md){
                if(isa<DILocation>(md)){

                  DILocation *loc = dyn_cast<DILocation>(md);

                  if(soureceFileName == loc->getFilename()){

                    errs() << soureceFileName << "    Line: " << loc->getLine() << "\n";

                    /* Visit */
                    BasicBlock *trueBB = brInst->getSuccessor(0);
                    ConstantInt *Pass_Loc = ConstantInt::get(Int32Ty, basicBlockMap[trueBB]);    
                    IRB.CreateCall(TraceBB,{Pass_Loc,CurLoc});
                  
                    /* Pass */
                    passSet.insert(std::pair<u32,u32>(basicBlockMap[trueBB],cur_loc));
                    instBrNum++;

                  }
                }
              }
            }
            brNum++;
          } 
        }
      }

      /* Load prev_loc */
      
      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      /* If pass, insert the pass string counter */
      if(passSet.find(cur_loc)!=passSet.end()){
        IRB.CreateCall(PassFunc,{ConstantInt::get(Int32Ty, cur_loc),PrevLoc,ConstantInt::get(Int32Ty, passSet[cur_loc])});
        passSet.erase(cur_loc);
      }
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
    }
  }
  // 关闭文件
  // fclose(file);
  
  /* Say something nice. */
  if (!be_quiet) {

    if (!brNum) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations, the number of all conditional branch %u  (%s mode, ratio %u%%).",
             instBrNum,brNum, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
