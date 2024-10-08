/*
  Copyright 2013 Google LLC All rights reserved.

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
   american fuzzy lop - map display utility
   ----------------------------------------

   Written and maintained by Michal Zalewski <lcamtuf@google.com>

   A very simple tool that runs the targeted binary and displays
   the contents of the trace bitmap in a human-readable form. Useful in
   scripts to eliminate redundant inputs and perform other checks.

   Exit code is 2 if the target program crashes; 1 if it times out or
   there is a problem executing it; or 0 if execution is successful.
*/

#define AFL_MAIN
#include "android-ashmem.h"

#include "config.h"
#include "types.h"
#include "debug.h"
#include "alloc-inl.h"
#include "hash.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
#include <fcntl.h>
#include <dirent.h>

#include <sys/wait.h>
#include <sys/time.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/resource.h>
#include <sys/mman.h>

static s32 child_pid;                 /* PID of the tested program         */

static u8* trace_bits;                /* SHM with instrumentation bitmap   */

static u8 *out_file,                  /* Trace output file                 */
          *out_dir,
          *doc_path,                  /* Path to docs                      */
          *target_path,               /* Path to target binary             */
          *at_file,
          *in_file,
          *in_dir;                   /* Substitution string for @@        */

static u32 exec_tmout;                /* Exec timeout (ms)                 */
static u64 total_execs=0;
static u64 mem_limit = MEM_LIMIT;     /* Memory limit (MB)                 */

static s32 shm_id;                    /* ID of the SHM region              */
static s32 bb_shm_id;                 /* ID of the Basic block region     */
static s32 pass_shm_id;                 /* ID of the Basic block region     */

static u32* basic_blk_cov;            /* SHM with bitmap for block hits   */
static u32* pass_string_cov;            /* SHM with bitmap for block hits   */

static u8 is_seed_visit=0,
          is_seed_pass=0;

static u32 br_string_pass[MAP_SIZE],
           br_string_visit[MAP_SIZE], 
           seed_string_pass[MAP_SIZE],
           seed_string_visit[MAP_SIZE],
           seed_first_pass[MAP_SIZE],
           seed_first_visit[MAP_SIZE];

static u64 seed_num_visit=0,seed_num_pass=0;

static u8  quiet_mode,                /* Hide non-essential messages?      */
           edges_only,                /* Ignore hit counts?                */
           cmin_mode,                 /* Generate output in afl-cmin mode? */
           binary_mode,               /* Write output as a binary map      */
           keep_cores;                /* Allow coredumps?                  */

static volatile u8
           stop_soon,                 /* Ctrl-C pressed?                   */
           child_timed_out,           /* Child timed out?                  */
           child_crashed;             /* Child crashed?                    */

/* Classify tuple counts. Instead of mapping to individual bits, as in
   afl-fuzz.c, we map to more user-friendly numbers between 1 and 8. */

static const u8 count_class_human[256] = {

  [0]           = 0,
  [1]           = 1,
  [2]           = 2,
  [3]           = 3,
  [4 ... 7]     = 4,
  [8 ... 15]    = 5,
  [16 ... 31]   = 6,
  [32 ... 127]  = 7,
  [128 ... 255] = 8

};

static const u8 count_class_binary[256] = {

  [0]           = 0,
  [1]           = 1,
  [2]           = 2,
  [3]           = 4,
  [4 ... 7]     = 8,
  [8 ... 15]    = 16,
  [16 ... 31]   = 32,
  [32 ... 127]  = 64,
  [128 ... 255] = 128

};

static void classify_counts(u8* mem, const u8* map) {

  u32 i = MAP_SIZE;

  if (edges_only) {

    while (i--) {
      if (*mem) *mem = 1;
      mem++;
    }

  } else {

    while (i--) {
      *mem = map[*mem];
      mem++;
    }

  }

}


/* Get rid of shared memory (atexit handler). */

static void remove_shm(void) {

  shmctl(shm_id, IPC_RMID, NULL);

}


/* Configure shared memory. */

static void setup_shm(void) {

  u8* shm_str;
  u8* bb_shm_str;
  u8* pass_shm_str;

  shm_id = shmget(IPC_PRIVATE, MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);

  if (shm_id < 0) PFATAL("shmget() failed");

  bb_shm_id = shmget(IPC_PRIVATE, sizeof(u32) * MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);

  if (bb_shm_id < 0) PFATAL("shmget() failed for basic block");

  pass_shm_id = shmget(IPC_PRIVATE, sizeof(u32) * MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);

  if(pass_shm_id<0) PFATAL("shmget() failed for pass string ");
  
  atexit(remove_shm);

  shm_str = alloc_printf("%d", shm_id);
  bb_shm_str = alloc_printf("%d", bb_shm_id);
  pass_shm_str = alloc_printf("%d",pass_shm_id);

  setenv(SHM_ENV_VAR, shm_str, 1);
  setenv(BB_SHM_ENV, bb_shm_str, 1);
  setenv(PASS_SHN_EVN,pass_shm_str,1);

  ck_free(shm_str);
  ck_free(bb_shm_str);
  ck_free(pass_shm_str);

  trace_bits = shmat(shm_id, NULL, 0);
  basic_blk_cov = shmat(bb_shm_id, NULL, 0);
  pass_string_cov = shmat(pass_shm_id,NULL,0);
  //实际共享的内存空间
  memset(basic_blk_cov, 0, sizeof(u32) * MAP_SIZE);
  memset(pass_string_cov, 0, sizeof(u32) * MAP_SIZE);
  //非共享的内存空间
  memset(br_string_pass, 0, sizeof(u32) * MAP_SIZE);
  memset(br_string_visit, 0, sizeof(u32) * MAP_SIZE);
  memset(seed_string_pass, 0, sizeof(u32) * MAP_SIZE);
  memset(seed_string_visit, 0, sizeof(u32) * MAP_SIZE);
  memset(seed_first_pass, 0, sizeof(u32) * MAP_SIZE);
  memset(seed_first_visit, 0, sizeof(u32) * MAP_SIZE);
  
  if (trace_bits == (void *)-1) PFATAL("shmat() failed");

}

/* Write results. */

static u32 write_results(void) {

  s32 fd;
  u32 i, ret = 0;

  u8  cco = !!getenv("AFL_CMIN_CRASHES_ONLY"),
      caa = !!getenv("AFL_CMIN_ALLOW_ANY");

  if (!strncmp(out_file, "/dev/", 5)) {

    fd = open(out_file, O_WRONLY, 0600);
    if (fd < 0) PFATAL("Unable to open '%s'", out_file);

  } else if (!strcmp(out_file, "-")) {

    fd = dup(1);
    if (fd < 0) PFATAL("Unable to open stdout");

  } else {

    unlink(out_file); /* Ignore errors */
    fd = open(out_file, O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd < 0) PFATAL("Unable to create '%s'", out_file);

  }


  if (binary_mode) {

    for (i = 0; i < MAP_SIZE; i++)
      if (trace_bits[i]) ret++;
    
    ck_write(fd, trace_bits, MAP_SIZE, out_file);
    close(fd);

  } else {

    FILE* f = fdopen(fd, "w");

    if (!f) PFATAL("fdopen() failed");

    for (i = 0; i < MAP_SIZE; i++) {

      if (!trace_bits[i]) continue;
      ret++;

      if (cmin_mode) {

        if (child_timed_out) break;
        if (!caa && child_crashed != cco) break;

        fprintf(f, "%u%u\n", trace_bits[i], i);

      } else fprintf(f, "%06u:%u\n", i, trace_bits[i]);

    }
  
    fclose(f);

  }

  return ret;

}


/* Handle timeout signal. */

static void handle_timeout(int sig) {

  child_timed_out = 1;
  if (child_pid > 0) kill(child_pid, SIGKILL);

}


/* Execute target application. */

static void run_target(char** argv) {

  static struct itimerval it;
  int status = 0;

  if (!quiet_mode)
    SAYF("-- Program output begins --\n" cRST);

  memset(trace_bits, 0, MAP_SIZE);
  memset(pass_string_cov, 0, MAP_SIZE);
  memset(basic_blk_cov, 0, MAP_SIZE);

  MEM_BARRIER();

  child_pid = fork();

  if (child_pid < 0) PFATAL("fork() failed");

  if (!child_pid) {

    struct rlimit r;

    if (quiet_mode) {

      s32 fd = open("/dev/null", O_RDWR);
    
      if (fd < 0 || dup2(fd, 1) < 0 || dup2(fd, 2) < 0) {
        *(u32*)trace_bits = EXEC_FAIL_SIG;
        PFATAL("Descriptor initialization failed");
      }

      close(fd);

    }

    if (mem_limit) {

      r.rlim_max = r.rlim_cur = ((rlim_t)mem_limit) << 20;

#ifdef RLIMIT_AS

      setrlimit(RLIMIT_AS, &r); /* Ignore errors */

#else

      setrlimit(RLIMIT_DATA, &r); /* Ignore errors */

#endif /* ^RLIMIT_AS */

    }

    if (!keep_cores) r.rlim_max = r.rlim_cur = 0;
    else r.rlim_max = r.rlim_cur = RLIM_INFINITY;

    setrlimit(RLIMIT_CORE, &r); /* Ignore errors */

    if (!getenv("LD_BIND_LAZY")) setenv("LD_BIND_NOW", "1", 0);

    setsid();
    
    execv(target_path, argv);

    *(u32*)trace_bits = EXEC_FAIL_SIG;
    exit(0);

  }

  /* Configure timeout, wait for child, cancel timeout. */

  if (exec_tmout) {

    child_timed_out = 0;
    it.it_value.tv_sec = (exec_tmout / 1000);
    it.it_value.tv_usec = (exec_tmout % 1000) * 1000;

  }

  setitimer(ITIMER_REAL, &it, NULL);

  if (waitpid(child_pid, &status, 0) <= 0) FATAL("waitpid() failed");

  child_pid = 0;
  it.it_value.tv_sec = 0;
  it.it_value.tv_usec = 0;
  setitimer(ITIMER_REAL, &it, NULL);

  MEM_BARRIER();

  /* Clean up bitmap, analyze exit condition, etc. */

  if (*(u32*)trace_bits == EXEC_FAIL_SIG)
    FATAL("Unable to execute '%s'", argv[0]);

  classify_counts(trace_bits, binary_mode ?
                  count_class_binary : count_class_human);

  if (!quiet_mode)
    SAYF(cRST "-- Program output ends --\n");

  if (!child_timed_out && !stop_soon && WIFSIGNALED(status))
    child_crashed = 1;

  if (!quiet_mode) {

    if (child_timed_out)
      SAYF(cLRD "\n+++ Program timed off +++\n" cRST);
    else if (stop_soon)
      SAYF(cLRD "\n+++ Program aborted by user +++\n" cRST);
    else if (child_crashed)
      SAYF(cLRD "\n+++ Program killed by signal %u +++\n" cRST, WTERMSIG(status));

  }


}


/* Handle Ctrl-C and the like. */

static void handle_stop_sig(int sig) {

  stop_soon = 1;

  if (child_pid > 0) kill(child_pid, SIGKILL);

}


/* Do basic preparations - persistent fds, filenames, etc. */

static void set_up_environment(void) {

  setenv("ASAN_OPTIONS", "abort_on_error=1:"
                         "detect_leaks=0:"
                         "symbolize=0:"
                         "allocator_may_return_null=1", 0);

  setenv("MSAN_OPTIONS", "exit_code=" STRINGIFY(MSAN_ERROR) ":"
                         "symbolize=0:"
                         "abort_on_error=1:"
                         "allocator_may_return_null=1:"
                         "msan_track_origins=0", 0);

  if (getenv("AFL_PRELOAD")) {
    setenv("LD_PRELOAD", getenv("AFL_PRELOAD"), 1);
    setenv("DYLD_INSERT_LIBRARIES", getenv("AFL_PRELOAD"), 1);
  }

}


/* Setup signal handlers, duh. */

static void setup_signal_handlers(void) {

  struct sigaction sa;

  sa.sa_handler   = NULL;
  sa.sa_flags     = SA_RESTART;
  sa.sa_sigaction = NULL;

  sigemptyset(&sa.sa_mask);

  /* Various ways of saying "stop". */

  sa.sa_handler = handle_stop_sig;
  sigaction(SIGHUP, &sa, NULL);
  sigaction(SIGINT, &sa, NULL);
  sigaction(SIGTERM, &sa, NULL);

  /* Exec timeout notifications. */

  sa.sa_handler = handle_timeout;
  sigaction(SIGALRM, &sa, NULL);

}


/* Detect @@ in args. */

  static void detect_file_args(char** argv) {

    u32 i = 0;
    u8* cwd = getcwd(NULL, 0);

    if (!cwd) PFATAL("getcwd() failed");

    while (argv[i]) {

      u8* aa_loc = strstr(argv[i], "@@");

      if (aa_loc) {

        u8 *aa_subst, *n_arg;
        
        // at_file设置为.cur_input  
      
        at_file = alloc_printf("%s/.cur_seed",in_dir);
          //FATAL("@@ syntax is not supported by this tool.");
        SAYF("using the default at_file path!\n");
        
        /* Be sure that we're always using fully-qualified paths. */

        if (at_file[0] == '/') aa_subst = at_file;
        else aa_subst = alloc_printf("%s/%s", cwd, at_file);

        /* Construct a replacement argv value. */

        *aa_loc = 0;
        n_arg = alloc_printf("%s%s%s", argv[i], aa_subst, aa_loc + 2);
        argv[i] = n_arg;
        *aa_loc = '@';

        if (at_file[0] != '/') ck_free(aa_subst);

      }

      i++;

    }

    free(cwd); /* not tracked */

  }


/* Show banner. */

static void show_banner(void) {

  SAYF(cCYA "afl-showmap " cBRI VERSION cRST " by <lcamtuf@google.com>\n");

}

/* Display usage hints. */

static void usage(u8* argv0) {

  show_banner();

  SAYF("\n%s [ options ] -- /path/to/target_app [ ... ]\n\n"

       "Required parameters:\n\n"

       "  -o file       - file to write the trace data to\n\n"

       "Execution control settings:\n\n"

       "  -t msec       - timeout for each run (none)\n"
       "  -m megs       - memory limit for child process (%u MB)\n"
       "  -Q            - use binary-only instrumentation (QEMU mode)\n\n"

       "Other settings:\n\n"

       "  -q            - sink program's output and don't show messages\n"
       "  -e            - show edge coverage only, ignore hit counts\n"
       "  -c            - allow core dumps\n"
       "  -V            - show version number and exit\n\n"

       "This tool displays raw tuple data captured by AFL instrumentation.\n"
       "For additional help, consult %s/README.\n\n" cRST,

       argv0, MEM_LIMIT, doc_path);

  exit(1);

}


/* Find binary. */

static void find_binary(u8* fname) {

  u8* env_path = 0;
  struct stat st;

  if (strchr(fname, '/') || !(env_path = getenv("PATH"))) {

    target_path = ck_strdup(fname);

    if (stat(target_path, &st) || !S_ISREG(st.st_mode) ||
        !(st.st_mode & 0111) || st.st_size < 4)
      FATAL("Program '%s' not found or not executable", fname);

  } else {

    while (env_path) {

      u8 *cur_elem, *delim = strchr(env_path, ':');

      if (delim) {

        cur_elem = ck_alloc(delim - env_path + 1);
        memcpy(cur_elem, env_path, delim - env_path);
        delim++;

      } else cur_elem = ck_strdup(env_path);

      env_path = delim;

      if (cur_elem[0])
        target_path = alloc_printf("%s/%s", cur_elem, fname);
      else
        target_path = ck_strdup(fname);

      ck_free(cur_elem);

      if (!stat(target_path, &st) && S_ISREG(st.st_mode) &&
          (st.st_mode & 0111) && st.st_size >= 4) break;

      ck_free(target_path);
      target_path = 0;

    }

    if (!target_path) FATAL("Program '%s' not found or not executable", fname);

  }

}


/* Fix up argv for QEMU. */

static char** get_qemu_argv(u8* own_loc, char** argv, int argc) {

  char** new_argv = ck_alloc(sizeof(char*) * (argc + 4));
  u8 *tmp, *cp, *rsl, *own_copy;

  /* Workaround for a QEMU stability glitch. */

  setenv("QEMU_LOG", "nochain", 1);

  memcpy(new_argv + 3, argv + 1, sizeof(char*) * argc);

  new_argv[2] = target_path;
  new_argv[1] = "--";

  /* Now we need to actually find qemu for argv[0]. */

  tmp = getenv("AFL_PATH");

  if (tmp) {

    cp = alloc_printf("%s/afl-qemu-trace", tmp);

    if (access(cp, X_OK))
      FATAL("Unable to find '%s'", tmp);

    target_path = new_argv[0] = cp;
    return new_argv;

  }

  own_copy = ck_strdup(own_loc);
  rsl = strrchr(own_copy, '/');

  if (rsl) {

    *rsl = 0;

    cp = alloc_printf("%s/afl-qemu-trace", own_copy);
    ck_free(own_copy);

    if (!access(cp, X_OK)) {

      target_path = new_argv[0] = cp;
      return new_argv;

    }

  } else ck_free(own_copy);

  if (!access(BIN_PATH "/afl-qemu-trace", X_OK)) {

    target_path = new_argv[0] = BIN_PATH "/afl-qemu-trace";
    return new_argv;

  }

  FATAL("Unable to find 'afl-qemu-trace'.");

}


static void write_bitmap(void) {

  u8* fname;
  s32 fd;
  /* Save Br Visit Bitmap  */

  fname = alloc_printf("%s/br_visit_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, br_string_visit, sizeof(u32) * MAP_SIZE, fname);

  close(fd);

    /* Save Br Pass Bitmap  */
  fname = alloc_printf("%s/br_pass_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, br_string_pass, sizeof(u32) * MAP_SIZE, fname);

  close(fd);

  /* Save Seed Visit Bitmap  每个分支，种子的访问数量*/
  fname = alloc_printf("%s/seed_visit_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, seed_string_visit, sizeof(u32) * MAP_SIZE, fname);

  close(fd);

  /* Save Seed Pass Bitmap  每个分支，种子的通过数量*/
  fname = alloc_printf("%s/seed_pass_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, seed_string_pass, sizeof(u32) * MAP_SIZE, fname);

  close(fd);


  /* Save Seed First Visit Bitmap  */
  fname = alloc_printf("%s/first_visit_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, seed_first_visit, sizeof(u32) * MAP_SIZE, fname);

  close(fd);

  /* Save Seed First Pass Bitmap  */
  fname = alloc_printf("%s/first_pass_bitmap", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_write(fd, seed_first_pass, sizeof(u32) * MAP_SIZE, fname);

  close(fd);

  /* Save Seed Pass Num  */
  fname = alloc_printf("%s/seed_pass_num", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  write(fd, &seed_num_pass, sizeof(seed_num_pass));
    
  close(fd);

  /* Save Seed Visit Num  */
  fname = alloc_printf("%s/seed_visit_num", out_dir);
  fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0600);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  write(fd, &seed_num_visit, sizeof(seed_num_visit));

  close(fd);

  ck_free(fname);

}


/* Main entry point */

int main(int argc, char** argv) {

  s32 opt;
  u8  mem_limit_given = 0, timeout_given = 0, qemu_mode = 0;
  u32 tcnt;
  char** use_argv;

  doc_path = access(DOC_PATH, F_OK) ? "docs" : DOC_PATH;

  while ((opt = getopt(argc,argv,"+o:m:t:i:A:eqZQbcV")) > 0)

    switch (opt) {

      case 'i':

        in_dir = optarg;
        break;

      case 'o':

        out_dir = optarg;
        break;

      case 'm': {

          u8 suffix = 'M';

          if (mem_limit_given) FATAL("Multiple -m options not supported");
          mem_limit_given = 1;

          if (!strcmp(optarg, "none")) {

            mem_limit = 0;
            break;

          }

          if (sscanf(optarg, "%llu%c", &mem_limit, &suffix) < 1 ||
              optarg[0] == '-') FATAL("Bad syntax used for -m");

          switch (suffix) {

            case 'T': mem_limit *= 1024 * 1024; break;
            case 'G': mem_limit *= 1024; break;
            case 'k': mem_limit /= 1024; break;
            case 'M': break;

            default:  FATAL("Unsupported suffix or bad syntax for -m");

          }

          if (mem_limit < 5) FATAL("Dangerously low value of -m");

          if (sizeof(rlim_t) == 4 && mem_limit > 2000)
            FATAL("Value of -m out of range on 32-bit systems");

        }

        break;

      case 't':

        if (timeout_given) FATAL("Multiple -t options not supported");
        timeout_given = 1;

        if (strcmp(optarg, "none")) {
          exec_tmout = atoi(optarg);

          if (exec_tmout < 20 || optarg[0] == '-')
            FATAL("Dangerously low value of -t");

        }

        break;

      case 'e':

        if (edges_only) FATAL("Multiple -e options not supported");
        edges_only = 1;
        break;

      case 'q':

        if (quiet_mode) FATAL("Multiple -q options not supported");
        quiet_mode = 1;
        break;

      case 'Z':

        /* This is an undocumented option to write data in the syntax expected
           by afl-cmin. Nobody else should have any use for this. */

        cmin_mode  = 1;
        quiet_mode = 1;
        break;

      case 'A':

        /* Another afl-cmin specific feature. */
        at_file = optarg;
        //at_file类似afl-fuzz设置为.cur_input类型,得到的argv 输入文件路径参数为 .cur_input
        // 遍历in_dir下文件执行run_target。并在遍历过程中，将文件数据复制到.cur_input中。
        break;

      case 'Q':

        if (qemu_mode) FATAL("Multiple -Q options not supported");
        if (!mem_limit_given) mem_limit = MEM_LIMIT_QEMU;

        qemu_mode = 1;
        break;

      case 'b':

        /* Secret undocumented mode. Writes output in raw binary format
           similar to that dumped by afl-fuzz in <out_dir/queue/fuzz_bitmap. */

        binary_mode = 1;
        break;

      case 'c':

        if (keep_cores) FATAL("Multiple -c options not supported");
        keep_cores = 1;
        break;

      case 'V':

        show_banner();
        exit(0);

      default:

        usage(argv[0]);

    }

  if (optind == argc ) usage(argv[0]);

  // 共享内存这一块，添加bitmap 
  // 设置seed_pass_nums，seed_visit_nums等等，用来统计 ,类似afl-fuzz中实现的操作
  setup_shm();
  setup_signal_handlers();

  set_up_environment();

  find_binary(argv[optind]);

  if (!quiet_mode) {
    show_banner();
    ACTF("Executing '%s'...\n", target_path);
  }

  detect_file_args(argv + optind);
  //将输入到待测程序的用例，替换为in_dir/.cur_input

  if (qemu_mode)
    use_argv = get_qemu_argv(argv[0], argv + optind, argc - optind);
  else
    use_argv = argv + optind;

  struct dirent **entry; 
  int n;

  n = scandir(in_dir, &entry, NULL, alphasort);
  if (n < 0) {
      perror("scandir failed");
      return 1;
  }

  // 输出排序后的文件名，跳过 "." 和 ".."
  for (int i = 0; i < n; i++) {
  // 跳过 "."、".." 和 ".cur_seed"
    if (strcmp(entry[i]->d_name, ".") == 0 || strcmp(entry[i]->d_name, "..") == 0 
    || strcmp(entry[i]->d_name, ".cur_seed") == 0 ||strcmp(entry[i]->d_name, ".cur_input") == 0 
    || strcmp(entry[i]->d_name, ".state") == 0) {
        continue;
    }
    if(i==5) continue;
    printf("%s\n",entry[i]->d_name);      
    
    u8* fn = alloc_printf("%s/%s",in_dir,entry[i]->d_name);

    int fd = open(fn, O_RDONLY);

    if (fd < 0) {
        perror("open failed");
        continue;
    }
    
    struct stat st;
    
    if (fstat(fd, &st) < 0) {
        perror("fstat failed");
        close(fd);
        continue;
    }

    void *in_buf = mmap(0, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);

    if (in_buf == MAP_FAILED) {
        perror("mmap failed");
        close(fd);
        continue;
    }

    int out_fd = open(at_file, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (out_fd < 0) {
        perror("open at_file failed");
        munmap(in_buf, st.st_size);
        close(fd);
        continue;
    }
    lseek(out_fd, 0, SEEK_SET);

    ck_write(out_fd, in_buf, st.st_size, at_file);

    run_target(use_argv);
    
    total_execs++;
    
    for(int i=0;i<MAP_SIZE;i++){
      if(pass_string_cov[i]!=0){

        br_string_pass[i]+=pass_string_cov[i];
        seed_string_pass[i]++;
        if(seed_first_pass[i]==0){
          seed_first_pass[i]=total_execs;
        }
        if(!is_seed_pass) is_seed_pass = 1;
      }

      if(basic_blk_cov[i]!=0){

        br_string_visit[i]+=basic_blk_cov[i];
        seed_string_visit[i]++;

        if(seed_first_visit[i]==0){
          seed_first_visit[i]=total_execs;
        }
        if(!is_seed_visit) is_seed_visit = 1;
      }
    }

    if(is_seed_pass) {
      seed_num_pass++;
      is_seed_pass=0;
    }

    if(is_seed_visit){
      seed_num_visit++;
      is_seed_pass=0;
    }
  
    write_bitmap();

    munmap(in_buf, st.st_size);
    close(fd);
    close(out_fd);

  }

  // tcnt = write_results();

  // if (!quiet_mode) {

  //   if (!tcnt) FATAL("No instrumentation detected" cRST);
  //   OKF("Captured %u tuples in '%s'." cRST, tcnt, out_file);

  // }

  exit(child_crashed * 2 + child_timed_out);

}

