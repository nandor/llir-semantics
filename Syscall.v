(* This file is part of the LLIR Semantics project. *)
(* Licensing information is available in the LICENSE file. *)
(* (C) 2020 Nandor Licker. All rights reserved. *)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Require Import LLIR.Values.
Require Import LLIR.Eval.
Require Import LLIR.Maps.
Require Import LLIR.Signal.
Require Import LLIR.Types.
Require Import LLIR.Frame.
Require Import LLIR.State.

Import ListNotations.

Axiom ENOSYS: INT.I64.t.

Inductive syscall :=
  | sys_read
  | sys_write
  | sys_open
  | sys_close
  | sys_stat
  | sys_fstat
  | sys_lstat
  | sys_poll
  | sys_lseek
  | sys_mmap
  | sys_mprotect
  | sys_munmap
  | sys_brk
  | sys_rt_sigaction
  | sys_rt_sigprocmask
  | sys_rt_sigreturn
  | sys_ioctl
  | sys_pread64
  | sys_pwrite64
  | sys_readv
  | sys_writev
  | sys_access
  | sys_pipe
  | sys_select
  | sys_sched_yield
  | sys_mremap
  | sys_msync
  | sys_mincore
  | sys_madvise
  | sys_shmget
  | sys_shmat
  | sys_shmctl
  | sys_dup
  | sys_dup2
  | sys_pause
  | sys_nanosleep
  | sys_getitimer
  | sys_alarm
  | sys_setitimer
  | sys_getpid
  | sys_sendfile
  | sys_socket
  | sys_connect
  | sys_accept
  | sys_sendto
  | sys_recvfrom
  | sys_sendmsg
  | sys_recvmsg
  | sys_shutdown
  | sys_bind
  | sys_listen
  | sys_getsockname
  | sys_getpeername
  | sys_socketpair
  | sys_setsockopt
  | sys_getsockopt
  | sys_clone
  | sys_fork
  | sys_vfork
  | sys_execve
  | sys_exit
  | sys_wait4
  | sys_kill
  | sys_uname
  | sys_semget
  | sys_semop
  | sys_semctl
  | sys_shmdt
  | sys_msgget
  | sys_msgsnd
  | sys_msgrcv
  | sys_msgctl
  | sys_fcntl
  | sys_flock
  | sys_fsync
  | sys_fdatasync
  | sys_truncate
  | sys_ftruncate
  | sys_getdents
  | sys_getcwd
  | sys_chdir
  | sys_fchdir
  | sys_rename
  | sys_mkdir
  | sys_rmdir
  | sys_creat
  | sys_link
  | sys_unlink
  | sys_symlink
  | sys_readlink
  | sys_chmod
  | sys_fchmod
  | sys_chown
  | sys_fchown
  | sys_lchown
  | sys_umask
  | sys_gettimeofday
  | sys_getrlimit
  | sys_getrusage
  | sys_sysinfo
  | sys_times
  | sys_ptrace
  | sys_getuid
  | sys_syslog
  | sys_getgid
  | sys_setuid
  | sys_setgid
  | sys_geteuid
  | sys_getegid
  | sys_setpgid
  | sys_getppid
  | sys_getpgrp
  | sys_setsid
  | sys_setreuid
  | sys_setregid
  | sys_getgroups
  | sys_setgroups
  | sys_setresuid
  | sys_getresuid
  | sys_setresgid
  | sys_getresgid
  | sys_getpgid
  | sys_setfsuid
  | sys_setfsgid
  | sys_getsid
  | sys_capget
  | sys_capset
  | sys_rt_sigpending
  | sys_rt_sigtimedwait
  | sys_rt_sigqueueinfo
  | sys_rt_sigsuspend
  | sys_sigaltstack
  | sys_utime
  | sys_mknod
  | sys_uselib
  | sys_personality
  | sys_ustat
  | sys_statfs
  | sys_fstatfs
  | sys_sysfs
  | sys_getpriority
  | sys_setpriority
  | sys_sched_setparam
  | sys_sched_getparam
  | sys_sched_setscheduler
  | sys_sched_getscheduler
  | sys_sched_get_priority_max
  | sys_sched_get_priority_min
  | sys_sched_rr_get_interval
  | sys_mlock
  | sys_munlock
  | sys_mlockall
  | sys_munlockall
  | sys_vhangup
  | sys_modify_ldt
  | sys_pivot_root
  | sys__sysctl
  | sys_prctl
  | sys_arch_prctl
  | sys_adjtimex
  | sys_setrlimit
  | sys_chroot
  | sys_sync
  | sys_acct
  | sys_settimeofday
  | sys_mount
  | sys_umount2
  | sys_swapon
  | sys_swapoff
  | sys_reboot
  | sys_sethostname
  | sys_setdomainname
  | sys_iopl
  | sys_ioperm
  | sys_create_module
  | sys_init_module
  | sys_delete_module
  | sys_get_kernel_syms
  | sys_query_module
  | sys_quotactl
  | sys_nfsservctl
  | sys_getpmsg
  | sys_putpmsg
  | sys_afs_syscall
  | sys_tuxcall
  | sys_security
  | sys_gettid
  | sys_readahead
  | sys_setxattr
  | sys_lsetxattr
  | sys_fsetxattr
  | sys_getxattr
  | sys_lgetxattr
  | sys_fgetxattr
  | sys_listxattr
  | sys_llistxattr
  | sys_flistxattr
  | sys_removexattr
  | sys_lremovexattr
  | sys_fremovexattr
  | sys_tkill
  | sys_time
  | sys_futex
  | sys_sched_setaffinity
  | sys_sched_getaffinity
  | sys_set_thread_area
  | sys_io_setup
  | sys_io_destroy
  | sys_io_getevents
  | sys_io_submit
  | sys_io_cancel
  | sys_get_thread_area
  | sys_lookup_dcookie
  | sys_epoll_create
  | sys_epoll_ctl_old
  | sys_epoll_wait_old
  | sys_remap_file_pages
  | sys_getdents64
  | sys_set_tid_address
  | sys_restart_syscall
  | sys_semtimedop
  | sys_fadvise64
  | sys_timer_create
  | sys_timer_settime
  | sys_timer_gettime
  | sys_timer_getoverrun
  | sys_timer_delete
  | sys_clock_settime
  | sys_clock_gettime
  | sys_clock_getres
  | sys_clock_nanosleep
  | sys_exit_group
  | sys_epoll_wait
  | sys_epoll_ctl
  | sys_tgkill
  | sys_utimes
  | sys_vserver
  | sys_mbind
  | sys_set_mempolicy
  | sys_get_mempolicy
  | sys_mq_open
  | sys_mq_unlink
  | sys_mq_timedsend
  | sys_mq_timedreceive
  | sys_mq_notify
  | sys_mq_getsetattr
  | sys_kexec_load
  | sys_waitid
  | sys_add_key
  | sys_request_key
  | sys_keyctl
  | sys_ioprio_set
  | sys_ioprio_get
  | sys_inotify_init
  | sys_inotify_add_watch
  | sys_inotify_rm_watch
  | sys_migrate_pages
  | sys_openat
  | sys_mkdirat
  | sys_mknodat
  | sys_fchownat
  | sys_futimesat
  | sys_newfstatat
  | sys_unlinkat
  | sys_renameat
  | sys_linkat
  | sys_symlinkat
  | sys_readlinkat
  | sys_fchmodat
  | sys_faccessat
  | sys_pselect6
  | sys_ppoll
  | sys_unshare
  | sys_set_robust_list
  | sys_get_robust_list
  | sys_splice
  | sys_tee
  | sys_sync_file_range
  | sys_vmsplice
  | sys_move_pages
  | sys_utimensat
  | sys_epoll_pwait
  | sys_signalfd
  | sys_timerfd_create
  | sys_eventfd
  | sys_fallocate
  | sys_timerfd_settime
  | sys_timerfd_gettime
  | sys_accept4
  | sys_signalfd4
  | sys_eventfd2
  | sys_epoll_create1
  | sys_dup3
  | sys_pipe2
  | sys_inotify_init1
  | sys_preadv
  | sys_pwritev
  | sys_rt_tgsigqueueinfo
  | sys_perf_event_open
  | sys_recvmmsg
  | sys_fanotify_init
  | sys_fanotify_mark
  | sys_prlimit64
  | sys_name_to_handle_at
  | sys_open_by_handle_at
  | sys_clock_adjtime
  | sys_syncfs
  | sys_sendmmsg
  | sys_setns
  | sys_getcpu
  | sys_process_vm_readv
  | sys_process_vm_writev
  | sys_kcmp
  | sys_finit_module
  | sys_sched_setattr
  | sys_sched_getattr
  | sys_renameat2
  | sys_seccomp
  | sys_getrandom
  | sys_memfd_create
  | sys_kexec_file_load
  | sys_bpf
  | sys_execveat
  | sys_userfaultfd
  | sys_membarrier
  | sys_mlock2
  | sys_copy_file_range
  | sys_preadv2
  | sys_pwritev2
  | sys_pkey_mprotect
  | sys_pkey_alloc
  | sys_pkey_free
  | sys_statx
  | sys_io_pgetevents
  | sys_rseq
  | sys_pidfd_send_signal
  | sys_io_uring_setup
  | sys_io_uring_enter
  | sys_io_uring_register
  | sys_open_tree
  | sys_move_mount
  | sys_fsopen
  | sys_fsconfig
  | sys_fsmount
  | sys_fspick
  .

Definition syscall_of_sno (sno: INT.I64.t): option syscall :=
  match INT.I64.to_nat sno with
  |   0 => Some sys_read
  |   1 => Some sys_write
  |   2 => Some sys_open
  |   3 => Some sys_close
  |   4 => Some sys_stat
  |   5 => Some sys_fstat
  |   6 => Some sys_lstat
  |   7 => Some sys_poll
  |   8 => Some sys_lseek
  |   9 => Some sys_mmap
  |  10 => Some sys_mprotect
  |  11 => Some sys_munmap
  |  12 => Some sys_brk
  |  13 => Some sys_rt_sigaction
  |  14 => Some sys_rt_sigprocmask
  |  15 => Some sys_rt_sigreturn
  |  16 => Some sys_ioctl
  |  17 => Some sys_pread64
  |  18 => Some sys_pwrite64
  |  19 => Some sys_readv
  |  20 => Some sys_writev
  |  21 => Some sys_access
  |  22 => Some sys_pipe
  |  23 => Some sys_select
  |  24 => Some sys_sched_yield
  |  25 => Some sys_mremap
  |  26 => Some sys_msync
  |  27 => Some sys_mincore
  |  28 => Some sys_madvise
  |  29 => Some sys_shmget
  |  30 => Some sys_shmat
  |  31 => Some sys_shmctl
  |  32 => Some sys_dup
  |  33 => Some sys_dup2
  |  34 => Some sys_pause
  |  35 => Some sys_nanosleep
  |  36 => Some sys_getitimer
  |  37 => Some sys_alarm
  |  38 => Some sys_setitimer
  |  39 => Some sys_getpid
  |  40 => Some sys_sendfile
  |  41 => Some sys_socket
  |  42 => Some sys_connect
  |  43 => Some sys_accept
  |  44 => Some sys_sendto
  |  45 => Some sys_recvfrom
  |  46 => Some sys_sendmsg
  |  47 => Some sys_recvmsg
  |  48 => Some sys_shutdown
  |  49 => Some sys_bind
  |  50 => Some sys_listen
  |  51 => Some sys_getsockname
  |  52 => Some sys_getpeername
  |  53 => Some sys_socketpair
  |  54 => Some sys_setsockopt
  |  55 => Some sys_getsockopt
  |  56 => Some sys_clone
  |  57 => Some sys_fork
  |  58 => Some sys_vfork
  |  59 => Some sys_execve
  |  60 => Some sys_exit
  |  61 => Some sys_wait4
  |  62 => Some sys_kill
  |  63 => Some sys_uname
  |  64 => Some sys_semget
  |  65 => Some sys_semop
  |  66 => Some sys_semctl
  |  67 => Some sys_shmdt
  |  68 => Some sys_msgget
  |  69 => Some sys_msgsnd
  |  70 => Some sys_msgrcv
  |  71 => Some sys_msgctl
  |  72 => Some sys_fcntl
  |  73 => Some sys_flock
  |  74 => Some sys_fsync
  |  75 => Some sys_fdatasync
  |  76 => Some sys_truncate
  |  77 => Some sys_ftruncate
  |  78 => Some sys_getdents
  |  79 => Some sys_getcwd
  |  80 => Some sys_chdir
  |  81 => Some sys_fchdir
  |  82 => Some sys_rename
  |  83 => Some sys_mkdir
  |  84 => Some sys_rmdir
  |  85 => Some sys_creat
  |  86 => Some sys_link
  |  87 => Some sys_unlink
  |  88 => Some sys_symlink
  |  89 => Some sys_readlink
  |  90 => Some sys_chmod
  |  91 => Some sys_fchmod
  |  92 => Some sys_chown
  |  93 => Some sys_fchown
  |  94 => Some sys_lchown
  |  95 => Some sys_umask
  |  96 => Some sys_gettimeofday
  |  97 => Some sys_getrlimit
  |  98 => Some sys_getrusage
  |  99 => Some sys_sysinfo
  | 100 => Some sys_times
  | 101 => Some sys_ptrace
  | 102 => Some sys_getuid
  | 103 => Some sys_syslog
  | 104 => Some sys_getgid
  | 105 => Some sys_setuid
  | 106 => Some sys_setgid
  | 107 => Some sys_geteuid
  | 108 => Some sys_getegid
  | 109 => Some sys_setpgid
  | 110 => Some sys_getppid
  | 111 => Some sys_getpgrp
  | 112 => Some sys_setsid
  | 113 => Some sys_setreuid
  | 114 => Some sys_setregid
  | 115 => Some sys_getgroups
  | 116 => Some sys_setgroups
  | 117 => Some sys_setresuid
  | 118 => Some sys_getresuid
  | 119 => Some sys_setresgid
  | 120 => Some sys_getresgid
  | 121 => Some sys_getpgid
  | 122 => Some sys_setfsuid
  | 123 => Some sys_setfsgid
  | 124 => Some sys_getsid
  | 125 => Some sys_capget
  | 126 => Some sys_capset
  | 127 => Some sys_rt_sigpending
  | 128 => Some sys_rt_sigtimedwait
  | 129 => Some sys_rt_sigqueueinfo
  | 130 => Some sys_rt_sigsuspend
  | 131 => Some sys_sigaltstack
  | 132 => Some sys_utime
  | 133 => Some sys_mknod
  | 134 => Some sys_uselib
  | 135 => Some sys_personality
  | 136 => Some sys_ustat
  | 137 => Some sys_statfs
  | 138 => Some sys_fstatfs
  | 139 => Some sys_sysfs
  | 140 => Some sys_getpriority
  | 141 => Some sys_setpriority
  | 142 => Some sys_sched_setparam
  | 143 => Some sys_sched_getparam
  | 144 => Some sys_sched_setscheduler
  | 145 => Some sys_sched_getscheduler
  | 146 => Some sys_sched_get_priority_max
  | 147 => Some sys_sched_get_priority_min
  | 148 => Some sys_sched_rr_get_interval
  | 149 => Some sys_mlock
  | 150 => Some sys_munlock
  | 151 => Some sys_mlockall
  | 152 => Some sys_munlockall
  | 153 => Some sys_vhangup
  | 154 => Some sys_modify_ldt
  | 155 => Some sys_pivot_root
  | 156 => Some sys__sysctl
  | 157 => Some sys_prctl
  | 158 => Some sys_arch_prctl
  | 159 => Some sys_adjtimex
  | 160 => Some sys_setrlimit
  | 161 => Some sys_chroot
  | 162 => Some sys_sync
  | 163 => Some sys_acct
  | 164 => Some sys_settimeofday
  | 165 => Some sys_mount
  | 166 => Some sys_umount2
  | 167 => Some sys_swapon
  | 168 => Some sys_swapoff
  | 169 => Some sys_reboot
  | 170 => Some sys_sethostname
  | 171 => Some sys_setdomainname
  | 172 => Some sys_iopl
  | 173 => Some sys_ioperm
  | 174 => Some sys_create_module
  | 175 => Some sys_init_module
  | 176 => Some sys_delete_module
  | 177 => Some sys_get_kernel_syms
  | 178 => Some sys_query_module
  | 179 => Some sys_quotactl
  | 180 => Some sys_nfsservctl
  | 181 => Some sys_getpmsg
  | 182 => Some sys_putpmsg
  | 183 => Some sys_afs_syscall
  | 184 => Some sys_tuxcall
  | 185 => Some sys_security
  | 186 => Some sys_gettid
  | 187 => Some sys_readahead
  | 188 => Some sys_setxattr
  | 189 => Some sys_lsetxattr
  | 190 => Some sys_fsetxattr
  | 191 => Some sys_getxattr
  | 192 => Some sys_lgetxattr
  | 193 => Some sys_fgetxattr
  | 194 => Some sys_listxattr
  | 195 => Some sys_llistxattr
  | 196 => Some sys_flistxattr
  | 197 => Some sys_removexattr
  | 198 => Some sys_lremovexattr
  | 199 => Some sys_fremovexattr
  | 200 => Some sys_tkill
  | 201 => Some sys_time
  | 202 => Some sys_futex
  | 203 => Some sys_sched_setaffinity
  | 204 => Some sys_sched_getaffinity
  | 205 => Some sys_set_thread_area
  | 206 => Some sys_io_setup
  | 207 => Some sys_io_destroy
  | 208 => Some sys_io_getevents
  | 209 => Some sys_io_submit
  | 210 => Some sys_io_cancel
  | 211 => Some sys_get_thread_area
  | 212 => Some sys_lookup_dcookie
  | 213 => Some sys_epoll_create
  | 214 => Some sys_epoll_ctl_old
  | 215 => Some sys_epoll_wait_old
  | 216 => Some sys_remap_file_pages
  | 217 => Some sys_getdents64
  | 218 => Some sys_set_tid_address
  | 219 => Some sys_restart_syscall
  | 220 => Some sys_semtimedop
  | 221 => Some sys_fadvise64
  | 222 => Some sys_timer_create
  | 223 => Some sys_timer_settime
  | 224 => Some sys_timer_gettime
  | 225 => Some sys_timer_getoverrun
  | 226 => Some sys_timer_delete
  | 227 => Some sys_clock_settime
  | 228 => Some sys_clock_gettime
  | 229 => Some sys_clock_getres
  | 230 => Some sys_clock_nanosleep
  | 231 => Some sys_exit_group
  | 232 => Some sys_epoll_wait
  | 233 => Some sys_epoll_ctl
  | 234 => Some sys_tgkill
  | 235 => Some sys_utimes
  | 236 => Some sys_vserver
  | 237 => Some sys_mbind
  | 238 => Some sys_set_mempolicy
  | 239 => Some sys_get_mempolicy
  | 240 => Some sys_mq_open
  | 241 => Some sys_mq_unlink
  | 242 => Some sys_mq_timedsend
  | 243 => Some sys_mq_timedreceive
  | 244 => Some sys_mq_notify
  | 245 => Some sys_mq_getsetattr
  | 246 => Some sys_kexec_load
  | 247 => Some sys_waitid
  | 248 => Some sys_add_key
  | 249 => Some sys_request_key
  | 250 => Some sys_keyctl
  | 251 => Some sys_ioprio_set
  | 252 => Some sys_ioprio_get
  | 253 => Some sys_inotify_init
  | 254 => Some sys_inotify_add_watch
  | 255 => Some sys_inotify_rm_watch
  | 256 => Some sys_migrate_pages
  | 257 => Some sys_openat
  | 258 => Some sys_mkdirat
  | 259 => Some sys_mknodat
  | 260 => Some sys_fchownat
  | 261 => Some sys_futimesat
  | 262 => Some sys_newfstatat
  | 263 => Some sys_unlinkat
  | 264 => Some sys_renameat
  | 265 => Some sys_linkat
  | 266 => Some sys_symlinkat
  | 267 => Some sys_readlinkat
  | 268 => Some sys_fchmodat
  | 269 => Some sys_faccessat
  | 270 => Some sys_pselect6
  | 271 => Some sys_ppoll
  | 272 => Some sys_unshare
  | 273 => Some sys_set_robust_list
  | 274 => Some sys_get_robust_list
  | 275 => Some sys_splice
  | 276 => Some sys_tee
  | 277 => Some sys_sync_file_range
  | 278 => Some sys_vmsplice
  | 279 => Some sys_move_pages
  | 280 => Some sys_utimensat
  | 281 => Some sys_epoll_pwait
  | 282 => Some sys_signalfd
  | 283 => Some sys_timerfd_create
  | 284 => Some sys_eventfd
  | 285 => Some sys_fallocate
  | 286 => Some sys_timerfd_settime
  | 287 => Some sys_timerfd_gettime
  | 288 => Some sys_accept4
  | 289 => Some sys_signalfd4
  | 290 => Some sys_eventfd2
  | 291 => Some sys_epoll_create1
  | 292 => Some sys_dup3
  | 293 => Some sys_pipe2
  | 294 => Some sys_inotify_init1
  | 295 => Some sys_preadv
  | 296 => Some sys_pwritev
  | 297 => Some sys_rt_tgsigqueueinfo
  | 298 => Some sys_perf_event_open
  | 299 => Some sys_recvmmsg
  | 300 => Some sys_fanotify_init
  | 301 => Some sys_fanotify_mark
  | 302 => Some sys_prlimit64
  | 303 => Some sys_name_to_handle_at
  | 304 => Some sys_open_by_handle_at
  | 305 => Some sys_clock_adjtime
  | 306 => Some sys_syncfs
  | 307 => Some sys_sendmmsg
  | 308 => Some sys_setns
  | 309 => Some sys_getcpu
  | 310 => Some sys_process_vm_readv
  | 311 => Some sys_process_vm_writev
  | 312 => Some sys_kcmp
  | 313 => Some sys_finit_module
  | 314 => Some sys_sched_setattr
  | 315 => Some sys_sched_getattr
  | 316 => Some sys_renameat2
  | 317 => Some sys_seccomp
  | 318 => Some sys_getrandom
  | 319 => Some sys_memfd_create
  | 320 => Some sys_kexec_file_load
  | 321 => Some sys_bpf
  | 322 => Some sys_execveat
  | 323 => Some sys_userfaultfd
  | 324 => Some sys_membarrier
  | 325 => Some sys_mlock2
  | 326 => Some sys_copy_file_range
  | 327 => Some sys_preadv2
  | 328 => Some sys_pwritev2
  | 329 => Some sys_pkey_mprotect
  | 330 => Some sys_pkey_alloc
  | 331 => Some sys_pkey_free
  | 332 => Some sys_statx
  | 333 => Some sys_io_pgetevents
  | 334 => Some sys_rseq
  | 424 => Some sys_pidfd_send_signal
  | 425 => Some sys_io_uring_setup
  | 426 => Some sys_io_uring_enter
  | 427 => Some sys_io_uring_register
  | 428 => Some sys_open_tree
  | 429 => Some sys_move_mount
  | 430 => Some sys_fsopen
  | 431 => Some sys_fsconfig
  | 432 => Some sys_fsmount
  | 433 => Some sys_fspick
  | _ => None
  end.


Inductive SyscallNumber : value -> syscall -> Prop :=
  | syscall_sys:
    forall (v: INT.I64.t) (s: syscall) (SNO_CALL: Some s = syscall_of_sno v),
      SyscallNumber (VInt (INT.Int64 v)) s
  .

Inductive SyscallNoSys : value -> Prop :=
  | syscall_no_sys:
    forall (v: INT.I64.t) (SNO_CALL: None = syscall_of_sno v),
      SyscallNoSys (VInt (INT.Int64 v))
  .

Inductive SyscallUndef : value -> Prop :=
  | syscall_undef_sym: forall (s: sym), SyscallUndef (VSym s)
  | syscall_undef_und: SyscallUndef VUnd
  .

Lemma syscall_number_complete:
  forall (v: value),
    TypeOfValue v (TInt I64) ->
    (exists (s: syscall), SyscallNumber v s)
    \/
    SyscallNoSys v
    \/
    SyscallUndef v.
Proof.
  intros v Hty. inversion Hty; subst.
  - inversion TY; subst.
    destruct (syscall_of_sno v) as [s|] eqn:Esno.
    + left; exists s; constructor; auto.
    + right; left; constructor; auto.
  - right; right; constructor.
  - right; right; constructor.
Qed.

Inductive SyscallArg : reg -> value -> Prop :=
  | sys_arg_und: forall (r: reg), SyscallArg r VUnd
  | sys_arg_sym: forall (r: reg) (s: sym), SyscallArg r (VSym s)
  | sys_arg_int: forall (r: reg) (i: INT.I64.t), SyscallArg r (VInt (INT.Int64 i))
  .

Inductive SyscallArgs : frame -> list reg -> list value -> Prop :=
  | arg_vals_nil:
    forall
      (fr: frame),
      SyscallArgs fr [] []
  | arg_vals_cons:
    forall
      (fr: frame)
      (arg_value: value) (arg_values: list value)
      (arg: reg) (args: list reg)
      (VALUE: Some arg_value = fr.(fr_regs) ! arg)
      (HEAD: SyscallArg arg arg_value)
      (TAIL: SyscallArgs fr args arg_values),
      SyscallArgs fr (arg::args) (arg_value::arg_values)
  .

Inductive SyscallRet 
  : syscall ->
    list value ->
    stack -> 
    heap -> 
    trace -> 
    stack -> 
    heap -> 
    INT.I64.t -> 
    Prop :=
  .

Inductive SyscallSig 
  : syscall ->
    list value ->
    stack -> 
    heap -> 
    trace -> 
    signal -> 
    Prop :=
  .

Lemma syscall_ret_or_sig :
  forall (sno: syscall) (args: list value) (stk: stack) (h: heap),
    {exists (tr: trace) (stk': stack) (h': heap) (v: INT.I64.t), 
      SyscallRet sno args stk h tr stk' h' v}
    +
    {exists (sig: signal) (tr: trace), 
      SyscallSig sno args stk h tr sig}.
Admitted.
