# How many H01Branch modules to build or replay at once; sourced by build_r1212.sh
# and leanchecker_r1212.sh. Each of these modules needs up to about 7 GB in the Lean
# kernel, and about 4 GB are left for the rest of the system.

# r1212_jobs_for_mem_kb KB: the number of modules for KB kilobytes of memory, 1 to 8.
r1212_jobs_for_mem_kb() {
  local n=$(( ($1 / 1048576 - 4) / 7 ))
  if [ "$n" -lt 1 ]; then n=1; fi
  if [ "$n" -gt 8 ]; then n=8; fi
  echo "$n"
}

# r1212_mem_kb: physical memory in kilobytes; prints nothing if it cannot tell.
r1212_mem_kb() {
  if [ -r /proc/meminfo ]; then
    awk '/^MemTotal:/ {print $2; exit}' /proc/meminfo
  elif command -v sysctl > /dev/null 2>&1; then
    local bytes
    bytes=$(sysctl -n hw.memsize 2> /dev/null) || return 0
    echo $(( bytes / 1024 ))
  fi
}

# r1212_jobs [-j N]: N from -j, else from R1212_JOBS, else from the memory size.
# Prints the number on stdout and the reason on stderr.
r1212_jobs() {
  local n="${R1212_JOBS:-}" origin="R1212_JOBS"
  if [ "$#" -gt 0 ]; then
    if [ "$#" -ne 2 ] || [ "$1" != "-j" ]; then
      echo "usage: $0 [-j JOBS]" >&2
      return 2
    fi
    n=$2
    origin="-j"
  fi
  if [ -z "$n" ]; then
    local kb
    kb=$(r1212_mem_kb)
    if [ -z "$kb" ]; then
      echo "memory size unknown: 1 H01Branch module at a time (set with -j N or R1212_JOBS=N)" >&2
      echo 1
    else
      n=$(r1212_jobs_for_mem_kb "$kb")
      echo "$(( kb / 1048576 )) GB of memory: $n H01Branch module(s) at a time (set with -j N or R1212_JOBS=N)" >&2
      echo "$n"
    fi
    return 0
  fi
  case "$n" in
    '' | *[!0-9]*)
      echo "$origin must be a positive integer, got '$n'" >&2
      return 2 ;;
  esac
  n=$(( 10#$n ))
  if [ "$n" -lt 1 ]; then
    echo "$origin must be a positive integer, got '$n'" >&2
    return 2
  fi
  if [ "$n" -gt 8 ]; then n=8; fi
  echo "$origin: $n H01Branch module(s) at a time" >&2
  echo "$n"
}
