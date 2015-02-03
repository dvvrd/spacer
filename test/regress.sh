#!/bin/bash

#the script directory. everything is relative to this.
SCRDIR=$(dirname $(readlink -f $0))

PMUZ="$SCRDIR/../pmuz/pmuz"
OUTF=$(mktemp /tmp/pmuz.XXXXXXXX)

function cleanup {
    rm -f $OUTF
    exit 0
}

trap "cleanup" SIGINT SIGTERM SIGHUP

function run_file {
    SMT2=$SCRDIR/$1
    OPTIONS="$2"
    EXPECTED_ANSWER=$3    
    timeout 15 /usr/bin/time -f "%e" $PMUZ $OPTIONS $SMT2 &> $OUTF
    RES=$(cat $OUTF | grep VERIFICATION | awk '{print $2}')
    UTIME=$(tail -n1 $OUTF)
    if [ x$RES == x ]; then
        printf "%-40s : timeout : %s\n" $(basename $SMT2) $UTIME
    elif [ x$RES == x$EXPECTED_ANSWER ]; then
        printf "%-40s : success : %s\n" $(basename $SMT2) $UTIME
    else
        printf "%-40s : failed  : %s\n" $(basename $SMT2) $UTIME
    fi
}

echo "============= direct query ..."
run_file ./ldv002_unsat.smt2 "-idl -dq" SUCCESSFUL
run_file ./teme_001_sat.smt2 "-idl -dq" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.01_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.02_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.03_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.04_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.01_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.02_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.03_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.04_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.06_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.07_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.08_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.09_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.10_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.11_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.12_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.13_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.14_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.15_unsafe.i.cil.o3.smt2 "-dq" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.16_unsafe.i.cil.o3.smt2 "-dq" FAILED

run_file ./svcomp13/ssh/s3_clnt.blast.01_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.02_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.03_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.04_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.01_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.02_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.06_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.07_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.08_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.09_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.10_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.11_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.12_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.13_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.14_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.15_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.16_safe.i.cil.o3.smt2 "-dq" SUCCESSFUL

echo "============= iterative query ..."
run_file ./ldv002_unsat.smt2 "-idl" SUCCESSFUL
run_file ./teme_001_sat.smt2 "-idl" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.01_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.02_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.03_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_clnt.blast.04_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.01_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.02_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.03_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.04_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.06_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.07_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.08_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.09_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.10_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.11_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.12_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.13_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.14_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.15_unsafe.i.cil.o3.smt2 "" FAILED
run_file ./svcomp13/ssh/s3_srvr.blast.16_unsafe.i.cil.o3.smt2 "" FAILED

run_file ./svcomp13/ssh/s3_clnt.blast.01_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.02_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.03_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_clnt.blast.04_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.01_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.02_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.06_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.07_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.08_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.09_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.10_safe.i.cil.o3.smt2 "" SUCCESSFUL
run_file ./svcomp13/ssh/s3_srvr.blast.11_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.12_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.13_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.14_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.15_safe.i.cil.o3.smt2 "" SUCCESSFUL
#run_file ./svcomp13/ssh/s3_srvr.blast.16_safe.i.cil.o3.smt2 "" SUCCESSFUL

cleanup
