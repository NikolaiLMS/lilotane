#!/bin/bash
TEMP_DIR=$1
PROBLEM_NUMBER=$2
DOMAIN_DIR=$3
INSTANCE_DIR=$4
BINARIES_DIR=$5
PARSED_FILE=${TEMP_DIR}/${PROBLEM_NUMBER}.parsed
SAS_FILE=${TEMP_DIR}/${PROBLEM_NUMBER}.sas
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$BINARIES_DIR

_term() {
  echo "Caught SIGTERM signal!" 
  kill -TERM "$child" 2>/dev/null
}
trap _term SIGINT
trap _term SIGKILL
${BINARIES_DIR}/pandaPIparser $DOMAIN_DIR $INSTANCE_DIR $PARSED_FILE
${BINARIES_DIR}/pandaPIgrounder $PARSED_FILE $SAS_FILE &
child=$!

wait "$child"

${BINARIES_DIR}/pandaPIengineSAT -s $SAS_FILE &

child=$!
wait "$child"

