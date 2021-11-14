#!/bin/bash
TEMP_DIR = $1
PROBLEM_NUMBER = $2
DOMAIN_DIR = $3
INSTANCE_DIR = $4
CRYPTOMINISAT_LIB = $5
PARSED_FILE = ${TEMP_DIR}/${PROBLEM_NUMBER}.parsed
SAS_FILE = ${TEMP_DIR}/${PROBLEM_NUMBER}.sas
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$CRYPTOMINISAT_LIB
./home/schnell/lilotane/pandaPIparser $DOMAIN_DIR $INSTANCE_DIR $PARSED_FILE
./home/schnell/lilotane/pandaPIgrounder $PARSED_FILE $SAS_FILE
./home/schnell/lilotane/pandaPIengine -s $SAS_FILE
