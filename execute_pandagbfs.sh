#!/bin/bash
TEMP_DIR = $1
PROBLEM_NUMBER = $2
DOMAIN_DIR = $3
INSTANCE_DIR = $4
PARSED_FILE = ${TEMP_DIR}/${PROBLEM_NUMBER}.parsed
SAS_FILE = ${TEMP_DIR}/${PROBLEM_NUMBER}.sas
./home/schnell/lilotane/pandaPIparser $DOMAIN_DIR $INSTANCE_DIR $PARSED_FILE
./home/schnell/lilotane/pandaPIgrounder $PARSED_FILE $SAS_FILE
./home/schnell/lilotane/pandaPIengine --heuristic='rc2(add)' $SAS_FILE
