#!/usr/bin/env bash

DIR="$(cd -P "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")" )" && pwd)"

AGDASTDLIB_DEF="${HOME}/build/agda/lib/current/src"
AGDASTDLIB="${1:-"${AGDASTDLIB_DEF}"}"

EXTENSION="lagda"
TEXDIR="${DIR}/../latex"

# without extension
SRCS=( "Report/Chapter1" )


for s in ${SRCS[@]}; do
    FPATH="${DIR}/${s}"
    TEXPATH="${TEXDIR}/${s}"

    if [ ! -f "$(dirname "${TEXPATH}")/$(basename "${TEXPATH}").tex" ]; then 
        agda -i "${AGDASTDLIB}" -i "${DIR}" --latex --latex-dir="${TEXDIR}" "${FPATH}.${EXTENSION}"
    fi
done

