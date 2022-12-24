#!/usr/bin/env sh

# first argument is directory for find, e.g. CompCert
prefix=$(basename $1)

find $1/. -type f -name "*.complex" -exec cat {} + > $prefix.complex