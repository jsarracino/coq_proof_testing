#!/usr/bin/env sh

# first argument is directory for find, e.g. CompCert

find $1/. -type f -name "*.complex*" -exec rm {} +