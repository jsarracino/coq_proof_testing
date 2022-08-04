#!/usr/bin/env sh

find CompCert/. -type f -name "*.complex" -exec cat {} + > total.complex