#!/bin/sh
#for i in alias boa buffer cgi cgi_header config escape get hash ip log mmap_cache pipe queue read request response 'select' signals sublog util; do
for i in alias; do
  sh ./jcpp.sh boa/src/$i.c
done
