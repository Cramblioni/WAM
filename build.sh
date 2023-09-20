set -xe
CFLAGS="-std=c17 -Wall -Wextra  -ggdb "

cc $CFLAGS -x c -o wam wam.c
