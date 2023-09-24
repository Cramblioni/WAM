set -xe
CFLAGS="-std=c17 -Wall -Wextra -fsanitize=address  -ggdb "

cc $CFLAGS -x c -o wam src/wam.c
