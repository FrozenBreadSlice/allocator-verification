CC := gcc
DEBUG_FLAGS := -g
C_FLAGS := -std=c99 -Werror -Wextra -Wpedantic 
RELEASE_FLAGS := -DBRELEASE

BIN := sm.out

debug:
	$(CC) -o logger.o $(C_FLAGS) $(DEBUG_FLAGS) -c logger.c
	$(CC) -o $(BIN) $(C_FLAGS) $(DEBUG_FLAGS) simplemimalloc.c logger.o
	rm -f logger.o

release:
	$(CC) -o logger.o $(C_FLAGS) $(RELEASE_FLAGS) -c logger.c
	$(CC) -o $(BIN) $(C_FLAGS) $(RELEASE_FLAGS) simplemimalloc.c logger.o
	rm -f logger.o
