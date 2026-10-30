CC := gcc
DEBUG_FLAGS := -g
C_FLAGS := -std=c99 -Werror -Wextra -Wpedantic 
RELEASE_FLAGS := -DBRELEASE

BIN := sm.out

debug:
	$(CC) -o logger.o $(C_FLAGS) $(DEBUG_FLAGS) -c logger.c
	$(CC) -o $(BIN) $(C_FLAGS) $(DEBUG_FLAGS) smtest.c logger.o 
	rm -f logger.o

release:
	$(CC) -o logger.o $(C_FLAGS) $(RELEASE_FLAGS) -c logger.c
	$(CC) -o $(BIN) $(C_FLAGS) $(RELEASE_FLAGS) smtest.c logger.o
	rm -f logger.o

deferred: 
	$(CC) -o logger.o $(C_FLAGS) $(DEBUG_FLAGS) -c logger.c
	$(CC) -o def_free_test.out $(C_FLAGS) $(DEBUG_FLAGS) deferred_free_test.c logger.o
	rm -f logger.o

