LIB_NAME ?= libstd

PROJ_FILES = ../../
LIB_FULL_NAME = $(LIB_NAME).a

VERSION = 1
#############################

-include $(PROJ_FILES)/Makefile.conf
-include $(PROJ_FILES)/Makefile.gen

# use an app-specific build dir
APP_BUILD_DIR = $(BUILD_DIR)/libs/$(LIB_NAME)

CFLAGS := $(DEBUG_CFLAGS) $(WARN_CFLAGS) $(EMBED_CFLAGS) $(AFLAGS)
CFLAGS += -ffreestanding
CFLAGS += -I$(PROJ_FILES)/kernel/shared
CFLAGS += -I$(PROJ_FILES)/include/generated -I. -Iarch/cores/$(CONFIG_ARCH) -I$(PROJ_FILES)
CFLAGS += -MMD -MP
# libstd API
CFLAGS += -Iapi/
# libstd sublibs
CFLAGS += -Ialloc/
CFLAGS += -Istream/
CFLAGS += -Istring/
CFLAGS += -Iembed/

LDFLAGS += -fno-builtin -nostdlib -nostartfiles
LD_LIBS +=

BUILD_DIR ?= $(PROJ_FILE)build

ARCH_DIR := ./arch/cores/$(ARCH)
ARCH_SRC = $(wildcard $(ARCH_DIR)/*.c)
ARCH_OBJ = $(patsubst %.c,$(APP_BUILD_DIR)/%.o,$(ARCH_SRC))

SRC_DIR = .
SRC = $(wildcard $(SRC_DIR)/*.c)
SRC += $(wildcard $(SRC_DIR)/alloc/*.c)
SRC += $(wildcard $(SRC_DIR)/stream/*.c)
SRC += $(wildcard $(SRC_DIR)/string/*.c)
SRC += $(wildcard $(SRC_DIR)/embed/*.c)
SRC += $(wildcard $(SRC_DIR)/embed/arch/cores/armv7-m/*.c)
OBJ = $(patsubst %.c,$(APP_BUILD_DIR)/%.o,$(SRC))
DEP = $(OBJ:.o=.d)
ASM_SRC += $(wildcard $(SRC_DIR)/embed/arch/cores/armv7-m/*.s)
ASM_OBJ = $(patsubst %.s,$(APP_BUILD_DIR)/%.o,$(ASM_SRC))

OUT_DIRS = $(dir $(OBJ)) $(dir $(ARCH_OBJ))

# file to (dist)clean
# objects and compilation related
TODEL_CLEAN += $(ARCH_OBJ) $(OBJ)
# targets
TODEL_DISTCLEAN += $(APP_BUILD_DIR)

.PHONY: app

default: all

all: $(APP_BUILD_DIR) lib

show:
	@echo
	@echo "\tAPP_BUILD_DIR\t=> " $(APP_BUILD_DIR)
	@echo
	@echo "C sources files:"
	@echo "\tSRC_DIR\t\t=> " $(SRC_DIR)
	@echo "\tSRC\t\t=> " $(SRC)
	@echo "\tOBJ\t\t=> " $(OBJ)
	@echo
	@echo "\tARCH_DIR\t=> " $(ARCH_DIR)
	@echo "\tARCH_SRC\t=> " $(ARCH_SRC)
	@echo "\tARCH_OBJ\t=> " $(ARCH_OBJ)
	@echo

lib: $(APP_BUILD_DIR)/$(LIB_FULL_NAME)

#############################################################
# build targets (driver, core, SoC, Board... and local)
# App C sources files
$(APP_BUILD_DIR)/%.o: %.c
	$(call if_changed,cc_o_c)

$(APP_BUILD_DIR)/%.o: %.s
	$(call if_changed,cc_o_c)

# arch C sources files
$(APP_BUILD_DIR)/%.o: $(ARCH_DIR)/%.c
	$(call if_changed,cc_o_c)

# lib
$(APP_BUILD_DIR)/$(LIB_FULL_NAME): $(OBJ) $(ASM_OBJ) $(ARCH_OBJ)
	$(call if_changed,mklib)
	$(call if_changed,ranlib)

$(APP_BUILD_DIR):
	$(call cmd,mkdir)

-include $(DEP)
-include $(DRVDEP)
-include $(TESTSDEP)
