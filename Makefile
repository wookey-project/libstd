###################################################################
# About the library name and path
###################################################################

# library name, without extension
LIB_NAME ?= libstd

# project root directory, relative to app dir
PROJ_FILES = ../../

# library name, with extension
LIB_FULL_NAME = $(LIB_NAME).a

# SDK helper Makefiles inclusion
-include $(PROJ_FILES)/Makefile.conf
-include $(PROJ_FILES)/Makefile.gen

# use an app-specific build dir
APP_BUILD_DIR = $(BUILD_DIR)/libs/$(LIB_NAME)

###################################################################
# About the compilation flags
###################################################################


CFLAGS := $(LIBS_CFLAGS)
# this lib is special: some of its functions are called by the kernel and as such must NOT be
# purged at strip time by the compiler.
# This flag block any attempt to delete unused symbols from the object file as they may be
# called from the kernel
CFLAGS += -I. -Iarch/cores/$(CONFIG_ARCH) -MMD -MP
# this is specific to libstd, as this lib hold the task entrypoints (do_startisr and do_starttask)
# which whould be overriden by the -Wl,gc -ffunction-sections
CFLAGS += -fno-function-sections

# about local subdirs
# libstd API
CFLAGS += -Iapi/
# libstd sublibs
CFLAGS += -Ialloc/
CFLAGS += -Istream/
CFLAGS += -Istring/
CFLAGS += -Iembed/
CFLAGS += -Iarpa/


#############################################################
# About library sources
#############################################################

# libstd has arch-specific sources
ARCH_DIR := ./arch/cores/$(ARCH)
ARCH_SRC = $(wildcard $(ARCH_DIR)/*.c)
ARCH_OBJ = $(patsubst %.c,$(APP_BUILD_DIR)/%.o,$(ARCH_SRC))

# ... and C sources
SRC_DIR = .
SRC = $(wildcard $(SRC_DIR)/*.c)
SRC += $(wildcard $(SRC_DIR)/alloc/*.c)
SRC += $(wildcard $(SRC_DIR)/stream/*.c)
SRC += $(wildcard $(SRC_DIR)/string/*.c)
SRC += $(wildcard $(SRC_DIR)/embed/*.c)
SRC += $(wildcard $(SRC_DIR)/arpa/*.c)
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

##########################################################
# generic targets of all libraries makefiles
##########################################################

.PHONY: app doc

default: all

all: $(APP_BUILD_DIR) lib

doc:
	$(Q)$(MAKE) BUILDDIR=../$(APP_BUILD_DIR)/doc  -C doc html latexpdf

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
