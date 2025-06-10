# Default build for x64
cake_scpog: basis_ffi.c cake_scpog.S
	gcc basis_ffi.c cake_scpog.S -o cake_scpog -std=c99

# To compile for native ARMv8 (replace gcc with your compiler)
cake_scpog_arm8: basis_ffi.c cake_scpog_arm8.S
	gcc basis_ffi.c cake_scpog_arm8.S -o cake_scpog -std=c99

# armv8 version (emulation on x64)
#cake_scpog_arm8_emu: basis_ffi.c cake_scpog_arm8.S
#	aarch64-linux-gnu-gcc -static basis_ffi.c cake_scpog_arm8.S -o cake_scpog_arm8

# Default build with 48 GB heap and 8 GB stack for starexec
big: basis_ffi.c cake_scpog.S
	gcc basis_ffi.c cake_scpog.S -o cake_scpog -std=c99 \
	-DCML_HEAP_SIZE=48000 -DCML_STACK_SIZE=8000

# see instructions above
big_arm8: basis_ffi.c cake_scpog_arm8.S
	gcc basis_ffi.c cake_scpog_arm8.S -o cake_scpog -std=c99 \
	-DCML_HEAP_SIZE=48000 -DCML_STACK_SIZE=8000

clean:
	rm -fv cake_scpog cake_scpog_arm8
