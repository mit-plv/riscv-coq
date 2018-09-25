#include <stdbool.h>

int32_t bitSlice(int32_t w, int32_t start, int32_t stop) {
    int32_t mask = (1 << (stop - start)) - 1;
    return (w >> start) & mask;
}

int32_t signExtend(int32_t l, int32_t n) {
    if ((n >> (l - 1)) & 1) {
	return n - (1 << l);
    } else {
	return n;
    }
}

t alu_add(t arg1, t arg2) {
  return arg1 + arg2;
}

t alu_sub(t arg1, t arg2) {
  return arg1 - arg2;
}

t alu_mul(t arg1, t arg2) {
  return arg1 * arg2;
}

t alu_div(t arg1, t arg2) {
  return arg1 / arg2;
}

t alu_rem(t arg1, t arg2) {
  return arg1 % arg2;
}

t alu_negate(t arg1) {
  return - arg1;
}

bool alu_reg_eqb(t arg1, t arg2) {
  return arg1 == arg2;
}

bool alu_signed_less_than(t arg1, t arg2) {
  return (t_signed)arg1 < (t_signed)arg2;
}

bool alu_ltu(t arg1, t arg2) {
  return (t_unsigned)arg1 < (t_unsigned)arg2;
}

t alu_xor(t arg1, t arg2) {
  return arg1 ^ arg2;
}

t alu_or(t arg1, t arg2) {
  return arg1 | arg2;
}

t alu_and(t arg1, t arg2) {
  return arg1 & arg2;
}

uint8_t alu_regToInt8(t arg1) {
  return arg1;
}

uint16_t alu_regToInt16(t arg1) {
  return arg1;
}

uint32_t alu_regToInt32(t arg1) {
  return arg1;
}

uint64_t alu_regToInt64(t arg1) {
  return arg1;
}

t alu_uInt8ToReg(uint8_t arg1) {
  return arg1;
}

t alu_uInt16ToReg(uint16_t arg1) {
  return arg1;
}

t alu_uInt32ToReg(uint32_t arg1) {
  return arg1;
}

t alu_uInt64ToReg(uint64_t arg1) {
  return arg1;
}

t alu_int8ToReg(int8_t arg1) {
  return arg1; // TODO does this sign-extend?
}

t alu_int16ToReg(int16_t arg1) {
  return arg1;
}

t alu_int32ToReg(int32_t arg1) {
  return arg1;
}

t alu_int64ToReg(int64_t arg1) {
  return arg1;
}

t alu_s32(t arg1) {
  return (t)((int32_t)arg1);
}

t alu_u32(t arg1) {
  return (t)((uint32_t)arg1);
}

// TODO this should be at least 2x bitwidth!
uint64_t alu_regToZ_signed(t arg1) {
  return arg1;
}

uint64_t alu_regToZ_unsigned(t arg1) {
  return arg1;
}

t alu_sll(t arg1, t arg2) {
  return (t_unsigned)arg1 << arg2;
}

t alu_srl(t arg1, t arg2) {
  return (t_unsigned)arg1 >> arg2;
}

t alu_sra(t arg1, t arg2) {
  return (t_signed)arg1 >> arg2;
}

t alu_divu(t arg1, t arg2) {
  return (t_unsigned)arg1 / (t_unsigned)arg2;
}

t alu_remu(t arg1, t arg2) {
  return (t_unsigned)arg1 % (t_unsigned)arg2;
}

t alu_maxSigned() {
  return MAX_t_SIGNED;
}

t alu_maxUnsigned() {
  return MAX_t_UNSIGNED;
}

t alu_minSigned() {
  return MIN_t_SIGNED;
}

t alu_regToShamt5(t arg1) {
  return arg1 & 0x1f;
}

t alu_regToShamt(t arg1) {
  return arg1; // TODO mask with 5 or 6 ones for 32 or 64 bit arch, respectively
}

t alu_highBits(t arg1) {
  return arg1; // TODO wrong
}

t alu_ZToReg(uint64_t arg1) {
  return arg1; // TODO
}

// derived functions:

t alu_lnot(t arg1) {
  return ~ arg1;
}
