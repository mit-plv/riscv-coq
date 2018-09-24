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
