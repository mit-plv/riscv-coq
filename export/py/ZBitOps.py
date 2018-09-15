def bitSlice(w, start, stop):
    mask = (1 << (stop - start)) - 1
    return (w >> start) & mask
  
def signExtend(l,n):
    if (n >> (l - 1)) & 1:
        return n - (1 << l)
    else:
        return n
