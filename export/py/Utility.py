def list_nth_default(index,l,default):
    if 0>index or index >= len(l):
        return default
    else:
        return l[index]

