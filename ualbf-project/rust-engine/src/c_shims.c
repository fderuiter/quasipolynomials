#include <lean/lean.h>

extern void* rs_lean_register_external_class(void* finalize, void* foreach) {
    return (void*)lean_register_external_class((lean_external_finalize_proc)finalize, (lean_external_foreach_proc)foreach);
}

extern void* rs_lean_alloc_external(void* cls, void* data) {
    return (void*)lean_alloc_external((lean_external_class*)cls, data);
}

extern void* rs_lean_get_external_data(void* obj) {
    return lean_get_external_data((lean_object*)obj);
}

extern void rs_lean_inc(void* obj) {
    lean_inc((lean_object*)obj);
}

extern void rs_lean_dec(void* obj) {
    lean_dec((lean_object*)obj);
}
