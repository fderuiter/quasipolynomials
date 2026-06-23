#include <metal_stdlib>
using namespace metal;

struct RNS512 {
    uint64_t w[8];
};

struct Task {
    RNS512 n;
    RNS512 r_squared;
    uint64_t m0_prime;
    uint64_t padding[3];
};

struct Result {
    RNS512 factor;
};

inline bool is_zero(RNS512 a) {
    for(int i=0; i<8; i++) if(a.w[i] != 0) return false;
    return true;
}

inline bool is_one(RNS512 a) {
    if(a.w[0] != 1) return false;
    for(int i=1; i<8; i++) if(a.w[i] != 0) return false;
    return true;
}

inline bool is_even(RNS512 a) {
    return (a.w[0] & 1) == 0;
}

inline int cmp(RNS512 a, RNS512 b) {
    for(int i=7; i>=0; i--) {
        if(a.w[i] > b.w[i]) return 1;
        if(a.w[i] < b.w[i]) return -1;
    }
    return 0;
}

inline RNS512 sub(RNS512 a, RNS512 b) {
    RNS512 res;
    uint64_t borrow = 0;
    for(int i=0; i<8; i++){
        uint64_t diff = a.w[i] - b.w[i] - borrow;
        res.w[i] = diff;
        borrow = (a.w[i] < b.w[i] || (borrow == 1 && diff == 0xFFFFFFFFFFFFFFFF)) ? 1 : 0;
    }
    return res;
}

inline RNS512 shr1(RNS512 a) {
    RNS512 res;
    uint64_t carry = 0;
    for(int i=7; i>=0; i--) {
        uint64_t next_carry = (a.w[i] & 1) << 63;
        res.w[i] = (a.w[i] >> 1) | carry;
        carry = next_carry;
    }
    return res;
}

inline RNS512 gcd(RNS512 a, RNS512 b) {
    if (is_zero(a)) return b;
    if (is_zero(b)) return a;
    
    int shift = 0;
    while (is_even(a) && is_even(b)) {
        a = shr1(a);
        b = shr1(b);
        shift++;
    }
    
    while (is_even(a)) a = shr1(a);
    
    while (!is_zero(b)) {
        while (is_even(b)) b = shr1(b);
        if (cmp(a, b) > 0) {
            RNS512 t = a; a = b; b = t;
        }
        b = sub(b, a);
    }
    
    RNS512 res = a;
    for(int i=0; i<shift; i++) {
        uint64_t carry = 0;
        for(int j=0; j<8; j++) {
            uint64_t next_carry = res.w[j] >> 63;
            res.w[j] = (res.w[j] << 1) | carry;
            carry = next_carry;
        }
    }
    return res;
}

inline RNS512 mont_mul(RNS512 a, RNS512 b, RNS512 m, uint64_t m0_prime) {
    uint64_t t[16] = {0};
    uint64_t t16 = 0;
    
    for (int i = 0; i < 8; ++i) {
        uint64_t c = 0;
        for (int j = 0; j < 8; ++j) {
            uint64_t lo = a.w[i] * b.w[j];
            uint64_t hi = mulhi(a.w[i], b.w[j]);
            
            uint64_t sum1 = t[i + j] + c;
            uint64_t carry1 = (sum1 < c) ? 1 : 0;
            uint64_t sum2 = sum1 + lo;
            uint64_t carry2 = (sum2 < lo) ? 1 : 0;
            
            t[i + j] = sum2;
            c = hi + carry1 + carry2;
        }
        t[i + 8] = c;
        
        uint64_t u = t[i] * m0_prime;
        c = 0;
        for (int j = 0; j < 8; ++j) {
            uint64_t lo = u * m.w[j];
            uint64_t hi = mulhi(u, m.w[j]);
            
            uint64_t sum1 = t[i + j] + c;
            uint64_t carry1 = (sum1 < c) ? 1 : 0;
            uint64_t sum2 = sum1 + lo;
            uint64_t carry2 = (sum2 < lo) ? 1 : 0;
            
            t[i + j] = sum2;
            c = hi + carry1 + carry2;
        }
        
        uint64_t sum3 = t[i + 8] + c;
        t[i + 8] = sum3;
        if (i == 7) {
            t16 = (sum3 < c) ? 1 : 0;
        } else {
            t[i + 9] += (sum3 < c) ? 1 : 0;
        }
    }
    
    RNS512 res;
    for(int i=0; i<8; i++) res.w[i] = t[8+i];
    
    uint64_t borrow = 0;
    RNS512 subtracted;
    for (int i = 0; i < 8; ++i) {
        uint64_t diff = res.w[i] - m.w[i] - borrow;
        subtracted.w[i] = diff;
        borrow = (res.w[i] < m.w[i] || (borrow == 1 && diff == 0xFFFFFFFFFFFFFFFF)) ? 1 : 0;
    }
    if (borrow && t16 == 0) return res;
    return subtracted;
}

inline RNS512 mont_add(RNS512 a, RNS512 b, RNS512 m) {
    RNS512 res;
    uint64_t carry = 0;
    for(int i=0; i<8; i++){
        uint64_t sum1 = a.w[i] + carry;
        uint64_t c1 = (sum1 < carry) ? 1 : 0;
        uint64_t sum2 = sum1 + b.w[i];
        uint64_t c2 = (sum2 < b.w[i]) ? 1 : 0;
        res.w[i] = sum2;
        carry = c1 + c2;
    }
    uint64_t borrow = 0;
    RNS512 sub_res;
    for(int i=0; i<8; i++){
        uint64_t diff = res.w[i] - m.w[i] - borrow;
        sub_res.w[i] = diff;
        borrow = (res.w[i] < m.w[i] || (borrow == 1 && diff == 0xFFFFFFFFFFFFFFFF)) ? 1 : 0;
    }
    if (borrow && carry == 0) return res;
    return sub_res;
}

inline RNS512 mont_to_norm(RNS512 a, RNS512 m, uint64_t m0_prime) {
    RNS512 one;
    for(int i=0; i<8; i++) one.w[i] = 0;
    one.w[0] = 1;
    return mont_mul(a, one, m, m0_prime);
}

kernel void pollard_rho(
    device const Task* tasks [[buffer(0)]],
    device Result* results [[buffer(1)]],
    uint id [[thread_position_in_grid]]
) {
    Task t = tasks[id];
    RNS512 n = t.n;
    
    for(uint64_t c = 1; c < 40; ++c) {
        RNS512 C;
        for(int i=0; i<8; i++) C.w[i] = 0;
        C.w[0] = c;
        C = mont_mul(C, t.r_squared, n, t.m0_prime);
        
        RNS512 two;
        for(int i=0; i<8; i++) two.w[i] = 0;
        two.w[0] = 2;
        RNS512 X = mont_mul(two, t.r_squared, n, t.m0_prime);
        RNS512 Y = X;
        
        RNS512 d;
        for(int i=0; i<8; i++) d.w[i] = 0;
        d.w[0] = 1;
        
        uint32_t r = 1;
        RNS512 Q;
        for(int i=0; i<8; i++) Q.w[i] = 0;
        Q.w[0] = 1;
        Q = mont_mul(Q, t.r_squared, n, t.m0_prime);
        
        RNS512 YS = Y;
        
        while(is_one(d)) {
            X = Y;
            for(uint32_t i=0; i<r; i++) {
                Y = mont_add(mont_mul(Y, Y, n, t.m0_prime), C, n);
            }
            
            uint32_t k = 0;
            while (k < r && is_one(d)) {
                YS = Y;
                uint32_t batch = r - k;
                if (batch > 128) batch = 128;
                for(uint32_t j=0; j<batch; j++) {
                    Y = mont_add(mont_mul(Y, Y, n, t.m0_prime), C, n);
                    RNS512 diff = cmp(X, Y) > 0 ? sub(X, Y) : sub(Y, X);
                    Q = mont_mul(Q, diff, n, t.m0_prime);
                }
                RNS512 Q_norm = mont_to_norm(Q, n, t.m0_prime);
                d = gcd(Q_norm, n);
                k += batch;
            }
            r *= 2;
            if (r > 100000) break;
        }
        
        if (!is_one(d) && cmp(d, n) != 0) {
            results[id].factor = d;
            return;
        }
        
        if (cmp(d, n) == 0) {
            while (true) {
                YS = mont_add(mont_mul(YS, YS, n, t.m0_prime), C, n);
                RNS512 YS_norm = mont_to_norm(YS, n, t.m0_prime);
                RNS512 X_norm = mont_to_norm(X, n, t.m0_prime);
                RNS512 diff = cmp(X_norm, YS_norm) > 0 ? sub(X_norm, YS_norm) : sub(YS_norm, X_norm);
                d = gcd(diff, n);
                if (!is_one(d)) break;
            }
            if (cmp(d, n) != 0) {
                results[id].factor = d;
                return;
            }
        }
    }
    
    for(int i=0; i<8; i++) results[id].factor.w[i] = 0;
}

struct Obstruction {
    RNS512 pe;
    RNS512 pe1;
    uint64_t pe_m0_prime;
    uint64_t pe1_m0_prime;
    uint64_t padding[2];
};

kernel void raycast_sieve(
    device const RNS512& r_i [[buffer(0)]],
    device const RNS512& s_l [[buffer(1)]],
    device const uint64_t& c_min [[buffer(2)]],
    device const uint64_t& c_max [[buffer(3)]],
    device const Obstruction* obstructions [[buffer(4)]],
    device const uint32_t& num_obstructions [[buffer(5)]],
    device atomic_uint* bit_vector [[buffer(6)]],
    device uint32_t* valid_indices [[buffer(7)]],
    device atomic_uint* valid_count [[buffer(8)]],
    device const uint8_t& enable_diagnostics [[buffer(9)]],
    uint id [[thread_position_in_grid]]
) {
    uint64_t c = c_min + id;
    if (c > c_max) return;

    RNS512 z;
    uint64_t carry = 0;
    for(int i=0; i<8; i++) {
        uint64_t lo = c * s_l.w[i];
        uint64_t hi = mulhi(c, s_l.w[i]);
        
        uint64_t sum1 = lo + carry;
        uint64_t c1 = (sum1 < carry) ? 1 : 0;
        z.w[i] = sum1;
        carry = hi + c1;
    }
    
    carry = 0;
    for(int i=0; i<8; i++) {
        uint64_t sum1 = z.w[i] + r_i.w[i];
        uint64_t c1 = (sum1 < z.w[i]) ? 1 : 0;
        uint64_t sum2 = sum1 + carry;
        uint64_t c2 = (sum2 < sum1) ? 1 : 0;
        z.w[i] = sum2;
        carry = c1 + c2;
    }

    bool passed = true;
    RNS512 one;
    for(int i=0; i<8; i++) one.w[i] = 0;
    one.w[0] = 1;

    for (uint32_t i = 0; i < num_obstructions; i++) {
        Obstruction obs = obstructions[i];
        
        RNS512 mod_pe = mont_mul(z, one, obs.pe, obs.pe_m0_prime);
        if (is_zero(mod_pe)) {
            RNS512 mod_pe1 = mont_mul(z, one, obs.pe1, obs.pe1_m0_prime);
            if (!is_zero(mod_pe1)) {
                passed = false;
                break;
            }
        }
    }

    if (!passed) {
        if (enable_diagnostics != 0) {
            uint32_t word_idx = id / 32;
            uint32_t bit_idx = id % 32;
            atomic_fetch_or_explicit(&bit_vector[word_idx], 1 << bit_idx, memory_order_relaxed);
        }
    } else {
        uint idx = atomic_fetch_add_explicit(valid_count, 1, memory_order_relaxed);
        valid_indices[idx] = id;
    }
}

struct TestInput {
    RNS512 a;
    RNS512 b;
    RNS512 m;
    uint64_t m0_prime;
};

struct TestOutput {
    RNS512 res;
};

kernel void test_gcd_kernel(
    device const TestInput* inputs [[buffer(0)]],
    device TestOutput* outputs [[buffer(1)]],
    uint id [[thread_position_in_grid]]
) {
    outputs[id].res = gcd(inputs[id].a, inputs[id].b);
}

kernel void test_mont_mul_kernel(
    device const TestInput* inputs [[buffer(0)]],
    device TestOutput* outputs [[buffer(1)]],
    uint id [[thread_position_in_grid]]
) {
    outputs[id].res = mont_mul(inputs[id].a, inputs[id].b, inputs[id].m, inputs[id].m0_prime);
}
