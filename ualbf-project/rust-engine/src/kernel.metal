#include <metal_stdlib>
using namespace metal;

struct U256 {
    uint32_t w[8];
};

struct Task {
    U256 n;
    U256 r_squared;
    uint32_t m0_prime;
    uint32_t padding[3];
};

struct Result {
    U256 factor;
};

inline bool is_zero(U256 a) {
    for(int i=0; i<8; i++) if(a.w[i] != 0) return false;
    return true;
}

inline bool is_one(U256 a) {
    if(a.w[0] != 1) return false;
    for(int i=1; i<8; i++) if(a.w[i] != 0) return false;
    return true;
}

inline bool is_even(U256 a) {
    return (a.w[0] & 1) == 0;
}

inline int cmp(U256 a, U256 b) {
    for(int i=7; i>=0; i--) {
        if(a.w[i] > b.w[i]) return 1;
        if(a.w[i] < b.w[i]) return -1;
    }
    return 0;
}

inline U256 sub(U256 a, U256 b) {
    U256 res;
    bool borrow = false;
    for(int i=0; i<8; i++){
        uint64_t diff = (uint64_t)a.w[i] - b.w[i] - borrow;
        res.w[i] = (uint32_t)diff;
        borrow = (diff >> 32) != 0;
    }
    return res;
}

inline U256 shr1(U256 a) {
    U256 res;
    uint32_t carry = 0;
    for(int i=7; i>=0; i--) {
        uint32_t next_carry = (a.w[i] & 1) << 31;
        res.w[i] = (a.w[i] >> 1) | carry;
        carry = next_carry;
    }
    return res;
}

inline U256 gcd(U256 a, U256 b) {
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
            U256 t = a; a = b; b = t;
        }
        b = sub(b, a);
    }
    
    U256 res = a;
    for(int i=0; i<shift; i++) {
        uint32_t carry = 0;
        for(int j=0; j<8; j++) {
            uint32_t next_carry = res.w[j] >> 31;
            res.w[j] = (res.w[j] << 1) | carry;
            carry = next_carry;
        }
    }
    return res;
}

inline U256 mont_mul(U256 a, U256 b, U256 m, uint32_t m0_prime) {
    uint32_t t[16] = {0};
    uint32_t t16 = 0;
    
    for (int i = 0; i < 8; ++i) {
        uint64_t c = 0;
        for (int j = 0; j < 8; ++j) {
            c += t[i + j] + (uint64_t)a.w[i] * b.w[j];
            t[i + j] = (uint32_t)c;
            c >>= 32;
        }
        t[i + 8] = (uint32_t)c;
        
        uint32_t u = t[i] * m0_prime;
        c = 0;
        for (int j = 0; j < 8; ++j) {
            c += t[i + j] + (uint64_t)u * m.w[j];
            t[i + j] = (uint32_t)c;
            c >>= 32;
        }
        c += t[i + 8];
        t[i + 8] = (uint32_t)c;
        if (i == 7) {
            t16 = c >> 32;
        } else {
            t[i + 9] += c >> 32;
        }
    }
    
    U256 res;
    for(int i=0; i<8; i++) res.w[i] = t[8+i];
    
    bool borrow = false;
    U256 subtracted;
    for (int i = 0; i < 8; ++i) {
        uint64_t diff = (uint64_t)res.w[i] - m.w[i] - borrow;
        subtracted.w[i] = (uint32_t)diff;
        borrow = (diff >> 32) != 0;
    }
    if (borrow && t16 == 0) return res;
    return subtracted;
}

inline U256 mont_add(U256 a, U256 b, U256 m) {
    U256 res;
    uint64_t c = 0;
    for(int i=0; i<8; i++){
        c += a.w[i];
        c += b.w[i];
        res.w[i] = (uint32_t)c;
        c >>= 32;
    }
    bool borrow = false;
    U256 sub_res;
    for(int i=0; i<8; i++){
        uint64_t diff = (uint64_t)res.w[i] - m.w[i] - borrow;
        sub_res.w[i] = (uint32_t)diff;
        borrow = (diff >> 32) != 0;
    }
    if (borrow && c == 0) return res;
    return sub_res;
}

inline U256 mont_to_norm(U256 a, U256 m, uint32_t m0_prime) {
    U256 one;
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
    U256 n = t.n;
    
    // Test small c from 1 to 40
    for(uint32_t c = 1; c < 40; ++c) {
        U256 C;
        for(int i=0; i<8; i++) C.w[i] = 0;
        C.w[0] = c;
        C = mont_mul(C, t.r_squared, n, t.m0_prime);
        
        U256 two;
        for(int i=0; i<8; i++) two.w[i] = 0;
        two.w[0] = 2;
        U256 X = mont_mul(two, t.r_squared, n, t.m0_prime);
        U256 Y = X;
        
        U256 d;
        for(int i=0; i<8; i++) d.w[i] = 0;
        d.w[0] = 1;
        
        uint32_t r = 1;
        U256 Q;
        for(int i=0; i<8; i++) Q.w[i] = 0;
        Q.w[0] = 1;
        Q = mont_mul(Q, t.r_squared, n, t.m0_prime);
        
        U256 YS = Y;
        
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
                    U256 diff = cmp(X, Y) > 0 ? sub(X, Y) : sub(Y, X);
                    Q = mont_mul(Q, diff, n, t.m0_prime);
                }
                U256 Q_norm = mont_to_norm(Q, n, t.m0_prime);
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
                U256 YS_norm = mont_to_norm(YS, n, t.m0_prime);
                U256 X_norm = mont_to_norm(X, n, t.m0_prime);
                U256 diff = cmp(X_norm, YS_norm) > 0 ? sub(X_norm, YS_norm) : sub(YS_norm, X_norm);
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
