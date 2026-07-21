// AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.

pub const EXPORTED_BOUNDS_MANIFEST_HASH: &str =
    "819e61abfc1a5732ec3a1ccfb4ca53c6346fe632042d934933cb2c237d524181";

use vstd::prelude::*;

verus! {
    pub spec fn lean_qpn_totient_bound_num() -> nat { 20442 }
    pub spec fn lean_qpn_totient_bound_den() -> nat { 10000 }

    pub spec fn lean_hagis1982_min_prime_factors() -> nat { 7 }
    pub spec fn lean_hagis1982_offset() -> nat { 0 }
    pub spec fn lean_hagis1982_combined() -> nat { 7 }

    pub spec fn lean_prasad_sunitha_bound() -> nat { 15 }
    pub spec fn lean_prasad_sunitha_offset() -> nat { 0 }
    pub spec fn lean_prasad_sunitha_combined() -> nat { 15 }

    pub spec fn lean_miller_rabin_20_base_sufficiency() -> bool { true }

    pub proof fn prove_combined_bounds() {
        assert(lean_hagis1982_combined() == lean_hagis1982_min_prime_factors() + lean_hagis1982_offset());
        assert(lean_prasad_sunitha_combined() == lean_prasad_sunitha_bound() + lean_prasad_sunitha_offset());
    }
}
