// AUTO-GENERATED from bounds_manifest.json. DO NOT EDIT.

pub const EXPORTED_BOUNDS_MANIFEST_HASH: &str =
    "d11f5adc1515970327e7d8fe3c7893bfee310cb09c0b08b5c9e85789200773d7";

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
