module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Orbit
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.InvolutionCentralizer.Candidate

/-!
# The ambient centralizer of the standard J₃ involution

The fixed local candidate centralizes a, and 8722 explicitly checked conjugates
of a are distinct. Under the two numerical order premises the candidate has
index 26163, so the centralizer index divides 26163 and is at least 8722.
Its complementary factor is at most two; oddness excludes two. Thus both
subgroups have the same order, and the checked containment is an equality.

This identifies the actual word-defined candidate with the ambient centralizer;
it assumes neither an ambient centralizer description nor normalizer coverage.
The parent J₃ assembly discharges the two numerical premises.

Source: GLS, Number 3, Table 5.3h, printed p.269, the entry C(2A). The finite
certificate uses the fixed degree-6156 ATLAS model; see `source/README.md`
in the companion directory for the untrusted discovery data and checked route.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
open Sporadic.Janko3 Sporadic.Janko3.TwoLocal

set_option maxRecDepth 40000 in
/-- The fixed two-local is exactly the ambient centralizer, under the two
numerical assumptions discharged by the parent model assembly. -/
public theorem involution_centralizer_eq_localFamily_zero
    (hG : Nat.card Model = 50232960) (hL : Nat.card (localFamily 0) = 1920) :
    Subgroup.centralizer ({a} : Set Model) = localFamily 0 := by
  have hl := (localFamily 0).index_mul_card
  rw [hG, hL] at hl
  have hl' : (localFamily 0).index = 26163 := by omega
  obtain ⟨k, hk⟩ := Subgroup.index_dvd_of_le localFamily_zero_le_involution_centralizer
  rw [hl'] at hk
  have hm := Nat.mul_le_mul_right k InvolutionCertificate.index_lower_bound
  rw [← hk] at hm
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hc : (Subgroup.centralizer ({a} : Set Model)).index = 26163 := by
    rcases hk' with rfl | rfl | rfl <;> omega
  have hcard := (Subgroup.centralizer ({a} : Set Model)).index_mul_card
  rw [hc, hG] at hcard
  have heq := Subgroup.eq_of_le_of_card_ge localFamily_zero_le_involution_centralizer (show
      Nat.card (Subgroup.centralizer ({a} : Set Model)) ≤ Nat.card (localFamily 0) by
    rw [hL]
    omega)
  exact heq.symm

/-- The ambient bound required by the elementary-normalizer coverage proof. -/
public theorem involution_centralizer_le_localFamily_zero
    (hG : Nat.card Model = 50232960) (hL : Nat.card (localFamily 0) = 1920) :
    Subgroup.centralizer ({a} : Set Model) ≤ localFamily 0 :=
  (involution_centralizer_eq_localFamily_zero hG hL).le

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage
