module
public import Theory.GroupTheory.PCoreQuotientBorelNormalizer

/-!
# Sylow normalizers for prime-group supplements

A prime-group R normalizing K and containing a full Sylow subgroup P of K
acts inner on the centerless quotient K/O_p(K) if the outer group has order
prime to p. The existing inner-supplement calculation gives
R = P O_p(KR), so the original N_K(P) normalizes R.

This extends the ambient-Sylow version to the stabilizer N_R(K) used in
Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A prime-group supplement containing a full Sylow subgroup has its local
Sylow normalizer controlled by that supplement when the outer action is coprime. -/
theorem pGroup_sylow_normalizer_le_of_coprime_outer
    (R K : Subgroup G) (hR : IsPGroup p R)
    (hn : R ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore p K) = ⊥)
    (ho : Nat.Coprime p (Nat.card (MulAut.Outer (K ⧸ pCore p K))))
    (P : Sylow p K) (hPR : (P : Subgroup K).map K.subtype ≤ R) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (R : Set G) := by
  let a : R →* MulAut (K ⧸ pCore p K) :=
    (pCoreJoinAction p hn).comp (inclusion le_sup_right)
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (K ⧸ pCore p K))).comp a
  have hi (t : R) : a t ∈ MulAut.innerSubgroup (K ⧸ pCore p K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f t = 1
    obtain ⟨n, hn⟩ := hR t
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (ho.pow_left n)
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hn, map_one]
    · exact _root_.orderOf_dvd_natCard (f t)
  have hfactor := sup_core_factor_of_inner_action K R hn hR
    hz P hPR hi
  let W := K ⊔ R
  have hcore : W ≤ normalizer (W.pCoreIn p : Set G) :=
    W.le_normalizer.trans (normalizer_le_normalizer_characteristic_image W (pCore p W))
  have h1 : (normalizer (P : Set K)).map K.subtype ≤
      normalizer ((P : Subgroup K).map K.subtype : Set G) :=
    (P : Subgroup K).le_normalizer_map K.subtype
  have h2 : (normalizer (P : Set K)).map K.subtype ≤
      normalizer (W.pCoreIn p : Set G) :=
    (map_subtype_le _).trans (le_sup_left.trans hcore)
  change _ ≤ normalizer (R : Set G)
  rw [hfactor]
  exact (le_inf h1 h2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

end Subgroup
