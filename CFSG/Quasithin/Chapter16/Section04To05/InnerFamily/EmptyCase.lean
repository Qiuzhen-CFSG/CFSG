module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion

/-!
# Products of commuting conjugate involutions in the empty-family case

A Sylow subgroup of order two contains every involution in its centralizer.
Thus a distinct commuting L-conjugate of r cannot lie in K′. If that conjugate
is r v with v in L′, the inner-involution detector, now applied with base L′,
contradicts the transported empty-family assumption. This proves the exclusion
v ∉ L′ in source (+), and hence (!) whenever O²(C_L(r)) ≤ L′ is supplied by
16.4.8. Neither fusion restriction is an input.

The order assertion 16.4.9(1) remains an explicit prerequisite; the empty-family
assumption is the contrary assumption used to prove 16.4.9(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.1190.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow subgroup of order two has no distinct commuting involution in its overgroup. -/
theorem SylowIn.involution_eq_of_commute_of_card_two {R H : Subgroup G} (hR : SylowIn R H)
    (hcard : Nat.card R = 2) {r s : G} (hrR : r ∈ R) (hr2 : orderOf r = 2)
    (hsH : s ∈ H) (hs2 : orderOf s = 2) (hcomm : Commute r s) : s = r := by
  classical
  have heq : zpowers r = R := eq_of_le_of_card_ge (zpowers_le.mpr hrR)
    (by rw [Nat.card_zpowers, hr2, hcard])
  have hsrN : zpowers s ≤ normalizer (zpowers r : Set G) := by
    apply zpowers_le.mpr
    apply centralizer_le_normalizer
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hcomm.eq.symm
  have hpr : IsPGroup 2 (zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr2, pow_one])
  have hps : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  have hsR : s ∈ R := by
    have hsup := hR.maximal (hpr.to_sup_of_normal_left' hps hsrN)
      (sup_le (zpowers_le.mpr (hR.le hrR)) (zpowers_le.mpr hsH))
      (heq ▸ le_sup_left)
    rw [← hsup]
    exact mem_sup_right (mem_zpowers s)
  have hsCases : s = 1 ∨ s = r := by
    rw [← heq] at hsR
    have hh := mem_zpowers_iff_mem_range_orderOf.mp hsR
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hh
    have hn2 : n < 2 := by simpa only [Finset.mem_range, hr2] using hn
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact Or.inl (by simpa only [pow_zero] using he.symm)
    · exact Or.inr (by simpa only [pow_one] using he.symm)
  exact hsCases.resolve_left (fun h => by simp [h] at hs2)


/-- The exclusion v ∉ L′ in source (+), derived from the empty-family assumption. -/
theorem IntersectionSetup.conjugate_involution_product_not_mem_component {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) {r l v : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L)
    (hcomm : Commute r (MulAut.conj l r)) (hne : MulAut.conj l r ≠ r)
    (hv : MulAut.conj l r = r * v) : v ∉ L.conjBy g := by
  have hcard : Nat.card R = 2 := hsmall _ h.mem_delta
    (fun hh => hempty ⟨_, hh⟩) R h.sylow
  have hnL : L ≤ normalizer (centralizer (L : Set G) : Set G) := by
    rw [h.normalizers_eq]
    exact L.le_normalizer
  have hrN := (h.sylow.le hr).2
  have hsN : MulAut.conj l r ∈ normalizer (centralizer (L : Set G) : Set G) := by
    exact (normalizer (centralizer (L : Set G) : Set G)).mul_mem
      ((normalizer (centralizer (L : Set G) : Set G)).mul_mem (hnL hl) hrN)
      ((normalizer (centralizer (L : Set G) : Set G)).inv_mem (hnL hl))
  have hs2 : orderOf (MulAut.conj l r) = 2 := (MulAut.conj l).orderOf_eq r |>.trans hr2
  have hsnot : MulAut.conj l r ∉ (centralizer (L : Set G)).conjBy g := by
    intro hs
    exact hne (SylowIn.involution_eq_of_commute_of_card_two h.sylow hcard hr hr2 ⟨hs, hsN⟩ hs2 hcomm)
  have hC : (centralizer (L : Set G)).conjBy g =
      centralizer (L.conjBy g : Set G) := map_centralizer_equiv _ (MulAut.conj g)
  intro hvL
  have hdet : ((centralizer (L : Set G)).conjBy g).conjBy l ∈ deltaZero (L.conjBy g) := by
    apply mem_deltaZero_of_inner_involution (normalizers_eq_conjBy h.normalizers_eq g)
      (hsmall.conjBy g) ⟨l, by rw [hC]⟩
      (show MulAut.conj l r ∈ ((centralizer (L : Set G)).conjBy g).conjBy l from
        ⟨r, (h.sylow.le hr).1, rfl⟩) hs2
    · rw [hv, ← hC]
      exact mul_mem_sup (h.sylow.le hr).1 hvL
    · rwa [← hC]
  exact hempty ((deltaZero_conjBy_nonempty_iff g).mp ⟨_, hdet⟩)

/-- Source (!), for any subgroup of C_L(r) contained in L′. Apply 16.4.8
with the actual two-residual O²(C_L(r)) to obtain the printed instance. -/
theorem IntersectionSetup.conjugate_product_eq_one_of_le_component {T : Sylow 2 G} {z g : G} {L R D : Subgroup G}
    (h : IntersectionSetup T z L g R) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty) {r l v : G}
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hl : l ∈ L)
    (hD : D ≤ L.conjBy g) (hDC : D ≤ centralizer ({r} : Set G)) (hvD : v ∈ D)
    (hv : MulAut.conj l r = r * v) : v = 1 := by
  by_contra hv1
  have hrv : Commute r v := (mem_centralizer_singleton_iff.mp (hDC hvD)).symm
  have hcomm : Commute r (MulAut.conj l r) := by
    rw [hv]
    exact (Commute.refl r).mul_right hrv
  have hne : MulAut.conj l r ≠ r := by
    intro he
    have hh : r * v = r * 1 := by simpa only [mul_one] using hv.symm.trans he
    exact hv1 (mul_left_cancel hh)
  exact h.conjugate_involution_product_not_mem_component hsmall hempty hr hr2 hl
    hcomm hne hv (hD hvD)

end CFSG.Quasithin.Chapter16.Intersections
