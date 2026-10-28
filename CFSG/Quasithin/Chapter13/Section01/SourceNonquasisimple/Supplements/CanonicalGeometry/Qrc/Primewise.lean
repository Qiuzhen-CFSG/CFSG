module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Standing
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Primewise intersections in the 13.1.9 qrc argument

A Sylow-containing subgroup which misses X∈Ξ(G,T) has trivial image
in X/O₂,Φ(X): irreducibility gives a zero or full image, and Frattini's
nongeneration property together with O₂(X)≤T excludes the full image.
The proved (+) uniqueness forces every HStar comparison group to miss
each supported canonical radical. This gives the exact primewise bound
for B=O²(H∩N_G(L)), retaining the two-residual and the quotient maps.

The same (+) centralizer containment excludes the central omega alternative
of 3.1.7. Canonical starred membership remains the authorized earlier
premise produced by qt-d-1314-canonical-radical-star and discharged by
qt-d-1317-source. Two-closedness of the whole radical intersection and
normalization of the canonical supplement remain with qt-d-1317-supplements.

Source: Aschbacher--Smith, 13.1.9, case (I) paragraph, printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- A Sylow-containing subgroup missing a Xi member meets it only in
its two-core/Frattini preimage. -/
private theorem xi_intersection_le_frattini {X H : Subgroup G}
    (hX : XiMember (T : Subgroup G) X) (hTH : (T : Subgroup G) ≤ H)
    (hXH : ¬ X ≤ H) :
    H ⊓ X ≤ ((frattini (XiQuotient X)).comap
      (QuotientGroup.mk' (pCore 2 X))).map X.subtype := by
  let D := H.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (QuotientGroup.mk' (frattini (XiQuotient X))).comp q
  let _ := conjMulDistribMulActionOfLeNormalizer (T : Subgroup G) X hX.invariant
  have he (t : T) (x : X) :
      xiFrattiniAction T X hX.invariant t (f x) = f (t • x) := by
    simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk, f, q]
    rfl
  have hstable : ∀ t : T, ∀ a ∈ D.map f,
      xiFrattiniAction T X hX.invariant t a ∈ D.map f := by
    rintro t a ⟨x, hx, rfl⟩
    refine ⟨t • x, ?_, (he t x).symm⟩
    exact H.mul_mem (H.mul_mem (hTH t.property) hx) (H.inv_mem (hTH t.property))
  have hz : D.map f = ⊥ := by
    rcases hX.irreducible (D.map f) hstable with hb | ht
    · exact hb
    · exfalso
      have hqimage : D.map q = ⊤ := by
        apply frattini_nongenerating
        have hm := congrArg (comap (QuotientGroup.mk' (frattini (XiQuotient X)))) ht
        rw [← map_map, comap_map_eq, QuotientGroup.ker_mk', comap_top] at hm
        exact hm
      have hcore : pCore 2 X ≤ D := by
        intro x hx
        exact hTH ((hX.pCoreIn_le_of_isSylowIn
          ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩)
          (mem_map_of_mem X.subtype hx))
      have hD : D = ⊤ := by
        have hm := congrArg (comap q) hqimage
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top,
          sup_eq_left.mpr hcore] using hm
      exact hXH (subgroupOf_eq_top.mp hD)
  rintro x ⟨hxH,hxX⟩
  refine ⟨⟨x,hxX⟩, ?_, rfl⟩
  have hx : f ⟨x,hxX⟩ = 1 := mem_bot.mp (hz ▸ mem_map_of_mem f hxH)
  exact (QuotientGroup.eq_one_iff (q ⟨x,hxX⟩)).mp hx

/-- The original (+) uniqueness excludes a supported canonical radical
from every HStar comparison group. -/
theorem canonical_radical_not_le_comparison
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) : ¬ XiP p L ≤ H := by
  intro hXH
  have hcore : pCore 2 H ≠ ⊥ := by
    intro hz
    exact hH.1.1.1 (by rw [pCoreIn, hz, Subgroup.map_bot])
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  have hc := Escape.canonical_standing_of_star h hmany hL hn ho hd
    (hs L hL hn p (Fact.out : p.Prime) ho hd)
  exact hH.1.2 (hHN.trans_eq (hc.2.2.2.1 N hN ((sup_le hXH hH.1.1.2).trans hHN)))

/-- The entire comparison subgroup meets each supported canonical radical
in its two-core/Frattini preimage. This stronger form will be transported
to the actual omega subgroup in L/O₂(L). -/
theorem comparison_inf_radical_le_frattini
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    H ⊓ XiP p L ≤ ((frattini (XiQuotient (XiP p L))).comap
      (QuotientGroup.mk' (pCore 2 (XiP p L)))).map (XiP p L).subtype :=
  xi_intersection_le_frattini
    (hs L hL hn p (Fact.out : p.Prime) ho hd).1 hH.1.1.2
    (canonical_radical_not_le_comparison h hmany hs hL hn hH ho hd)

/-- The primewise Frattini containment for the actual two-residual
B=O²(H∩N_G(L)), retaining the source quotient map. -/
theorem comparison_twoResidual_inf_radical_le_frattini
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ((pResidual 2 (H ⊓ normalizer (L : Set G) : Subgroup G)).map
      (H ⊓ normalizer (L : Set G)).subtype) ⊓ XiP p L ≤
      ((frattini (XiQuotient (XiP p L))).comap
        (QuotientGroup.mk' (pCore 2 (XiP p L)))).map (XiP p L).subtype := by
  apply (inf_le_inf_right _ ((map_subtype_le _).trans inf_le_left)).trans
  exact comparison_inf_radical_le_frattini h hmany hs hL hn hH ho hd

/-- The original (+) centralizer containment excludes the central omega
alternative of 3.1.7 for the actual HStar comparison subgroup. -/
theorem comparison_omegaCenter_not_central
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
  intro hz
  have hHC : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    intro x hx z hz'
    obtain ⟨y,hy,he⟩ := hz hz'
    have hc := (mem_center_iff.mp hy) (⟨x,hx⟩ : H)
    have hc' := congrArg (fun u : H => (u : G)) hc
    change (y : G) = z at he
    change x * (y : G) = (y : G) * x at hc'
    simpa only [he] using hc'.symm
  exact hH.1.2 (hHC.trans
    (Escape.nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).2.1)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
