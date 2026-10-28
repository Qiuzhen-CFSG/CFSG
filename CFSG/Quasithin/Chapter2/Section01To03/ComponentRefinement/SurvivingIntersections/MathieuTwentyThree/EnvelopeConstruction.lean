module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyThree.EnvelopeConstruction.Basic
public import Theory.GroupTheory.AlternatingPowerTwoExtension.Transport
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.HeptadAutomorphisms

/-!
# Construction of the full-S M23 envelope

Let K be the embedded pullback of the fixed-heptad stabilizer. The projected
involution is fixed by N_S(L), whose induced automorphisms therefore preserve
K. Inside H, the S-conjugates of K form independent commuting factors in
distinct centerless components. The component-orbit construction shows that
X = ⟨K,S⟩ has a nontrivial self-centralizing two-core and an actual normal
section mapping onto a finite direct power of A7 with two-group kernel and
two-group upper quotient. Transport along H's inclusion gives the envelope
in G, retaining all of S.

Source: Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526, using 1.1.5(3)(f),
printed p.502, combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M23Geometry Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Adjoining the whole supplied Sylow subgroup to the heptad factor gives
the required characteristic-two overgroup and alternating-power section. -/
theorem mathieuTwentyThreeHeptadSubgroup_sup_sylow_envelope
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    MathieuTwentyThreeLocalEnvelope L ((S : Subgroup H).map H.subtype) e t
      (mathieuTwentyThreeHeptadSubgroup e t ⊔ (S : Subgroup H).map H.subtype) := by
  let := h.finite
  let K := mathieuTwentyThreeHeptadSubgroup e t
  have hKL : K ≤ L := mathieuTwentyThreeHeptadSubgroup_le e t
  have hKH : K ≤ H := hKL.trans h.component_le
  let KH := K.subgroupOf H
  let eK := (subgroupOfEquivOfLe hKH).trans (mathieuTwentyThreeHeptadSubgroupEquiv e t)
  obtain ⟨hne, hchar, f, hf, hk⟩ :=
    heptad_stabilizer_local_structure (fixedHeptad_mem ((e.orderOf_eq t).trans ht2)) eK
  have hnorm := mathieuTwentyThreeHeptadSubgroup_normalized_of_aut_invariant h e ht
    (fun α hα => fixedHeptad_stabilizer_map_of_aut_fix ((e.orderOf_eq t).trans ht2) α hα)
  have hinv : (S : Subgroup H) ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (KH : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le, ← subgroupOf_normalizer_eq hKH]
    rintro s ⟨hs, hsN⟩
    exact hnorm ⟨mem_map_of_mem H.subtype hs, hsN⟩
  have hZ := mathieuTwentyThree_center_eq_bot
    ((subgroupOfEquivOfLe h.component_le).trans e)
  obtain ⟨hXne, hXchar, hXext⟩ := component_local_closure h.component hZ S.isPGroup'
    (show KH ≤ L.subgroupOf H from comap_mono hKL) hinv hne hchar f hf hk
  let XH := KH ⊔ (S : Subgroup H)
  let X := XH.map H.subtype
  let eX : XH ≃* X := XH.equivMapOfInjective H.subtype H.subtype_injective
  have hXeq : X = K ⊔ (S : Subgroup H).map H.subtype := by
    change (KH ⊔ (S : Subgroup H)).map H.subtype = _
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH]
  have hXcore : pCore 2 X ≠ ⊥ := by
    intro hb
    apply hXne
    exact ((pCore 2 XH).map_eq_bot_iff_of_injective eX.injective).mp
      ((pCore_map_iso 2 eX).trans hb)
  have hHe : X ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 eX).mp hXchar)
  have hH : X ∈ Chapter1.H G := by
    intro hb
    exact hXcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hb)
  have hExt : AlternatingPowerTwoExtension X 7 := hXext.of_equiv eX
  rw [hXeq] at hHe hH hExt
  refine ⟨sup_le_sup_right hKL _, ⟨hHe, hH, ?_⟩, le_sup_left, hExt⟩
  change (S : Subgroup H).map H.subtype ≤ K ⊔ _
  exact le_sup_right

/-- The full-S local envelope exists from the actual M23 model and involution
projection, with no further normalization or local-structure premises. -/
theorem mathieuTwentyThree_exists_local_envelope
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M23) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ X : Subgroup G,
      MathieuTwentyThreeLocalEnvelope L ((S : Subgroup H).map H.subtype) e t X :=
  ⟨_, mathieuTwentyThreeHeptadSubgroup_sup_sylow_envelope h e ht ht2⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
