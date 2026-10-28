module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CPU
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The section kernel fixes the exchanged component

The marked split complement in 1.3.4 meets the selected component in a
nontrivial three-subgroup. A C-component with simple two-core quotient is
the unique C-component containing such a subgroup: modulo the ambient
two-core, its simple image has trivial intersection with any other
C-component. The actual PSL₂ model and perfectness give this simplicity.

Write a kernel element using U=O₂(X)N_U(P). The first factor normalizes the
component through the C-component layer. The second centralizes P, since
its commutators lie both in P and in O₂(X), and consequently fixes the
component by the preceding uniqueness argument. No assertion about the
centralizer of an unspecified quotient is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.3.4(1),
printed pp.509–510, and the characteristic-two paragraph of 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs

private theorem common_odd {G : Type*} [Group G] [Finite G] {L D A : Subgroup G}
    (hL : L.IsCComponent) (hD : D.IsCComponent)
    (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (hAL : A ≤ L) (hAD : A ≤ D) (hA : IsPGroup 3 A) (hne : A ≠ ⊥) : L = D := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let L' := L.map q
  let D' := D.map q
  let A' := A.map q
  let _ := pCore_isNilpotent (p := 2) (G := G)
  have hL' : L'.IsCComponent := hL.map_quotient _
  have hD' : D'.IsCComponent := hD.map_quotient _
  let _ := hs
  let _ : IsSimpleGroup L' := (cComponentTwoCoreQuotientEquiv hL).symm.isSimpleGroup
  have hn : (D'.subgroupOf L').Normal := normal_subgroupOf_of_le_normalizer
    ((le_cComponentLayer hL').trans (cComponentLayer_le_normalizer hD'))
  have hAb : A' ≠ ⊥ := by
    intro hb
    have hAc : A ≤ pCore 2 G := by simpa only [A', q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb
    have hd := hA.disjoint_of_coprime (pCore_isPGroup (p := 2) (G := G)) (by decide : Nat.Coprime 3 2)
    exact hne (le_bot_iff.mp (fun x hx => hd.le_bot ⟨hx, hAc hx⟩))
  have hle : L' ≤ D' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D'.subgroupOf L') hn with hb | ht
    · exfalso
      apply hAb
      apply le_bot_iff.mp
      intro a ha
      have hmem : (⟨a, map_mono hAL ha⟩ : L') ∈ D'.subgroupOf L' := map_mono hAD ha
      exact congrArg Subtype.val (show (⟨a, map_mono hAL ha⟩ : L') = 1 from mem_bot.mp (hb ▸ hmem))
    · intro a ha
      exact (show (⟨a, ha⟩ : L') ∈ D'.subgroupOf L' from ht ▸ mem_top _)
  exact hL.eq_of_map_quotient_eq hD _ (hL'.eq_of_le hD' hle)

private theorem centralizer_normalizes_component {G : Type*} [Group G] [Finite G]
    {L A : Subgroup G} (hL : L.IsCComponent)
    (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (hAL : A ≤ L) (hA : IsPGroup 3 A) (hne : A ≠ ⊥) :
    centralizer (A : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (common_odd hL (hL.map_equiv (MulAut.conj g)) hs hAL ?_ hA hne).symm
  intro a ha
  refine ⟨a, hAL ha, ?_⟩
  change g * a * g⁻¹ = a
  rw [← mem_centralizer_iff.mp hg a ha, mul_assoc, mul_inv_cancel, mul_one]

private theorem relative_centralizer_normalizes_component {G : Type*} [Group G] [Finite G]
    {H L A : Subgroup G} (hL : L ∈ CFSG.Quasithin.Chapter1.cComponentsIn H)
    (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (hAL : A ≤ L) (hA : IsPGroup 3 A) (hne : A ≠ ⊥) :
    H ⊓ centralizer (A : Set G) ≤ normalizer (L : Set G) := by
  let e := subgroupOfEquivOfLe hL.1
  let eqv := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) e (pCore_map_iso 2 e)
  let _ := hs
  have hs' : IsSimpleGroup ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) := eqv.isSimpleGroup
  have hA' : A.subgroupOf H ≠ ⊥ := by
    intro hb
    have he := congrArg (Subgroup.map H.subtype) hb
    exact hne (by simpa only [map_subgroupOf_eq_of_le (hAL.trans hL.1), Subgroup.map_bot] using he)
  have hnorm := centralizer_normalizes_component hL.2 hs'
    (show A.subgroupOf H ≤ L.subgroupOf H from fun _ ha => hAL ha)
    hA.comap_subtype hA'
  intro g hg
  have hgc : (⟨g, hg.1⟩ : H) ∈ centralizer (A.subgroupOf H : Set H) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp hg.2 a ha)
  have hn := hnorm hgc
  rw [← subgroupOf_normalizer_eq hL.1] at hn
  exact hn

private theorem linear_quotient_simple {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) :
    IsSimpleGroup Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2, F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.XiEmbedding
open CFSG.Quasithin.ChapterA.Section04
/-- The actual section kernel fixes the exchanged component. The quasisimple
clause and split complement here are the retained conclusions of 1.3.4;
normalization is deduced from the rank-one model and the actual factor actions. -/
theorem swapped_kernel_normalizes {G : Type*} [Group G] [Finite G]
    {U X P H L M : Subgroup G} (h : LocalInput 3 U X P H)
    (hL : L ∈ cComponentsIn H) (hq : IsQuasisimple (XiQuotient L))
    (hX : X ≤ componentOrbit L U) (ha : SwappedFactors U P L)
    (hm : SwappedModel 3 (XiQuotient L)) :
    U ⊓ twoSectionCentralizer X M ≤ normalizer (L : Set G) := by
  have hs : IsSimpleGroup (L ⧸ pCore 2 L) := by
    rcases hm with ⟨n, _, _, hm⟩ | ⟨p, _, _, hm⟩ <;> exact linear_quotient_simple hq hm
  have hAL : P ⊓ L ≠ ⊥ := by
    intro hb
    obtain ⟨_, t, _, _, he, _, _⟩ := ha
    have hPb : P = ⊥ := by simpa only [hb, Subgroup.conjBy, Subgroup.map_bot, bot_sup_eq] using he
    exact h.complement_not_cyclic (hPb ▸ inferInstance)
  have hnorm := relative_centralizer_normalizes_component hL hs inf_le_right
    (h.odd_complement.isPGroup.to_le (show P ⊓ L ≤ P from inf_le_left)) hAL
  have hUH : U ≤ H := le_sup_right.trans h.overgroup
  have hcoreN : X.pCoreIn 2 ≤ normalizer (L : Set G) :=
    (pCoreIn_le 2 X).trans (hX.trans (cComponentOrbit_le_normalizer hL hUH))
  let C := X.pCoreIn 2
  let N := U ⊓ normalizer (P : Set G)
  have hCU : C ≤ U := h.core_le_two_group
  have hUC : U ≤ normalizer (C : Set G) :=
    h.invariant.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  let _ : (C.subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer hUC
  have hgen : C.subgroupOf U ⊔ N.subgroupOf U = ⊤ := by
    rw [← subgroupOf_sup hCU (show N ≤ U from inf_le_left), ← h.normalizer_factor, subgroupOf_self]
  intro r hr
  have hr' : (⟨r, hr.1⟩ : U) ∈ C.subgroupOf U ⊔ N.subgroupOf U := hgen ▸ mem_top _
  obtain ⟨c, hc, n, hn, he⟩ := mem_sup_of_normal_left.mp hr'
  have hcC : (c : G) ∈ twoSectionCentralizer X ⊤ :=
    pCoreIn_le_twoSectionCentralizer X ⊤ le_top hc
  have hrC : r ∈ twoSectionCentralizer X ⊤ := ⟨mem_top _, hr.2.2⟩
  have hnC : (n : G) ∈ twoSectionCentralizer X ⊤ := by
    have he' : (c : G)⁻¹ * r = (n : G) := by
      have hh := congrArg Subtype.val he
      change (c : G) * (n : G) = r at hh
      rw [← hh, inv_mul_cancel_left]
    exact he' ▸ (twoSectionCentralizer X ⊤).mul_mem
      ((twoSectionCentralizer X ⊤).inv_mem hcC) hrC
  have hnP : (n : G) ∈ centralizer (P : Set G) := by
    apply mem_centralizer_iff.mpr
    intro p hp
    have hcomm : ⁅(n : G), p⁆ = 1 := by
      apply h.disjoint.le_bot
      refine ⟨hnC.2.2 p (h.complement_le hp), ?_⟩
      change (n : G) * p * (n : G)⁻¹ * p⁻¹ ∈ P
      exact P.mul_mem ((mem_normalizer_iff.mp hn.2 p).mp hp) (P.inv_mem hp)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
  have hnL : (n : G) ∈ normalizer (L : Set G) :=
    hnorm ⟨hUH n.property, centralizer_le inf_le_left hnP⟩
  have he' : (c : G) * (n : G) = r := congrArg Subtype.val he
  exact he' ▸ (normalizer (L : Set G)).mul_mem (hcoreN hc) hnL

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.ComponentInputs
