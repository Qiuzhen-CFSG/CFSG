module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Cubic.Normalized
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SylowKernelCore

/-!
# Cubic blocks are determined by their embedded two-cores

Under the exact guard of C.1.9, two cubic blocks with the same embedded
four-group U coincide. Both lie in H = O₂,₃(G). The ambient two-core
centralizes U, so the normalizer of U in H contains O₂(H) and inherits
its self-centralizing two-core.

In that normalizer, both blocks fix the two-core modulo U. The two-layer
fixer theorem puts the kernel of their action on U inside the two-core.
Their action images have order three in Aut(U), of order six, and hence
coincide. Equality modulo the two-core then recovers the original
subnormal two-perfect subgroups by their residual characterization.

Applying the proved mutually normalizing dichotomy gives commutation of
distinct mutually normalizing cubic blocks. The general normalization
argument and unconditional commutation remain with the C.1.9 assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Proposition C.1.9, printed p.123, citing Aschbacher (1981), §3.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.BlockCommutation
variable {G : Type*} [Group G] [Finite G]

private theorem three_subgroups_eq_of_card_six {A : Type*} [Group A] [Finite A]
    (hc : Nat.card A = 6) (B C : Subgroup A)
    (hB : Nat.card B = 3) (hC : Nat.card C = 3) : B = C := by
  have hi : B.index = 2 := by
    have hh := B.card_mul_index
    rw [hc, hB] at hh
    omega
  let : B.Normal := normal_of_index_eq_two hi
  let q := QuotientGroup.mk' B
  have hd₁ : Nat.card (C.map q) ∣ 3 := hC ▸ C.card_map_dvd q
  have hd₂ : Nat.card (C.map q) ∣ 2 := by
    rw [← hi, B.index_eq_card]
    exact card_subgroup_dvd_card _
  have he : C.map q = ⊥ := Subgroup.card_eq_one.mp
    (Nat.eq_one_of_dvd_one (by simpa using Nat.dvd_gcd hd₁ hd₂))
  have hCB : C ≤ B := by
    simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using he
  exact (eq_of_le_of_card_ge hCB (by rw [hB, hC])).symm

omit [Finite G] in
private theorem conjNormal_ker (U : Subgroup G) [U.Normal] :
    (MulAut.conjNormal : G →* MulAut U).ker = centralizer (U : Set G) := by
  ext g
  constructor
  · intro hg u hu
    have he := congrArg (fun a : MulAut U => (a ⟨u, hu⟩ : G)) (MonoidHom.mem_ker.mp hg)
    change g * u * g⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    apply MonoidHom.mem_ker.mpr
    ext u
    change g * (u : G) * g⁻¹ = u
    rw [← hg u u.property, mul_inv_cancel_right]

private theorem eq_of_normal_four_core
    (X Y U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hsX : X.IsSubnormal) (hsY : Y.IsSubnormal)
    (hpX : IsPPerfect 2 X) (hpY : IsPPerfect 2 Y)
    (heX : X.pCoreIn 2 = U) (heY : Y.pCoreIn 2 = U)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3) : X = Y := by
  let Q := pCore 2 G
  let D := commutatorPreimage ⊤ Q U
  let f : G →* MulAut U := MulAut.conjNormal
  have hDX : X ≤ D := by
    apply le_commutatorPreimage le_top
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal X Q hsX hpX
      pCore_isPGroup le_normalizer_of_normal).trans
      ((map_mono (commutator_le_left _ _)).trans_eq heX)
  have hDY : Y ≤ D := by
    apply le_commutatorPreimage le_top
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal Y Q hsY hpY
      pCore_isPGroup le_normalizer_of_normal).trans
      ((map_mono (commutator_le_left _ _)).trans_eq heY)
  have hUQ : U ≤ Q := heX ▸ pCoreIn_le_of_subnormal 2 hsX
  have hfix : f.ker ⊓ D ≤ Q := by
    rw [show f.ker = centralizer (U : Set G) from conjNormal_ker U]
    exact two_layer_le_radical Q U Q (pCore_isPGroup.to_le hUQ)
      (pCore_quotient_pCore_eq_bot 2) (inf_le_right.trans hc)
  have hUker : U ≤ f.ker := by
    rw [show f.ker = centralizer (U : Set G) from conjNormal_ker U]
    exact le_centralizer U
  have hcard (B : Subgroup G) (hsB : B.IsSubnormal) (hDB : B ≤ D)
      (heB : B.pCoreIn 2 = U) (hqB : Nat.card (B ⧸ pCore 2 B) = 3) :
      Nat.card (B.map f) = 3 := by
    have hk : (f.subgroupMap B).ker = pCore 2 B := by
      rw [ker_subgroupMap]
      apply le_antisymm
      · rw [pCore_subnormal_eq_comap 2 hsB]
        intro b hb
        exact hfix ⟨hb, hDB b.property⟩
      · intro b hb
        exact hUker (heB ▸ mem_map_of_mem B.subtype hb)
    let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap B)
        (f.subgroupMap_surjective B))
    exact (Nat.card_congr e.toEquiv).symm.trans hqB
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hU, IsElementaryAbelian.exponent_eq_prime⟩
  have him : X.map f = Y.map f := three_subgroups_eq_of_card_six
    (IsKleinFour.card_mulAut U) _ _ (hcard X hsX hDX heX hqX)
      (hcard Y hsY hDY heY hqY)
  let q := QuotientGroup.mk' Q
  have hle : X.map q ≤ Y.map q := by
    rintro _ ⟨x, hx, rfl⟩
    have hfx : f x ∈ Y.map f := him ▸ mem_map_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := hfx
    have hxy : x / y ∈ Q := hfix ⟨by
      apply MonoidHom.mem_ker.mpr
      rw [map_div, hyx]
      exact div_self' _, D.div_mem (hDX hx) (hDY hy)⟩
    have he : q x = q y := QuotientGroup.eq_iff_div_mem.mpr hxy
    exact he ▸ mem_map_of_mem q hy
  apply eq_of_map_eq X Y hsX hsY hpX hpY
  exact eq_of_le_of_card_ge hle (by
    rw [(Nat.card_congr (coreQuotientEquiv X hsX).toEquiv).symm,
      (Nat.card_congr (coreQuotientEquiv Y hsY).toEquiv).symm, hqX, hqY])

/-- The source guard makes the normalizer of a shared cubic core characteristic two. -/
private theorem shared_core_normalizer_selfCentralizing
    (X : Subgroup G) (hX : IsBlock X)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3) (hG : BlockCommutationHypothesis G) :
    let N := upperTwoThreeCore G ⊓ normalizer (X.pCoreIn 2 : Set G)
    centralizer (pCore 2 N : Set N) ≤ pCore 2 N := by
  let H := upperTwoThreeCore G
  let U := X.pCoreIn 2
  let Q := pCore 2 G
  let N := H ⊓ normalizer (U : Set G)
  change centralizer (pCore 2 N : Set N) ≤ pCore 2 N
  have hQH : Q ≤ H := by
    intro q hq
    change (q : G ⧸ Q) ∈ pCore 3 (G ⧸ Q)
    rw [(QuotientGroup.eq_one_iff q).mpr hq]
    exact one_mem _
  let : H.Normal := inferInstanceAs
    ((pCore 3 (G ⧸ Q)).comap (QuotientGroup.mk' Q)).Normal
  have hHQ : H.pCoreIn 2 = Q := by
    rw [pCoreIn, pCore_subnormal_eq_comap 2 (inferInstance : H.Normal).isSubnormal]
    exact map_subgroupOf_eq_of_le hQH
  have hQU : Q ≤ centralizer (U : Set G) := by
    have hh := hX.core_centralizes_blockU
    rwa [← hX.short.core_eq_blockU_of_quotient_three hqX] at hh
  have hQN : Q ≤ N := le_inf hQH (hQU.trans (centralizer_le_normalizer _))
  have hR : Q.subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    rw [← hG.fitting_of_quotient_three hX hqX]
    exact centralizer_generalizedFitting_le H
  intro n hn
  have hnQ : (n : G) ∈ centralizer (Q : Set G) := by
    intro q hq
    exact congrArg Subtype.val (hn ⟨q, hQN hq⟩ (hR hq))
  have hnH : (n : G) ∈ H := n.property.1
  have hh : (⟨(n : G), hnH⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
    intro q hq
    apply Subtype.ext
    exact hnQ q (hHQ ▸ mem_map_of_mem H.subtype hq)
  have hnR : n ∈ Q.subgroupOf N := hHQ ▸ mem_map_of_mem H.subtype (hself hh)
  exact hR hnR

/-- Under C.1.9's guard, a cubic block is determined by its embedded two-core. -/
theorem cubic_blocks_eq_of_core_eq (X Y : Subgroup G)
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hG : BlockCommutationHypothesis G)
    (he : X.pCoreIn 2 = Y.pCoreIn 2) : X = Y := by
  let U := X.pCoreIn 2
  let N := upperTwoThreeCore G ⊓ normalizer (U : Set G)
  have hXU : X ≤ normalizer (U : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hYU : Y ≤ normalizer (U : Set G) := by
    change Y ≤ normalizer (X.pCoreIn 2 : Set G)
    rw [he]
    exact Y.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hXN : X ≤ N := le_inf (hX.le_upperTwoThreeCore_of_quotient_three hqX) hXU
  have hYN : Y ≤ N := le_inf (hY.le_upperTwoThreeCore_of_quotient_three hqY) hYU
  have hUN : U ≤ N := (pCoreIn_le 2 X).trans hXN
  let V := U.subgroupOf N
  let : V.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (U : Set G) from inf_le_right)
  let : IsElementaryAbelian 2 (pCore 2 X) := by
    rw [hX.short.core_eq_blockU_of_quotient_three hqX]
    exact hX.short.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map X.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hUN
  have hV : Nat.card V = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv]
    exact (card_map_of_injective X.subtype_injective).trans
      (hX.short.core_card_four_of_quotient_three hqX)
  have hcores (B : Subgroup G) (hBN : B ≤ N) (hBU : B.pCoreIn 2 = U) :
      (B.subgroupOf N).pCoreIn 2 = V := by
    apply map_injective N.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ _ N.subtype_injective,
      map_subgroupOf_eq_of_le hBN, hBU, map_subgroupOf_eq_of_le hUN]
  have hquot (B : Subgroup G) (hBN : B ≤ N)
      (hqB : Nat.card (B ⧸ pCore 2 B) = 3) :
      Nat.card (B.subgroupOf N ⧸ pCore 2 (B.subgroupOf N)) = 3 := by
    let e := subgroupOfEquivOfLe hBN
    let eq := QuotientGroup.congr (pCore 2 (B.subgroupOf N)) (pCore 2 B) e
      (pCore_map_iso 2 e)
    exact (Nat.card_congr eq.toEquiv).trans hqB
  have hlocal := eq_of_normal_four_core (X.subgroupOf N) (Y.subgroupOf N) V hV
    (shared_core_normalizer_selfCentralizing X hX hqX hG)
    hX.subnormal.subgroupOf hY.subnormal.subgroupOf
    (hX.short.twoPerfect.of_surjective (subgroupOfEquivOfLe hXN).symm.toMonoidHom
      (subgroupOfEquivOfLe hXN).symm.surjective)
    (hY.short.twoPerfect.of_surjective (subgroupOfEquivOfLe hYN).symm.toMonoidHom
      (subgroupOfEquivOfLe hYN).symm.surjective)
    (hcores X hXN rfl) (hcores Y hYN he.symm) (hquot X hXN hqX) (hquot Y hYN hqY)
  have hh := congrArg (Subgroup.map N.subtype) hlocal
  simpa only [map_subgroupOf_eq_of_le hXN, map_subgroupOf_eq_of_le hYN] using hh

/-- Distinct mutually normalizing cubic blocks commute under the exact source guard. -/
theorem cubic_blocks_commute_of_normalizes (X Y : Subgroup G)
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hG : BlockCommutationHypothesis G) (hne : X ≠ Y)
    (hnX : Y ≤ normalizer X) (hnY : X ≤ normalizer Y) : ⁅X, Y⁆ = ⊥ := by
  rcases cubic_normalizing_dichotomy X Y hX hY hqX hqY hnX hnY with hc | hc
  · exact hc
  · exact (hne (cubic_blocks_eq_of_core_eq X Y hX hY hqX hqY hG hc.2)).elim

end CFSG.Quasithin.ChapterC.BlockCommutation
