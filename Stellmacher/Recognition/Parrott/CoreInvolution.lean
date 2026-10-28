module
public import Stellmacher.Recognition.Parrott.FusionOutsideDerived
public import Stellmacher.Recognition.Parrott.OmegaOrbit
public import Stellmacher.Recognition.Parrott.OmegaStabilizer
public import Theory.GroupTheory.ElementarySixteenSolvableTwoFive

/-!
# An involution outside the derived two-core

For a finite nonsolvable simple N₂ group satisfying Parrott's centralizer
hypotheses at z, the two-core J of H = C_G(z) has an involution outside J'.
All subgroups below are the actual subgroups and images in G.

Suppose all core involutions belong to the derived image E. Fusion outside
E supplies an outer involution y conjugate to z. The actual mapped omega
subgroup X = Ω₁(C_H(y)) is elementary of order sixteen. Its normalizer N
has N∩H of index five, and this intersection is a two-group. Conjugation
on X has kernel contained in N∩H, so its image K has order 2^n * 5.
The N₂ condition makes N, and hence K, solvable. On the other hand E has
order 32 and C_E(X) has order eight, so it supplies an elementary subgroup
of K of order four. The solvable automorphism-group bound excludes this.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 3, printed p.675. Local solvability replaces the source's GL(4,2)
subgroup exclusion without changing the desired involution conclusion.
-/

open Subgroup
namespace Stellmacher.Recognition

/-- Parrott's third lemma: the actual two-core contains an involution outside its derived image. -/
public theorem parrott_core_involution_outside_derived
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ a : G, a ∈ J.map H.subtype ∧ orderOf a = 2 ∧ a ∉ E := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change ∃ a : G, a ∈ J.map H.subtype ∧ orderOf a = 2 ∧ a ∉ E
  by_contra hnone
  have hcore (a : G) (ha : a ∈ J.map H.subtype) (ha2 : orderOf a = 2) : a ∈ E := by
    by_contra haE
    exact hnone ⟨a, ha, ha2, haE⟩
  obtain ⟨t, ht2, htH, htE, htconj⟩ := parrott_fusion_outside_derived hns hN z h
  let y : H := ⟨t, htH⟩
  have hy : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans ht2
  have hyJ : y ∉ J := fun hyJ => htE (hcore t (mem_map_of_mem H.subtype hyJ) ht2)
  let P := centralizer ({y} : Set H)
  let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
  let Z := E ⊓ centralizer ({(y : G)} : Set G)
  let N := normalizer (X : Set G)
  let T := H.subgroupOf N
  obtain ⟨hEcard, hZcard, hXcard, hEelem, hXelem, hzZ, hZX, _, hEN, hCX, _, _⟩ :=
    parrott_outer_omega_geometry z h hcore y hy hyJ
  change E ≤ N at hEN
  change E ⊓ centralizer (X : Set G) = Z at hCX
  let : IsElementaryAbelian 2 E := hEelem
  let : IsElementaryAbelian 2 X := hXelem
  have hzX : z ∈ X := hZX hzZ
  have hXne : X ≠ ⊥ := by
    intro hbot
    change Nat.card X = 16 at hXcard
    rw [hbot, card_bot] at hXcard
    omega
  let : Group.IsSolvable N := hN N ⟨X, hXne, IsElementaryAbelian.isPGroup 2 X, rfl⟩
  let f : N →* MulAut X := X.normalizerMonoidHom
  let K := f.range
  have hKsolv : Group.IsSolvable K := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hkerT : f.rangeRestrict.ker ≤ T := by
    intro a ha
    have hfa : f a = 1 := congrArg (fun k : K => (k : MulAut X)) ha
    have hca : a ∈ f.ker := hfa
    change a ∈ X.normalizerMonoidHom.ker at hca
    rw [normalizerMonoidHom_ker] at hca
    exact mem_centralizer_singleton_iff.mpr (hca z hzX).symm
  have hTp : IsPGroup 2 T := parrott_omega_normalizer_stabilizer_isPGroup z h hcore y hy hyJ
  have hTindex : T.index = 5 := parrott_omega_normalizer_index hN z h hcore y hy hyJ htconj
  obtain ⟨n, hn⟩ := (hTp.map f.rangeRestrict).exists_card_eq
  have hKcard : Nat.card K = 2 ^ n * 5 := by
    have hc := (T.map f.rangeRestrict).index_mul_card
    rw [T.index_map_eq f.rangeRestrict_surjective hkerT, hTindex, hn] at hc
    exact hc.symm.trans (Nat.mul_comm _ _)
  let EN := E.subgroupOf N
  let : IsElementaryAbelian 2 EN := IsElementaryAbelian.subgroupOf hEN
  let A : Subgroup K := EN.map f.rangeRestrict
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f.rangeRestrict
  let g : EN →* K := f.rangeRestrict.comp EN.subtype
  let embed : EN →* G := N.subtype.comp EN.subtype
  have hembed : Function.Injective embed := N.subtype_injective.comp EN.subtype_injective
  have hker (a : EN) : a ∈ g.ker ↔ ((a : N) : G) ∈ centralizer (X : Set G) := by
    change f.rangeRestrict (a : N) = 1 ↔ _
    rw [Subtype.ext_iff]
    change (a : N) ∈ X.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hkerMap : g.ker.map embed = Z := by
    rw [← hCX]
    apply le_antisymm
    · rintro a ⟨b, hb, rfl⟩
      exact ⟨b.property, (hker b).mp hb⟩
    · intro a ha
      let b : EN := ⟨⟨a, hEN ha.1⟩, ha.1⟩
      exact ⟨b, (hker b).mpr ha.2, rfl⟩
  have hgker : Nat.card g.ker = 8 := by
    have hc := card_map_of_injective (K := g.ker) (f := embed) hembed
    rw [hkerMap] at hc
    exact hc.symm.trans hZcard
  have hENcard : Nat.card EN = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hEcard
  have hgrange : g.range = A := by
    rw [MonoidHom.range_comp, range_subtype]
  have hAcard : Nat.card A = 4 := by
    have hc := g.ker.card_mul_index
    rw [index_ker, hgker, hgrange, hENcard] at hc
    omega
  have hbound := card_elementary_two_le_two_of_solvable_aut16_two_five hXcard K hKsolv hKcard A
  rw [hAcard] at hbound
  omega

end Stellmacher.Recognition
