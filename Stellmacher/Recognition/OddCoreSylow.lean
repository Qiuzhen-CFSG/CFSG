module
public import Stellmacher.Recognition.OddCoreComponentNormalizer
public import Theory.GroupTheory.ElementaryCommutingTwoGroup

/-!
# Sylow control of rank-three odd-core closures

Let S be a two-subgroup and let A be an elementary binary
subgroup of S of order at least eight. In an N₂ group, S normalizes
the odd-core closure of A. Moreover, so does the full normalizer of any
Q ≤ S containing an elementary subgroup of order at least eight.

For the second assertion choose such a subgroup B of Q. Conjugating B
by an element of N(Q) keeps it inside S. The normal four-group connects
A, B and the conjugate of B; constancy and naturality of the odd-core
closure then give the conclusion. No simplicity or nontriviality of the
closure is needed. The argument is GLS2, Lemmas 10.20–10.21, applied to
the completion from Section 22. Lemma 10.11 supplies the normal four-group
in S. The final two theorems specialize the resulting control to an
ambient Sylow two-subgroup. Source: `refs/KGroup/GLS2/ChapterC.tex`.
-/

namespace Stellmacher.Recognition

/-- A subgroup with a normal four-group normalizes the closure of each
rank-three elementary subgroup it contains. -/
public theorem le_normalizer_oddCoreClosure_of_normal_four
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A : Subgroup G) (E : Subgroup S) [E.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4) :
    S ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let _ : IsElementaryAbelian 2 (E.map S.subtype) := IsElementaryAbelian.map_subtype
  have hSE : S ≤ Subgroup.normalizer (E.map S.subtype : Set G) := by
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using E.le_normalizer_map S.subtype
  exact hSE.trans (normalizer_four_le_normalizer_closure_of_normalizes hN A
    (E.map S.subtype) hA
    (by simpa only [Subgroup.card_map_of_injective S.subtype_injective] using hE)
    (hAS.trans hSE))

/-- The full normalizer of any rank-three subgroup of S controls the
closure, provided S contains a normal four-group. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_normal_four
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A Q B : Subgroup G) (E : Subgroup S) [E.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hAS : A ≤ S) (hQS : Q ≤ S) (hBQ : B ≤ Q)
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have hAB := Subgroup.elementaryCommutingConnected_of_le_of_normal_four S A B E
    hA hB hE hAS (hBQ.trans hQS)
  rw [oddCoreClosure_eq_of_connected hN hAB]
  intro g hg
  let e := MulAut.conj g
  let _ : IsElementaryAbelian 2 (B.map e.toMonoidHom) :=
    IsElementaryAbelian.map e.toMonoidHom
  have hBgS : B.map e.toMonoidHom ≤ S := by
    have hQg : Q.map e.toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    exact ((Subgroup.map_mono hBQ).trans hQg.le).trans hQS
  have hBBg := Subgroup.elementaryCommutingConnected_of_le_of_normal_four S B
    (B.map e.toMonoidHom) E hB
    (by simpa only [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      using hB)
    hE (hBQ.trans hQS) hBgS
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure B).map e.toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN hBBg).symm

/-- A finite two-subgroup normalizes the odd-core closure of each
rank-three elementary subgroup it contains. -/
public theorem twoGroup_le_normalizer_oddCoreClosure
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A : Subgroup G) (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) :
    S ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let _ : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 8 ≤ Nat.card (A.subgroupOf S) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv]
  obtain ⟨E, hEn, hEe, hE⟩ :=
    hS.exists_normal_elementaryAbelian_four (A.subgroupOf S) hAScard
  let _ : E.Normal := hEn
  let _ : IsElementaryAbelian 2 E := hEe
  exact le_normalizer_oddCoreClosure_of_normal_four hN S A E hAS hA hE

/-- If Q lies in a two-subgroup S and contains a rank-three elementary
subgroup, its full normalizer controls the closure of any rank-three
elementary subgroup of S. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_le_twoGroup
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S A Q B : Subgroup G) (hS : IsPGroup 2 S)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hQS : Q ≤ S) (hBQ : B ≤ Q)
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let _ : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hAS
  have hAScard : 8 ≤ Nat.card (A.subgroupOf S) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv]
  obtain ⟨E, hEn, hEe, hE⟩ :=
    hS.exists_normal_elementaryAbelian_four (A.subgroupOf S) hAScard
  let _ : E.Normal := hEn
  let _ : IsElementaryAbelian 2 E := hEe
  exact normalizer_le_normalizer_oddCoreClosure_of_normal_four hN S A Q B E
    hAS hQS hBQ hA hB hE

/-- A Sylow two-subgroup normalizes the odd-core closure of each
rank-three elementary subgroup it contains. -/
public theorem sylow_le_normalizer_oddCoreClosure
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) :
    (S : Subgroup G) ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  twoGroup_le_normalizer_oddCoreClosure hN S A S.isPGroup' hAS hA

/-- If Q ≤ S contains a rank-three elementary subgroup and S is a Sylow
two-subgroup, the normalizer of Q normalizes the odd-core closure of every
rank-three elementary subgroup of S. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_le_sylow
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hQS : Q ≤ S) (hBQ : B ≤ Q)
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  normalizer_le_normalizer_oddCoreClosure_of_le_twoGroup hN S A Q B S.isPGroup'
    hAS hQS hBQ hA hB

end Stellmacher.Recognition
