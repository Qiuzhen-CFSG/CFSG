module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.LocalReduction

/-!
# Local branches for elementary J₄ pairs

The three proposed overgroups are actual subgroups of the binary matrix
carrier: the specified max1, the centralizer of the first standard
involution, and the specified max4. Coverage by their conjugates and
absorption of elementary pairs from the first two remain separate proof
obligations. In particular, the max1 quotient isomorphism by itself does
not establish absorption.

The transport lemma below moves the entire pair through an inner
automorphism. It retains the ambient Sylow witness and every `PairInput`
clause, including setwise permutability. Composing the two conjugators
gives an actual ambient max4 conjugate containing the original pair.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), citing Aschbacher, *Overgroups of
Sylow subgroups in sporadic groups* (1986). The proposed three local types
are the first, second and fourth entries of the ATLAS J₄ maximal-subgroup
list, https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/ . This module does not
assert that the list covers the elementary normalizers or identify a
word-generated subgroup with the full involution centralizer.

The elementary normalizer is proper: otherwise simplicity makes A the
whole group, contradicting the certified noncommutation of the standard
generators. It therefore lies in a maximal proper subgroup, whose order
is divisible by 2²¹ because it contains the specified two-subgroup. These
facts permit exclusions of proposed overgroups with insufficient two-part
without assuming the ambient order or the separate odd-index theorem.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

open Subgroup
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

attribute [local irreducible] Janko4.modelGroup max4Subgroup

/-- A nontrivial elementary normal subgroup would contradict simplicity
and the certified noncommutation of the two standard generators. -/
theorem fixedTwoElementaryNormalizer_ne_top [IsSimpleGroup Janko4.Model]
    {A : Subgroup Janko4.Model} (hA : FixedTwoElementaryNormalizer A) :
    normalizer (A : Set Janko4.Model) ≠ ⊤ := by
  intro htop
  have hAn : A.Normal := normalizer_eq_top_iff.mp htop
  have hAt : A = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal A hAn).resolve_left hA.ne_bot
  let _ : IsElementaryAbelian 2 (⊤ : Subgroup Janko4.Model) := hAt ▸ hA.elementary
  exact Janko4.a_mul_b_ne_b_mul_a (congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := (⊤ : Subgroup Janko4.Model))).comm
      ⟨Janko4.a, mem_top _⟩ ⟨Janko4.b, mem_top _⟩))

/-- Every overgroup of the normalizer contains the specified order-2²¹
subgroup. This uses its proved local order, not an ambient order formula. -/
theorem fixedTwoElementaryNormalizer_twoPart_dvd
    {A M : Subgroup Janko4.Model} (hA : FixedTwoElementaryNormalizer A)
    (hM : normalizer (A : Set Janko4.Model) ≤ M) : 2 ^ 21 ∣ Nat.card M := by
  have hc := card_dvd_of_le (hA.normalized.trans hM)
  rwa [twoSubgroup_card] at hc

/-- Maximal-subgroup calculations may be restricted to proper overgroups
whose order is divisible by the full, already certified two-part. -/
theorem fixedTwoElementaryNormalizer_le_maximal
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
    {A : Subgroup Janko4.Model} (hA : FixedTwoElementaryNormalizer A) :
    ∃ M : Subgroup Janko4.Model, IsCoatom M ∧
      normalizer (A : Set Janko4.Model) ≤ M ∧ 2 ^ 21 ∣ Nat.card M := by
  obtain ⟨M, hM, hAM⟩ :=
    (eq_top_or_exists_le_coatom (normalizer (A : Set Janko4.Model))).resolve_left
      (fixedTwoElementaryNormalizer_ne_top hA)
  exact ⟨M, hM, hAM, fixedTwoElementaryNormalizer_twoPart_dvd hA hAM⟩

/-- Absorption of source elementary pairs lying in one specified subgroup.
The containments do not assert that either member normalizes the other. -/
def ElementaryLocalAbsorption (L : Subgroup Janko4.Model) : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model), PairInput S R →
      IsElementaryAbelian 3 R → Nat.card R = 3 ^ 2 →
      (S : Subgroup Janko4.Model) ≤ L → R ≤ L →
      ∃ g : Janko4.Model,
        (S : Subgroup Janko4.Model) ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom ∧
        R ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- The remaining elementary-pair calculation inside the literal max1 carrier. -/
abbrev ElementaryMathieuAbsorption : Prop :=
  ElementaryLocalAbsorption
    (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- The remaining elementary-pair calculation inside the full ambient
centralizer of the certified standard involution. -/
abbrev ElementaryInvolutionAbsorption : Prop :=
  ElementaryLocalAbsorption (centralizer ({Janko4.a} : Set Janko4.Model))

/-- A proposed exhaustive cover of the fixed Sylow's maximal elementary
normalizers. Each alternative specifies an actual ambient subgroup.
This incidence assertion is an unproved prerequisite, not an ATLAS tag. -/
def FixedTwoElementaryNormalizerCover : Prop :=
  ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model), (S : Subgroup Janko4.Model) = twoSubgroup →
    ∀ A : Subgroup Janko4.Model, FixedTwoElementaryNormalizer A →
      ∃ g : Janko4.Model,
        normalizer (A : Set Janko4.Model) ≤
            (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
              Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom ∨
        normalizer (A : Set Janko4.Model) ≤
            (centralizer ({Janko4.a} : Set Janko4.Model)).map
              (MulAut.conj g).toMonoidHom ∨
        normalizer (A : Set Janko4.Model) ≤
            max4Subgroup.map (MulAut.conj g).toMonoidHom

/-- Absorption in a fixed local subgroup also absorbs pairs in its ambient
conjugates. The proof transports, rather than strengthens, permutability. -/
theorem elementaryLocalAbsorption_of_conjugate
    {L : Subgroup Janko4.Model} (hL : ElementaryLocalAbsorption L)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model) (h : PairInput S R)
    (hE : IsElementaryAbelian 3 R) (hcard : Nat.card R = 3 ^ 2)
    (g : Janko4.Model)
    (hS : (S : Subgroup Janko4.Model) ≤ L.map (MulAut.conj g).toMonoidHom)
    (hR : R ≤ L.map (MulAut.conj g).toMonoidHom) :
    ∃ k : Janko4.Model,
      (S : Subgroup Janko4.Model) ≤ max4Subgroup.map (MulAut.conj k).toMonoidHom ∧
      R ≤ max4Subgroup.map (MulAut.conj k).toMonoidHom := by
  let e := MulAut.conj g
  let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let R' := R.map e.symm.toMonoidHom
  have hp : PairInput S' R' := pairInput_map e.symm h
  let _ := hE
  have hE' : IsElementaryAbelian 3 R' := IsElementaryAbelian.map e.symm.toMonoidHom
  have hc' : Nat.card R' = 3 ^ 2 :=
    (Nat.card_congr (e.symm.subgroupMap R).toEquiv).symm.trans hcard
  have hS' : (S' : Subgroup Janko4.Model) ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hS hy
    change e.symm (e z) ∈ L
    simpa only [MulEquiv.symm_apply_apply, SetLike.mem_coe] using hz
  have hR' : R' ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hR hy
    change e.symm (e z) ∈ L
    simpa only [MulEquiv.symm_apply_apply, SetLike.mem_coe] using hz
  obtain ⟨k, hkS, hkR⟩ := hL S' R' hp hE' hc' hS' hR'
  have hcomp : e.toMonoidHom.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (g * k)).toMonoidHom := by
    ext x
    simp [e, mul_assoc]
  have back (K : Subgroup Janko4.Model)
      (hK : K.map e.symm.toMonoidHom ≤ max4Subgroup.map (MulAut.conj k).toMonoidHom) :
      K ≤ max4Subgroup.map (MulAut.conj (g * k)).toMonoidHom := by
    intro x hx
    have hm : e (e.symm x) ∈
        (max4Subgroup.map (MulAut.conj k).toMonoidHom).map e.toMonoidHom :=
      mem_map_of_mem e.toMonoidHom
      (hK (mem_map_of_mem e.symm.toMonoidHom hx))
    rw [map_map, hcomp, e.apply_symm_apply] at hm
    exact hm
  exact ⟨g * k, back S.toSubgroup hkS, back R hkR⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
