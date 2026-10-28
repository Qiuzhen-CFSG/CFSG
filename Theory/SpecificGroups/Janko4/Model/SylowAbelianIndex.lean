module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.NormalClosure
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Mathlib.GroupTheory.IndexNormal

/-!
# The full J₄ Sylow has no abelian subgroup of index at most two

The actual max2 seed normal closure is extraspecial of order 2¹³. Its
certified center and central quotient give this order without enumerating
J₄. Embed that seed into the model, choose a containing Sylow, and conjugate
it into the supplied Sylow. An abelian subgroup of index at most two would
restrict to such a subgroup of the extraspecial seed, which is impossible.

This is the Sylow obstruction for the solvable whole-actor argument in
Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf. The imported
literal normal-closure certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Janko4
attribute [local irreducible] modelGroup matrixA matrixB
private theorem extraspecial_no_abelian_index_le_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : 8 < Nat.card P) (A : Subgroup P) (hi : A.index ≤ 2) :
    ¬ IsMulCommutative A := by
  intro hab
  have hp : 0 < A.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  by_cases htwo : A.index = 2
  · let : A.Normal := normal_of_index_eq_two htwo
    have hcard : Nat.card (P ⧸ A) = 2 := htwo
    let : IsCyclic (P ⧸ A) := isCyclic_of_prime_card hcard
    have hZ : center P ≤ A := by
      rw [←IsExtraspecial.commutator_eq_center (p := 2)]
      exact Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    exact IsExtraspecial.not_isMulCommutative_of_index_two hP A htwo hZ hab
  · have ht : A = ⊤ := index_eq_one.mp (by omega)
    have habP : IsMulCommutative P := isMulCommutative_iff.mpr (by
      intro x y
      exact congrArg Subtype.val (isMulCommutative_iff.mp hab
        ⟨x,ht ▸ mem_top x⟩ ⟨y,ht ▸ mem_top y⟩))
    let : Nontrivial (P ⧸ center P) := IsExtraspecial.quotient_nontrivial 2 P
    exact QuotientGroup.nontrivial_iff.mp inferInstance (center_eq_top_iff.mpr habP)

open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData
open TwoCoreComparison.CoordinateGenerators.Realization

private theorem seed_card : Nat.card localNormalClosure = 2^13 := by
  have hc := (center localNormalClosure).card_mul_index
  have hq : (center localNormalClosure).index = 2^12 := by
    rw [index_eq_card,Nat.card_congr normalClosureCentralCoordinates.toEquiv]
    simp [Nat.card_eq_fintype_card]
  rw [normalClosure_center_card,hq] at hc
  exact hc.symm

/-- Every full Sylow two-subgroup of the actual J₄ model has no abelian
subgroup of index at most two. -/
theorem sylow_no_abelian_index_le_two (S : Sylow 2 Model)
    (A : Subgroup S) (hi : A.index ≤ 2) : ¬ IsMulCommutative A := by
  let : IsExtraspecial 2 localNormalClosure := normalClosure_extraspecial
  let f : localNormalClosure →* Model :=
    centralizerToModel.comp (localSubgroup.subtype.comp localNormalClosure.subtype)
  have hf : Function.Injective f := centralizerToModel_injective.comp
    (localSubgroup.subtype_injective.comp localNormalClosure.subtype_injective)
  have hp : IsPGroup 2 f.range := (IsExtraspecial.isPGroup 2 localNormalClosure).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model P S
  let j : localNormalClosure →* S :=
    ((MulAut.conj g).toMonoidHom.comp f).codRestrict _ (by
      intro x
      have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hP (show f x ∈ f.range from ⟨x,rfl⟩))
      exact (congrArg Sylow.toSubgroup hg) ▸ hh)
  have hj : Function.Injective j := by
    intro x y he
    apply hf
    apply (MulAut.conj g).injective
    exact congrArg Subtype.val he
  let B := A.comap j
  have hBi : B.index ≤ 2 := by
    rw [show B.index = A.relIndex j.range from A.index_comap j]
    exact (relIndex_le_of_le_right (show j.range ≤ ⊤ from le_top)
      (by simpa using (Subgroup.FiniteIndex.index_ne_zero (H := A)))).trans
      (by simpa using hi)
  intro hab
  let := hab
  have hB : IsMulCommutative B := A.comap_injective_isMulCommutative hj
  exact extraspecial_no_abelian_index_le_two (by rw [seed_card]; norm_num) B hBi hB
end Janko4
