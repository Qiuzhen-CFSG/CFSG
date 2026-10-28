module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer.Generators
public import Theory.Alternating.theorem_5_2_1_2
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# An embedded S₈ in the symmetric outer HS centralizer

The seven checked permutations satisfy the type-A₇ Coxeter relations.
The proved Coxeter presentation of S₈ produces a homomorphism. A nontrivial
kernel would contain A₈ and kill the product of the first two adjacent
transpositions, contrary to the checked permutation calculation.

Source: Aschbacher–Smith 16.1.5(10), p.1172; GLS3 Table 5.3m, class 2D.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
open Sporadic.LeechRelated.HS
open GLS3.Chapter5.SchurPresentation
open Subgroup

local notation "C" => permutationCentralizer symmetricPermutation

/-- The concrete adjacent transpositions as elements of the actual centralizer. -/
def centralizerGenerator (i : Fin 7) : C :=
  ⟨⟨generator i, generator_mem i⟩, mem_centralizer_singleton_iff.mpr (generator_commutes i).symm⟩

private theorem centralizerGenerator_relations :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A 7) centralizerGenerator := by
  intro i j
  apply Subtype.ext
  apply Subtype.ext
  exact generator_relations i j

private def coxeterHom : TypeACoxeterGroup 3 →* C :=
  (CoxeterMatrix.A 7).toCoxeterSystem.lift
    ⟨centralizerGenerator, centralizerGenerator_relations⟩

private noncomputable def coxeterEquiv : TypeACoxeterGroup 3 ≃* S8 :=
  MulEquiv.ofBijective (typeACoxeterPermutationProjection 3)
    ⟨typeACoxeterPermutationProjection_injective 3,
      typeACoxeterPermutationProjection_surjective 3⟩

/-- The homomorphism from the genuine symmetric group to the specified centralizer. -/
noncomputable def embedding : S8 →* C := by
  exact coxeterHom.comp coxeterEquiv.symm.toMonoidHom

private theorem embedding_adjacent (i : Fin 7) :
    embedding (adjacentSwap 3 i) = centralizerGenerator i := by
  rw [← typeACoxeterPermutationProjection_simple 3 i]
  change coxeterHom (coxeterEquiv.symm
    (coxeterEquiv ((CoxeterMatrix.A 7).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A 7).toCoxeterSystem.lift_apply_simple
    centralizerGenerator_relations i

/-- The representation is faithful, since its kernel cannot contain A₈. -/
theorem embedding_injective : Function.Injective embedding := by
  apply (MonoidHom.ker_eq_bot_iff embedding).mp
  by_contra h
  have hn : Nontrivial embedding.ker := (Subgroup.nontrivial_iff_ne_bot embedding.ker).mpr h
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 8)) hn
  have hm : adjacentSwap 3 0 * adjacentSwap 3 1 ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [adjacentSwap]
  have hz := hA hm
  change embedding (adjacentSwap 3 0 * adjacentSwap 3 1) = 1 at hz
  rw [map_mul, embedding_adjacent, embedding_adjacent] at hz
  exact generator_product_ne_one
    (congrArg (fun g : C => (g.val.val : Equiv.Perm (Fin 100))) hz)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.SymmetricCentralizer
