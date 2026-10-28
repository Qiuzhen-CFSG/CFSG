module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Bridges to the smaller-model section calculations

The linear target is the actual PSL₃(4) matrix quotient. Its established
higher-rank simplicity and perfectness provide the hypotheses of the
independent proper-section calculation. Its whole-group simple quotients
are isomorphic to itself, so that calculation suffices for all sections.
The degree-eight permutation calculation restricts to degree seven by
extending each permutation to fix the eighth letter.

These bridges do not prove either outstanding subgroup classification.
Source obligation: condition K in Aschbacher–Smith, Theorem 0.1.2(4),
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
open CFSG.KnownSimple

public noncomputable section

theorem linearTarget_model : ClassicalGroup.IsPSL LinearTarget 3 4 :=
  ⟨GaloisField 2 2, inferInstance, inferInstance,
    GaloisField.card 2 2 (by decide), ⟨MulEquiv.refl _⟩⟩

theorem linearTarget_isSimpleGroup : IsSimpleGroup LinearTarget :=
  Atlas.psl_simple_high_rank 3 (by decide)

theorem linearTarget_not_isMulCommutative : ¬ IsMulCommutative LinearTarget := by
  let : Group.IsPerfect LinearTarget := Atlas.psl_perfect 3 (by decide)
  exact Group.IsPerfect.not_isMulCommutative LinearTarget

theorem linearTarget_constructed : IsConstructedCarrier LinearTarget := by
  apply IsConstructedCarrier.classical
  apply IsClassicalModel.linear 3 4 _ linearTarget_model
  refine ⟨?_, by decide, by omega⟩
  exact (isPrimePow_nat_iff 4).mpr ⟨2, 2, by decide, by decide, by decide⟩

theorem linearTarget_isKGroup_of_properK
    (h : HasProperKSubgroups IsConstructedCarrier LinearTarget) :
    IsKGroup IsConstructedCarrier LinearTarget := by
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let : IsSimpleGroup LinearTarget := linearTarget_isSimpleGroup
    let : IsSimpleGroup (⊤ : Subgroup LinearTarget) := Subgroup.topEquiv.isSimpleGroup
    let e : (⊤ : Subgroup LinearTarget) ≃* S :=
      MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf, hf⟩
    exact linearTarget_constructed.of_mulEquiv (e.symm.trans Subgroup.topEquiv)
  · let t : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
    exact h U hU S hS ⊤ (f.comp t.toMonoidHom) (hf.comp t.surjective)

theorem permutationTarget_isKGroup_of_symmetricEight
    (h : IsKGroup IsConstructedCarrier (Equiv.Perm (Fin 8))) :
    IsKGroup IsConstructedCarrier PermutationTarget :=
  h.of_injective (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (show 7 ≤ 8 by decide)))
    (Equiv.Perm.viaEmbeddingHom_injective _)

end
end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
