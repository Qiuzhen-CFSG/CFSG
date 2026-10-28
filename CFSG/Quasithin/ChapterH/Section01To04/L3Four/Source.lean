module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.BinaryModels
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The genuine component input for H.4.7

The cover is SL₃(F) → PSL₃(F) ≃ F*(M) → M, with F*(M) defined as the join
of the Fitting subgroup and the layer. Faithfulness gives exactly the scalar
center as kernel. Surjective inflation preserves the irreducibility assumed
on F*(M), so the central-character and field-of-definition calculation applies
to the original space. It produces actual Schur-extension equivalences and
the exhaustive binary dimensions 9, 16 and 64.

Source: Aschbacher–Smith H.4.7, printed pp.382–383 of refs/quasithin.pdf.
These are preliminary conclusions; the involution bound and its tensor/field
equality characterization still require the displacement and descent steps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups
open Representation Representation.SL3.BinaryDefiningFactors Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SchurField SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable {F M V : Type*} [Field F] [Group M]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal central quotient followed by the supplied isomorphism to F*(M). -/
def componentCover (e : PSL(3,F) ≃* generalizedFitting M) : SL(3,F) →* M :=
  (generalizedFitting M).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(3,F))))

/-- The original binary action pulled back along the actual component cover. -/
def coverRep (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) : Representation (ZMod 2) SL(3,F) V :=
  ρ.comp (componentCover e)

instance coverRep_irreducible (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] : IsIrreducible (coverRep e ρ) :=
  (irreducible_comp_surjective_iff
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(3,F))))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (ρ.comp (generalizedFitting M).subtype)).mpr inferInstance

/-- Faithfulness retains exactly the central kernel, not a solvable residual. -/
theorem coverRep_ker (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) (hρ : Function.Injective ρ) :
    (coverRep e ρ).ker = Subgroup.center SL(3,F) := by
  ext g
  change ρ ((e (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) : generalizedFitting M) : M) = 1 ↔ _
  rw [← ρ.map_one, hρ.eq_iff]
  have he (x : PSL(3,F)) : ((e x : generalizedFitting M) : M) = 1 ↔ x = 1 := by
    constructor
    · intro h
      apply e.injective
      exact (Subtype.ext h).trans e.map_one.symm
    · rintro rfl
      simp
  rw [he]
  exact QuotientGroup.eq_one_iff g

private def root : SL(3,F) := ⟨!![1,1,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩

private theorem root_not_central : root (F := F) ∉ Subgroup.center SL(3,F) := by
  intro h
  obtain ⟨a,_,ha⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 1) ha
  simp [root, Matrix.scalar, Matrix.diagonal] at he

/-- The source action is nontrivial on its genuine PSL₃(4) component. -/
theorem coverRep_nontrivial (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) (hρ : Function.Injective ρ) :
    ∃ g, coverRep e ρ g ≠ 1 := by
  refine ⟨root, ?_⟩
  intro h
  have hh : root (F := F) ∈ (coverRep e ρ).ker := h
  rw [coverRep_ker e ρ hρ] at hh
  exact root_not_central hh

variable [Finite F] [CharP F 2] [FiniteDimensional (ZMod 2) V]

/-- The source hypotheses give the five actual Schur-extension models. -/
theorem source_word_model (hcard : Nat.card F = 4)
    (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ) :
    ∃ (ι : F →+* SplittingField (coverRep e ρ)) (b c : Factor), NontrivialPair b c ∧
      Nonempty ((extendScalars (SplittingField (coverRep e ρ)) (coverRep e ρ).endFieldRep).Equiv
        (wordRep ι [b,c])) ∧
      schurDegree 2 (coverRep e ρ) = (if b = c then 1 else 2) ∧
      Module.finrank (ZMod 2) V = (if b = c then 1 else 2) * wordDegree [b,c] :=
  exists_nontrivial_binary_pair_model (coverRep e ρ) hcard
    (le_of_eq (coverRep_ker e ρ hρ).symm) (coverRep_nontrivial e ρ hρ)

/-- Dimension alternatives under the literal generalized-Fitting hypothesis of H.4.7. -/
theorem source_dimension_cases (hcard : Nat.card F = 4)
    (e : PSL(3,F) ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ) :
    Module.finrank (ZMod 2) V = 9 ∨ Module.finrank (ZMod 2) V = 16 ∨
      Module.finrank (ZMod 2) V = 64 :=
  binary_dimension_cases (coverRep e ρ) hcard
    (le_of_eq (coverRep_ker e ρ hρ).symm) (coverRep_nontrivial e ρ hρ)

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
