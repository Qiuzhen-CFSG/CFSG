module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Field
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.FieldTransport

/-!
# The two literal actors in the middle-factor calculation

The computable field uses the same polynomial X² − X + 2 as the retained
witnesses. We check the two matrices in the antidiagonal special unitary
group and transport them through the proved Borel-preserving field comparison.
No generation or coset-table assertion is included in these definitions.

Source: `MiddleFactors/source/standard_flag_data.txt`; the calculation supports
Guralnick–Malle Proposition 4.3 and Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization

/-- The antidiagonal form over the existing polynomial-coordinate field. -/
def tableForm : HermitianForm 3 F25 where
  conj := F25.conjugation
  conj_involutive := F25.conjugation_involutive
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> decide
  form_nondegenerate := by decide

abbrev TableGroup := standardGroup tableForm
abbrev tableBorel : Subgroup TableGroup := standardBorel tableForm

/-- The retained entries are powers of the primitive polynomial root. -/
def tableActorMatrix : Fin 2 → Matrix (Fin 3) (Fin 3) F25 :=
  ![!![F25.omega, 0, 0; 0, F25.omega ^ 4, 0; 0, 0, F25.omega ^ 19],
    !![F25.omega ^ 13, F25.omega ^ 12, 1;
      F25.omega ^ 12, F25.omega ^ 12, 0; 1, 0, 0]]

theorem tableActorMatrix_det (j : Fin 2) : (tableActorMatrix j).det = 1 := by
  revert j
  decide +kernel

def tableLinearActor (j : Fin 2) : GL (Fin 3) F25 :=
  GeneralLinearGroup.mkOfDetNeZero (tableActorMatrix j)
    (by rw [tableActorMatrix_det]; exact one_ne_zero)

theorem tableLinearActor_mem (j : Fin 2) :
    tableLinearActor j ∈ (FormTransport.standardForm tableForm).specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · change (FormTransport.standardForm tableForm).conjTranspose (tableActorMatrix j) *
      (FormTransport.standardForm tableForm).form * tableActorMatrix j =
      (FormTransport.standardForm tableForm).form
    revert j
    decide +kernel
  · apply Units.ext
    exact tableActorMatrix_det j

/-- Actual elements, without an assertion that they generate. -/
def tableActor (j : Fin 2) : TableGroup := ⟨tableLinearActor j, tableLinearActor_mem j⟩

/-- One fixed comparison of the actual group and Borel pairs. -/
noncomputable def canonicalEquiv : TableGroup ≃* CanonicalGroup :=
  Classical.choose (borel_field_transport F25 tableForm F25.card F25.conjugation_eq_fifth)

theorem canonicalEquiv_borel (g : TableGroup) :
    canonicalEquiv g ∈ canonicalBorel ↔ g ∈ tableBorel :=
  Classical.choose_spec (borel_field_transport F25 tableForm F25.card F25.conjugation_eq_fifth) g

noncomputable def actor (j : Fin 2) : CanonicalGroup := canonicalEquiv (tableActor j)

/-- Transport generation, retaining the two specific actors. -/
theorem actor_generates_of_table
    (h : Subgroup.closure (Set.range tableActor) = ⊤) :
    Subgroup.closure (Set.range actor) = ⊤ := by
  have hr : Set.range actor = canonicalEquiv '' Set.range tableActor := by
    exact Set.range_comp canonicalEquiv tableActor
  rw [hr]
  change Subgroup.closure (canonicalEquiv.toMonoidHom '' Set.range tableActor) = ⊤
  rw [← MonoidHom.map_closure, h, Subgroup.map_top_of_surjective _ canonicalEquiv.surjective]

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
