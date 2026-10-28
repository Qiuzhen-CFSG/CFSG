module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour.Rows
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoFour.Adequate

/-!
# J₄ in the odd-characteristic and sporadic preliminary table

Full abstract innerness comes from the completed actual max1/centralizer
amalgam generation and rigidity proof. In the inherited simple/perfect source
context, the center is trivial. An involutory inner automorphism therefore
has a genuine order-two representative, to which exhaustive marked fusion
and the two exact full-centralizer calculations apply.

This assembles Aschbacher–Smith 16.1.5(9), printed p.1172, including the plus
type and the full 3.M₂₂.2 quotient, and excludes components as needed in
16.1.7. The marked row companions in `Rows` are independent of the global
innerness argument and feed 16.5.6(4). Full innerness also proves 16.1.6 for
arbitrary two-elements, including the identity, without a power reduction.
The source carrier is the original 112-dimensional binary Janko4.Model.
-/

public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
open Subgroup Theory.GroupTheory Janko4 Janko4.InvolutionCentralizers Sporadic.Mathieu

variable [IsSimpleGroup Model] [Group.IsPerfect Model]

/-- Full innerness on the actual matrix carrier, supplied by the proved amalgam assembly. -/
theorem automorphism_inner (r : MulAut Model) : ∃ g : Model, r = MulAut.conj g := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels.jankoFour_conj_surjective r
  exact ⟨g, hg.symm⟩

/-- The innerness assertion of source 16.1.5(9). -/
theorem involutory_inner (r : MulAut Model) (_hr : orderOf r = 2) :
    ∃ g : Model, r = MulAut.conj g := automorphism_inner r

/-- Center triviality is discharged from the inherited simple/perfect context. -/
theorem center_eq_bot : center Model = ⊥ := Subgroup.center_eq_bot_of_simple_perfect

/-- The conjugating element really has order two. Before using the trivial center,
the square of an inner involution only places its representative's square in the center. -/
theorem involution_representative (r : MulAut Model) (hr : orderOf r = 2) :
    ∃ g : Model, orderOf g = 2 ∧ r = MulAut.conj g ∧
      r.fixedSubgroup = centralizer ({g} : Set Model) :=
  MulAut.inner_involution_representative center_eq_bot r hr (automorphism_inner r)

/-- The complete marked source table of 16.1.5(9), with genuine full fixed groups.
The first quotient is the actual matrix 3.M22.2 of `firstCoveringExtension`. -/
theorem involution_table (r : MulAut Model) (hr : orderOf r = 2) :
    ∃ g : Model, orderOf g = 2 ∧ r = MulAut.conj g ∧
      ((DoubleCoverCentralizer.TwoCentral g ∧ Nonempty (FirstRow r.fixedSubgroup)) ∨
        (¬ DoubleCoverCentralizer.TwoCentral g ∧ Nonempty (GroupExtension (BinaryElementary 11)
          r.fixedSubgroup (MulAut M22)))) := by
  classical
  obtain ⟨g, hg, rfl, _⟩ := involution_representative r hr
  refine ⟨g, hg, rfl, ?_⟩
  by_cases hc : DoubleCoverCentralizer.TwoCentral g
  · exact Or.inl ⟨hc, central_row_of_twoCentral hg hc⟩
  · exact Or.inr ⟨hc, noncentral_row_of_not_twoCentral hg hc⟩

/-- The ordinary-component exclusion required in 16.1.7. -/
theorem involution_fixed_no_component (r : MulAut Model) (hr : orderOf r = 2)
    (K : Subgroup r.fixedSubgroup) : ¬ IsComponent r.fixedSubgroup K := by
  obtain ⟨g, hg, rfl, _⟩ := involution_representative r hr
  exact inner_fixed_no_component g hg K

/-- Component exclusion with the subgroup retained in the original model. -/
theorem involution_fixed_no_componentIn (r : MulAut Model) (hr : orderOf r = 2)
    (K : Subgroup Model) : ¬ IsComponentIn K r.fixedSubgroup :=
  fun hK => involution_fixed_no_component r hr _ hK.2

/-- Source 16.1.6 for every two-power order, including the identity. -/
theorem sylow_centralizing_two_automorphisms :
    HasInnerSylowCentralizingTwoAutomorphisms Model := by
  intro r _ _ _ _
  exact automorphism_inner r

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoFour
