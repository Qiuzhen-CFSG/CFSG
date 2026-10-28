module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorSingularLineFixed.Normalization
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorConjugateSingularCommutator

/-!
# The original actor fixes its singular coefficient line

The invariant singular coefficient line normalizes the conjugate module
by its small-index action kernel. Its commutators with the actor remain
inside that same singular subgroup of order four. The source singular
commutator theorem makes this action trivial, retaining the exact line
and vector supplied by the full binary-normalizer geometry.

Source: Aschbacher–Smith 9.4.5, printed pp.736–737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual actor fixes every vector of its chosen singular coefficient line. -/
theorem tensor_singular_line_fixed (hr : 3 < globalR D.fullModule)
    (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAM : A ≤ D.maximalLocal)
    (d : Binary.NormalizerSingularLineData
      (m.maximalNormalizerAction.comp (inclusion hAM))) :
    ∀ (a : A) (v : Binary.V), v ∈ d.line →
      ((m.maximalNormalizerAction.comp (inclusion hAM)) a).val.val v = v := by
  have hCV := m.tensorCoordinateSubgroup_le d.line
  have hCN := m.tensor_singular_line_normalizes hr g hAW hcor hAM d
  have hcard : Nat.card (m.tensorCoordinateSubgroup d.line) ≤ 4 := by
    rw [m.card_tensorCoordinateSubgroup,d.line_card]
  have hsing (s : m.tensorCoordinateSubgroup d.line) :
      ((m.sectionData.coordinates ⟨s,hCV s.property⟩).toAdd).det = 0 :=
    d.line_singular _ ((m.mem_tensorCoordinateSubgroup d.line _).mp s.property)
  have hcomm : ⁅m.tensorCoordinateSubgroup d.line,A⁆ ≤ m.tensorCoordinateSubgroup d.line := by
    rw [commutator_comm]
    apply m.tensorCoordinateSubgroup_commutator hAM
    intro a v hv
    have hh := d.moved a v hv
    change normalizerRepresentation Binary.action
      (m.maximalNormalizerAction ⟨a,hAM a.property⟩) v - v ∈ d.line at hh
    rwa [m.maximalNormalizerAction_apply] at hh
  have hc := m.tensor_commutator_eq_bot_of_singular_image g hAW hcor
    hCV hCN hCV hcard hsing hcomm
  intro a u hu
  obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd u)
  have hv' : (m.sectionData.coordinates v).toAdd = u := congrArg Multiplicative.toAdd hv
  have hvC : (v : G) ∈ m.tensorCoordinateSubgroup d.line :=
    (m.mem_tensorCoordinateSubgroup d.line v).mpr (hv' ▸ hu)
  have hh := (commutator_eq_bot_iff_le_centralizer.mp hc) hvC a a.property
  have he := m.maximalAction_coordinates ⟨a,hAM a.property⟩ v
  have hvfix : D.fullModule.normalizerMonoidHom
      ⟨(a : G),D.maximalLocal_normalizes_fullModule (hAM a.property)⟩ v = v := by
    apply Subtype.ext
    change (a : G) * (v : G) * (a : G)⁻¹ = v
    rw [hh,mul_inv_cancel_right]
  rw [hvfix,hv'] at he
  change normalizerRepresentation Binary.action
    (m.maximalNormalizerAction ⟨a,hAM a.property⟩) u = u
  rw [m.maximalNormalizerAction_apply]
  exact he

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
