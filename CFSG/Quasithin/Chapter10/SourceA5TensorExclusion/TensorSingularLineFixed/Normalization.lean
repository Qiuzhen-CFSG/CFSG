module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorInnerWeakClosure.Subspaces
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorThompsonActor
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.SingularLine
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# The invariant singular line normalizes the conjugate module

The actual binary tensor-normalizer action supplies a singular coefficient
line with a fixed kernel of index at most two. For an actor of corank at
most one in a conjugate module, this kernel has corank at most two.
The global-rank centralizer criterion therefore places the literal line
in the normalizer of that conjugate module.

This is the first source transport in Aschbacher–Smith 9.4.5, printed p.737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem tensor_singular_line_normalizes (hr : 3 < globalR D.fullModule)
    (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAM : A ≤ D.maximalLocal)
    (d : Binary.NormalizerSingularLineData
      (m.maximalNormalizerAction.comp (inclusion hAM))) :
    m.tensorCoordinateSubgroup d.line ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G) := by
  let W := D.fullModule.map (MulAut.conj g).toMonoidHom
  let K := d.kernel.map A.subtype
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hKA : K ≤ A := map_subtype_le _
  have hi : K.relIndex A ≤ 2 := by
    change (K.subgroupOf A).index ≤ 2
    rw [show K.subgroupOf A = d.kernel from
      comap_map_eq_self_of_injective A.subtype_injective d.kernel]
    exact d.index_le_two
  have hcA : subgroupCorank A K ≤ 1 := by
    change Nat.log 2 (K.relIndex A) ≤ 1
    exact (Nat.log_mono_right hi).trans (by decide)
  have hcW : subgroupCorank W K ≤ 2 := by
    rw [offender_corank_add hKA hAW]
    omega
  have hrW : 3 < globalR W := by
    rw [globalR_map_equiv]
    exact hr
  have hCN : centralizer (K : Set G) ≤ normalizer (W : Set G) :=
    centralizer_le_normalizer_of_corank_lt_globalR (hKA.trans hAW)
      ((show (subgroupCorank W K : ℕ∞) ≤ 3 by exact_mod_cast hcW.trans (by decide)).trans_lt hrW)
  apply le_trans (le_centralizer_iff.mp ?_) hCN
  rintro a ⟨b,hb,rfl⟩
  apply m.tensorCoordinateSubgroup_fixed d.line ⟨b,hAM b.property⟩
  intro v hv
  have hh := d.fixed b hb v hv
  change normalizerRepresentation Binary.action
    (m.maximalNormalizerAction ⟨b,hAM b.property⟩) v = v at hh
  rwa [m.maximalNormalizerAction_apply] at hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
