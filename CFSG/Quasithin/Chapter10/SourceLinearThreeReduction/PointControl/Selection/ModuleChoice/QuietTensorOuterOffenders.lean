module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFull
public import Theory.Representation.BinaryTensorThree.OuterOffenders

/-!
# The original tensor (F−1)-offenders lie in the component orbit

The full-automizer coordinates carry an elementary actor with fixed
codimension at most its rank plus one into the concrete tensor group.
H.4.10(3) places it in the tensor base. The original base-image equality
then lifts every element back through the same L₀ inclusion; faithfulness
of the ambient automizer proves equality of these actual actions.

This supplies the outer-involution exclusion used in 8.3.11, with no
quadratic-action or additional marking premise. It does not establish
r>3: recognition of the tensor base and the preceding ambient centralizer
arguments of 8.3.7--10 still need source proofs. Point-core containment,
both quiet tensor exclusions, and FixedSupportRowsAt/ModuleChoiceAt remain
with this selected-module owner; the named point-control owner retains
final assembly.
Source: Aschbacher--Smith H.4.10(3) and 8.3.11, printed pp.384,726.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The (F−1)-offenders in the actual ambient automizer lie in the image
of the original component orbit L₀. This is the H.4.10(3) input to 8.3.11,
with its action and centralizer kernel unchanged. -/
theorem quiet_tensor_near_offender_le_orbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    (A : Subgroup (Automizer D.fullModule)) (hA : IsElementaryTwo A)
    (hbound : fixedCodim (automizerRepresentation D.fullModule) A ≤ rank A + 1) :
    A ≤ inducedAutomizer D.fullModule (localOrbit T L) := by
  obtain ⟨f,hf⟩ := quiet_tensor_automizer_coordinates D hn e hbase
  let : IsElementaryAbelian 2 A := hA.2
  have hAf : IsElementaryTwo (A.map f.toMonoidHom) := by
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hz
    exact hA.1 ((map_eq_bot_iff_of_injective A f.injective).mp hz)
  have hcb := fixedCodim_map_equivariant (automizerRepresentation D.fullModule)
    BinaryTensorThree.action f.toMonoidHom e hf A
  have hb := BinaryTensorThree.near_offender_le_base (A.map f.toMonoidHom) hAf
    (by rw [←hcb,rank_map_injective _ f.injective]; exact hbound)
  intro a ha
  obtain ⟨x,hx⟩ := hb (mem_map_of_mem f.toMonoidHom ha)
  obtain ⟨l,hl,he⟩ := hbase.ge
    (show BinaryTensorThree.baseAction x ∈ BinaryTensorThree.baseAction.range from ⟨x,rfl⟩)
  let n : normalizer (D.fullModule : Set G) :=
    ⟨l,D.maximalLocal_normalizes_fullModule ((localOrbit T L).le_normalizer hl)⟩
  let b : Automizer D.fullModule := D.fullModule.normalizerMonoidHom.rangeRestrict n
  have hab : b = a := by
    apply f.injective
    apply BinaryTensorThree.action_faithful
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [←hf]
    have hh := quietTensorLinearAction_apply D e l v
    rw [he] at hh
    change e (Additive.ofMul (D.fullModule.normalizerMonoidHom n v.toMul)) = _
    rw [←hh]
    change BinaryTensorThree.action (BinaryTensorThree.baseEmbedding x) (e v) = _
    exact congrArg (fun g => BinaryTensorThree.action g (e v)) hx
  exact ⟨n,hl,hab⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
