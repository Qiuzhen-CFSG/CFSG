module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.OutsideSelection
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.OutsideSelection.SquareTransport
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.InvolutionGeometry
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Applying the selected conjugate-centralizer involution to the split geometry

A compatible equivalence from the unitriangular group to the flagged
Sylow subgroup, identifying its core with the actual point-parabolic
two-core, carries the selected involution to an outside involution of
the unitriangular model. The existing involution theorem then gives the
middle elementary sixteen and generation by x and [U,x].

The restriction of the same Sylow embedding gives an actual equivalence
of cores and intertwines their conjugation actions. Transport across
its central quotient proves a₂ for the original core action, using the
original embedded quaternion data. The ambient elementary Thompson
subgroup and the actual Sylow containment are retained in the conclusion.

The parent assembly supplies `CoreCoordinates`, the compatible Sylow
equivalence and its core identification, and the source identification
of g in P − H with the line-minus-point parabolic condition. These are
identification premises, not involution or elementary-generation premises.
The result selects one involution for every such g; it makes no claim
that every element of W^g − U has order two.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 12.8.9,
printed pp.852–853, and proof of 14.4.4, printed p.1007.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Two.SplitParabolic.OutsideSelection

local instance : Finite Block :=
  Finite.of_equiv (E3 × SL) SemidirectProduct.equivProd.symm

variable (e : Unitriangular.T ≃* standardSylow)
/-- The compatible subgroup is an actual Sylow two-subgroup of the block. -/
noncomputable def compatibleSylow : Sylow 2 Block := Sylow.ofCard standardSylow (by
  have hs : Nat.card standardSylow = 64 :=
    (Nat.card_congr e.toEquiv).symm.trans Unitriangular.card_T
  have hv : Nat.card E3 = 8 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [hs, SemidirectProduct.card, hv, card_SL]
  decide +kernel)

theorem coe_compatibleSylow : (compatibleSylow e : Subgroup Block) = standardSylow := rfl

def sylowEmbedding : Unitriangular.T →* Block := standardSylow.subtype.comp e.toMonoidHom

theorem sylowEmbedding_injective : Function.Injective (sylowEmbedding e) :=
  standardSylow.subtype_injective.comp e.injective

variable (he : Unitriangular.U.map (sylowEmbedding e) = U)

noncomputable def coreEquiv : Unitriangular.U ≃* U :=
  (Unitriangular.U.equivMapOfInjective (sylowEmbedding e) (sylowEmbedding_injective e)).trans
    (MulEquiv.subgroupCongr he)

theorem coreEquiv_apply (u : Unitriangular.U) :
    (coreEquiv e he u : Block) = sylowEmbedding e u := rfl

include he in
theorem embedding_normalizes (y : Unitriangular.T) : sylowEmbedding e y ∈ normalizer (U : Set Block) := by
  rw [← he]
  exact le_normalizer_map (sylowEmbedding e)
    ⟨y, by rw [Unitriangular.U.normalizer_eq_top]; trivial, rfl⟩

def selectedActor (y : Unitriangular.T) : MulAut U :=
  U.normalizerMonoidHom ⟨sylowEmbedding e y, embedding_normalizes e he y⟩

theorem core_action (y : Unitriangular.T) (u : Unitriangular.U) :
    coreEquiv e he (Unitriangular.U.normalizerMonoidHom
      ⟨y, by rw [Unitriangular.U.normalizer_eq_top]; trivial⟩ u) =
    selectedActor e he y (coreEquiv e he u) := by
  apply Subtype.ext
  change sylowEmbedding e (y * (u : Unitriangular.T) * y⁻¹) =
    sylowEmbedding e y * sylowEmbedding e u * (sylowEmbedding e y)⁻¹
  simp only [map_mul, map_inv]

include he in
theorem exists_selected_geometry (hc : CoreCoordinates)
    (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage)
    (d : QuaternionCentralProductData Unitriangular.U) :
    ∃ y : Unitriangular.T,
      sylowEmbedding e y = selected g ∧ y ∉ Unitriangular.U ∧ y^2=1 ∧
      sylowEmbedding e y ∈ X g ∧
      zpowers (sylowEmbedding e y) ⊔ ⁅U,zpowers (sylowEmbedding e y)⁆ =
        Unitriangular.A.map (sylowEmbedding e) ∧
      d.IsA2Action (Unitriangular.U.normalizerMonoidHom
        ⟨y, by rw [Unitriangular.U.normalizer_eq_top]; trivial⟩) := by
  let x : standardSylow := ⟨selected g, conjugate_le_sylow hc g hg (selected_mem hc g)⟩
  let y := e.symm x
  have hy : sylowEmbedding e y = selected g :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hu : y ∉ Unitriangular.U := by
    intro hu
    apply selected_not_mem hc g hg hp
    rw [← hy, ← he]
    exact mem_map_of_mem _ hu
  have h2 : y^2=1 := by
    apply (sylowEmbedding_injective e)
    rw [map_pow, hy, selected_square, map_one]
  have ha := Unitriangular.outside_involution_mem_middle y hu h2
  refine ⟨y,hy,hu,h2,hy ▸ selected_mem hc g,?_,
    Unitriangular.a2_of_mem_A_outside d y ha hu⟩
  rw [← he, ← MonoidHom.map_zpowers, ← map_commutator, ← Subgroup.map_sup,
    Unitriangular.generation_of_mem_A_outside y ha hu]


theorem sylowEmbedding_range : (sylowEmbedding e).range = standardSylow := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (e y).property
  · intro hx
    exact ⟨e.symm ⟨x,hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

theorem thompson_image : Stellmacher.elementaryAbelianMaxJ standardSylow =
    Unitriangular.A.map (sylowEmbedding e) := by
  rw [← sylowEmbedding_range e, MonoidHom.range_eq_map,
    Stellmacher.elementaryAbelianMaxJ_map_injective _ (sylowEmbedding_injective e),
    Unitriangular.thompson_eq]

include he in
/-- The selected element generates the actual elementary Thompson subgroup,
and its action on the actual first core has the a₂ square-quotient condition.
The two identifications are supplied by the compatible flagged model. -/
theorem selected_generation_and_a2 (hc : CoreCoordinates)
    (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage)
    (d : QuaternionCentralProductData U) :
    zpowers (selected g) ⊔ ⁅U,zpowers (selected g)⁆ =
      Stellmacher.elementaryAbelianMaxJ standardSylow ∧
    ∃ hn : selected g ∈ normalizer (U : Set Block),
      d.IsA2Action (U.normalizerMonoidHom ⟨selected g,hn⟩) := by
  let dP := d.map (coreEquiv e he).symm
  obtain ⟨y,hy,_hu,_h2,_hx,hgen,ha⟩ := exists_selected_geometry e he hc g hg hp dP
  have ha' : d.IsA2Action (selectedActor e he y) :=
    a2_transport dP d (coreEquiv e he) _ _ (core_action e he y) ha
  constructor
  · rw [← hy, thompson_image e]
    exact hgen
  · have hn := embedding_normalizes e he y
    refine ⟨hy ▸ hn, ?_⟩
    simpa only [selectedActor, hy] using ha'

include he in
/-- Complete selection in the split natural model, under the explicit
core and flagged Sylow identifications retained for the assembly owner. -/
theorem exists_outside_involution_with_geometry (hc : CoreCoordinates)
    (g : Block) (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage)
    (d : QuaternionCentralProductData U) :
    ∃ x : Block, x ∈ X g ∧ x ∉ U ∧ x ≠ 1 ∧ x^2=1 ∧ x ∈ (compatibleSylow e : Subgroup Block) ∧
      zpowers x ⊔ ⁅U,zpowers x⁆ = Stellmacher.elementaryAbelianMaxJ standardSylow ∧
      ∃ hn : x ∈ normalizer (U : Set Block),
        d.IsA2Action (U.normalizerMonoidHom ⟨x,hn⟩) := by
  obtain ⟨hgen,ha⟩ := selected_generation_and_a2 e he hc g hg hp d
  refine ⟨selected g, selected_mem hc g, selected_not_mem hc g hg hp, ?_,
    selected_square g, conjugate_le_sylow hc g hg (selected_mem hc g),hgen,ha⟩
  intro hh
  exact selected_not_mem hc g hg hp (hh ▸ U.one_mem)

end Matrix.PSL3Two.SplitParabolic.OutsideSelection
