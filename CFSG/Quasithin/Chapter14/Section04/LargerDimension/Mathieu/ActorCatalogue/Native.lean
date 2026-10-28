module
public import Theory.Representation.Mathieu.M22James.Model
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Native carrier and point marking for the Mathieu branch

The model is the literal binary matrix group `TwoCoreLinearModel.actionGroup`.
Its normal component is the published genuine M₂₂ triple cover, and the
restriction of its column action is exactly that cover's binary representation.
The matrix centralizer and quotient-automorphism coverage identify the full
normalizer of the component with this model. The explicit outer involution
then proves index two and identifies every faithful matrix-marked proper
extension of the component, with the matrix action retained.

The point-centralizer transport uses an actual equivariant linear marking.
It concerns a binary vector, as required for Vtilde₂ in 14.4.12; it does not
identify the stabilizer of the entire associated F₄-point with that centralizer.
The native point-centralizer structure and residual catalogue are separate
calculations.

Source: Aschbacher--Smith, 14.4.2(6) and 14.4.12, printed pp.1006 and
1011--1012; H.12.1, printed pp.393--394 (1 March 2004 manuscript).
The imported ATLAS matrices, their attribution and source hashes are retained
in the original `TwoCoreNormalizer/LinearModel/source/` directory. No new
finite computation or recognition from equal orders is used here.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Sporadic.Mathieu
open scoped Matrix
abbrev Model := actionGroup
abbrev Space := M22TripleCover.BinarySpace
noncomputable def action : Representation (ZMod 2) Model Space :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom Matrix12).comp actionGroup.subtype)

theorem action_apply (g : Model) (v : Space) : action g v = (g.val : Matrix12) *ᵥ v := rfl

theorem action_faithful : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLinAlgEquiv'.injective he

def component : Subgroup Model := derivedGroup.subgroupOf actionGroup

def componentInclusion : M22TripleCover →* Model := inclusion derivedGroup_le_actionGroup

theorem action_component (g : M22TripleCover) :
    action (componentInclusion g) = M22TripleCover.binaryRepresentation g := rfl

instance component_normal : component.Normal :=
  normal_subgroupOf_of_le_normalizer (actionGroup.le_normalizer.trans
    normalizer_actionGroup_le_normalizer_derivedGroup)

/-- Every binary matrix normalizing the actual triple cover belongs to the
published outer extension. This is a matrix comparison, not order recognition. -/
theorem component_matrix_normalizer : normalizer (derivedGroup : Set Matrix12ˣ) = actionGroup := by
  apply le_antisymm ?_ (actionGroup.le_normalizer.trans
    normalizer_actionGroup_le_normalizer_derivedGroup)
  intro g hg
  let n : normalizer (derivedGroup : Set Matrix12ˣ) := ⟨g, hg⟩
  obtain ⟨h, hh⟩ := derivedQuotientConjugation_surjective
    (quotientAut (center derivedGroup) (derivedGroup.normalizerMonoidHom n))
  have he : derivedConjugation h = derivedGroup.normalizerMonoidHom n :=
    MulAut.quotient_center_injective hh
  have hk : (toDerivedNormalizer h)⁻¹ * n ∈ derivedGroup.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (derivedConjugation h)⁻¹ * derivedGroup.normalizerMonoidHom n = 1
    rw [he, inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hc : (h : Matrix12ˣ)⁻¹ * g ∈ actionGroup := centralizer_derivedGroup_le hk
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using actionGroup.mul_mem h.property hc

/-- The source involution in the explicit outer extension. -/
def outerInvolution : Model := ⟨unitC, unitC_mem_actionGroup⟩

theorem outerInvolution_sq : outerInvolution ^ 2 = 1 := Subtype.ext unitC_pow_two

theorem outerInvolution_not_mem : outerInvolution ∉ component := by
  intro hc
  have hcomm := congrArg Subtype.val
    (mem_center_iff.mp coreScalar_mem_center (⟨unitC, hc⟩ : derivedGroup))
  change unitC * scalarUnit = scalarUnit * unitC at hcomm
  have hfix : unitC * scalarUnit * unitC⁻¹ = scalarUnit := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [unitC_conj_scalarUnit] at hfix
  apply scalarUnit_ne_one
  apply mul_left_cancel (a := scalarUnit)
  simpa only [pow_two, mul_one] using hfix

/-- The component together with the literal outer involution generates Model. -/
theorem component_sup_outer : component ⊔ zpowers outerInvolution = ⊤ := by
  apply map_injective actionGroup.subtype_injective
  rw [Subgroup.map_sup, component, map_subgroupOf_eq_of_le derivedGroup_le_actionGroup,
    MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm (sup_le derivedGroup_le_actionGroup (zpowers_le.mpr unitC_mem_actionGroup))
  change closure {unitC, unitD} ≤ _
  rw [closure_le]
  have hc : unitC ∈ derivedGroup ⊔ zpowers unitC :=
    (show zpowers unitC ≤ derivedGroup ⊔ zpowers unitC from le_sup_right) (mem_zpowers unitC)
  have ha : unitC * unitD ∈ derivedGroup ⊔ zpowers unitC :=
    (show derivedGroup ≤ derivedGroup ⊔ zpowers unitC from le_sup_left) coreA_mem_derivedGroup
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hc
  · change unitD ∈ (derivedGroup ⊔ zpowers unitC : Subgroup Matrix12ˣ)
    have hh : unitC⁻¹ * (unitC * unitD) ∈ (derivedGroup ⊔ zpowers unitC : Subgroup Matrix12ˣ) :=
      (derivedGroup ⊔ zpowers unitC).mul_mem ((derivedGroup ⊔ zpowers unitC).inv_mem hc) ha
    simpa only [inv_mul_cancel_left] using hh

/-- The component has index two in the concrete outer extension. -/
theorem component_index : component.index = 2 := by
  have hd : component.index ∣ 2 := by
    have hi := component.relIndex_dvd_card (zpowers outerInvolution)
    rw [← relIndex_sup_left, component_sup_outer, relIndex_top_right] at hi
    exact hi.trans (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one outerInvolution_sq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · have ht : component = ⊤ := index_eq_one.mp h
    exact (outerInvolution_not_mem (ht ▸ mem_top _)).elim
  · exact h

/-- Any subgroup properly containing the component is the full outer extension. -/
theorem eq_top_of_component_lt (K : Subgroup Model) (hK : component < K) : K = ⊤ := by
  have hi := index_strictAnti hK
  rw [component_index] at hi
  exact index_eq_one.mp (by have hp := K.index_ne_zero_of_finite; omega)

/-- Any actual matrix action whose normal component is the published triple
cover has image inside the correct native outer-extension carrier. -/
theorem range_le_model {Q : Type*} [Group Q] (L : Subgroup Q) [L.Normal]
    (f : Q →* Matrix12ˣ) (hL : L.map f = derivedGroup) : f.range ≤ actionGroup := by
  rw [← component_matrix_normalizer, ← hL]
  rintro y ⟨g, rfl⟩
  exact le_normalizer_map f (mem_map_of_mem f (by
    rw [normalizer_eq_top]
    trivial))

/-- A faithful matrix marking of the normal component and a proper outer
extension identifies the whole carrier with Model. No equality of orders is
used for the recognition. -/
theorem range_eq_model {Q : Type*} [Group Q] (L : Subgroup Q) [L.Normal]
    (f : Q →* Matrix12ˣ) (hf : Function.Injective f)
    (hL : L.map f = derivedGroup) (hproper : L ≠ ⊤) : f.range = actionGroup := by
  have hr := range_le_model L f hL
  let K := f.range.subgroupOf actionGroup
  have hCK : component ≤ K := by
    intro x hx
    exact (hL ▸ map_le_range f L) hx
  have hne : component ≠ K := by
    intro he
    apply hproper
    apply top_unique
    intro g _
    have hg : (⟨f g, hr ⟨g, rfl⟩⟩ : Model) ∈ K := ⟨g, rfl⟩
    rw [← he] at hg
    change f g ∈ derivedGroup at hg
    rw [← hL] at hg
    obtain ⟨l, hl, hlg⟩ := mem_map.mp hg
    exact hf hlg ▸ hl
  have htop := eq_top_of_component_lt K (lt_of_le_of_ne hCK hne)
  have hm := congrArg (map actionGroup.subtype) htop
  rw [map_subgroupOf_eq_of_le hr, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The actual isomorphism to the native carrier supplied by that matrix action. -/
noncomputable def equivOfMatrixComponent {Q : Type*} [Group Q]
    (L : Subgroup Q) [L.Normal] (f : Q →* Matrix12ˣ) (hf : Function.Injective f)
    (hL : L.map f = derivedGroup) (hproper : L ≠ ⊤) : Q ≃* Model :=
  (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (range_eq_model L f hf hL hproper))

theorem equivOfMatrixComponent_apply {Q : Type*} [Group Q]
    (L : Subgroup Q) [L.Normal] (f : Q →* Matrix12ˣ) (hf : Function.Injective f)
    (hL : L.map f = derivedGroup) (hproper : L ≠ ⊤) (g : Q) :
    (equivOfMatrixComponent L f hf hL hproper g).val = f g := rfl

/-- The carrier comparison intertwines the literal twelve-dimensional matrix
action, including the outer element. -/
theorem equivOfMatrixComponent_action {Q : Type*} [Group Q]
    (L : Subgroup Q) [L.Normal] (f : Q →* Matrix12ˣ) (hf : Function.Injective f)
    (hL : L.map f = derivedGroup) (hproper : L ≠ ⊤) (g : Q) (v : Space) :
    action (equivOfMatrixComponent L f hf hL hproper g) v = (f g : Matrix12) *ᵥ v := by
  rw [action_apply, equivOfMatrixComponent_apply]

/-- The subgroup fixing a specified vector in an actual linear action. -/
def vectorStabilizer {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (v : V) : Subgroup Q where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change ρ a⁻¹ v = v
    have he : ρ a⁻¹ (ρ a v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at he

/-- The actual point centralizer in the native outer-extension module. -/
noncomputable def pointCentralizer (v : Space) : Subgroup Model := vectorStabilizer action v

/-- An equivariant marking carries the literal point centralizer to its
native counterpart. The marking is an input; it is not replaced by a dimension
or an equality of group orders. -/
theorem pointCentralizer_transport {Q V : Type*} [Group Q]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (e : Q ≃* Model) (a : V ≃ₗ[ZMod 2] Space)
    (ha : ∀ g v, a (ρ g v) = action (e g) (a v)) (v : V) :
    (vectorStabilizer ρ v).map e.toMonoidHom = pointCentralizer (a v) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change action (e x) (a v) = a v
    rw [← ha, hx]
  · intro hg
    refine mem_map.mpr ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    change ρ (e.symm g) v = v
    apply a.injective
    rw [ha, e.apply_symm_apply]
    exact hg

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
