module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry.Standard.Coordinates
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
/-!
# The action-compatible symmetric-six model of inverse-transpose fixed points

Every standard binary dot-product isometry fixes the canonical norm-one vector.
The explicit coordinates from `Standard.Coordinates` therefore restrict it to
an isometry of the alternating four-space. Conversely, the designated polar
representation of S₆ extends by fixing the canonical line. The existing
`symmetricSixEquiv` identifies its image with the actual matrix group Sp₄(2),
so restriction and extension give inverse group equivalences. The theorem
`fixedSpEquiv_action` records their compatibility on every vector.

For the transposition `(0 1)`, the duad table gives the exact formula
`v ↦ v + polarForm (polarVector 0) v • polarVector 0`. Extending this formula
supplies a nonzero direction and a nonzero functional on the original five-space,
with the functional vanishing on that direction. Conjugacy of transpositions
then supplies the transvection clause for every swap.

This proves the standard fixed-model obligation in the degree-five calculation
used in Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265),
`refs/quasithin.pdf`. It is independent of the Gram-normalization argument for
general outer involutions.
-/

@[expose] public section

open Matrix
open BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricSix
namespace BinaryLinear.SixSylowActors.Five.Standard
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable def polarLinearEquiv (σ : S6) : NaturalModule ≃ₗ[ZMod 2] NaturalModule where
  __ := polarLinearMap σ
  invFun := polarAction σ⁻¹
  left_inv v := by
    change polarAction σ⁻¹ (polarAction σ v) = v
    rw [← polarAction_mul, inv_mul_cancel, polarAction_one]
  right_inv v := by
    change polarAction σ (polarAction σ⁻¹ v) = v
    rw [← polarAction_mul, mul_inv_cancel, polarAction_one]

/-- Extend the designated polar action by the identity on the canonical line. -/
noncomputable def extension : S6 →* LinearGroup 5 where
  toFun σ := coordinates.symm.trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr (polarLinearEquiv σ)).trans coordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨a, w⟩, rfl⟩ := coordinates.surjective v
    simp [LinearEquiv.trans_apply, polarLinearEquiv, polarLinearMap, polarAction_one]
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨a, w⟩, rfl⟩ := coordinates.surjective v
    simp [LinearEquiv.trans_apply, polarLinearEquiv, polarLinearMap, polarAction_mul]

theorem extension_coordinates (σ : S6) (a : ZMod 2) (v : NaturalModule) :
    extension σ (coordinates (a, v)) = coordinates (a, polarAction σ v) := by
  simp [extension, LinearEquiv.trans_apply, polarLinearEquiv, polarLinearMap]

theorem extension_fixed (σ : S6) : extension σ ∈ (graphLinear 5).fixedSubgroup := by
  apply (fixed_iff_form _).mpr
  intro x y
  obtain ⟨⟨a, v⟩, rfl⟩ := coordinates.surjective x
  obtain ⟨⟨b, w⟩, rfl⟩ := coordinates.surjective y
  rw [extension_coordinates, extension_coordinates, coordinates_form, coordinates_form,
    polarAction_form]

noncomputable def fixedExtension : S6 →* (graphLinear 5).fixedSubgroup :=
  extension.codRestrict _ extension_fixed

theorem extension_injective : Function.Injective extension := by
  intro σ τ h
  apply polarRepresentation_injective
  apply Subtype.ext
  change (polarLinearMap σ).toMatrix' = (polarLinearMap τ).toMatrix'
  congr 1
  apply LinearMap.ext
  intro v
  have hh := congrArg (fun g : LinearGroup 5 => g (coordinates (0, v))) h
  rw [extension_coordinates, extension_coordinates] at hh
  exact congrArg Prod.snd (coordinates.injective hh)

noncomputable def conjugated (g : (graphLinear 5).fixedSubgroup) :
    SplitSpace ≃ₗ[ZMod 2] SplitSpace :=
  coordinates.trans (g.val.trans coordinates.symm)

theorem conjugated_form (g : (graphLinear 5).fixedSubgroup) (x y : SplitSpace) :
    (conjugated g x).1 * (conjugated g y).1 +
      polarForm (conjugated g x).2 (conjugated g y).2 =
    x.1 * y.1 + polarForm x.2 y.2 := by
  rw [← coordinates_form, ← coordinates_form]
  simpa [conjugated, LinearEquiv.trans_apply] using
    (fixed_iff_form g.val).mp g.property (coordinates x) (coordinates y)

theorem conjugated_one_zero (g : (graphLinear 5).fixedSubgroup) :
    conjugated g (1, 0) = (1, 0) := by
  apply coordinates.injective
  simpa [conjugated, LinearEquiv.trans_apply, coordinates_one_zero] using fixed_canonical g

theorem conjugated_fst (g : (graphLinear 5).fixedSubgroup) (x : SplitSpace) :
    (conjugated g x).1 = x.1 := by
  have h := conjugated_form g (1, 0) x
  rw [conjugated_one_zero] at h
  simpa using h

noncomputable def restriction (g : (graphLinear 5).fixedSubgroup) :
    NaturalModule →ₗ[ZMod 2] NaturalModule :=
  (LinearMap.snd (ZMod 2) (ZMod 2) NaturalModule).comp
    ((conjugated g).toLinearMap.comp (LinearMap.inr (ZMod 2) (ZMod 2) NaturalModule))

theorem conjugated_apply (g : (graphLinear 5).fixedSubgroup) (a : ZMod 2)
    (v : NaturalModule) : conjugated g (a, v) = (a, restriction g v) := by
  have hs : conjugated g (a, 0) = (a, 0) := by
    have h := congrArg (fun x : SplitSpace => a • x) (conjugated_one_zero g)
    simpa only [← map_smul, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using h
  have hv : conjugated g (0, v) = (0, restriction g v) :=
    Prod.ext (conjugated_fst g (0, v)) rfl
  have he : (a, v) = (a, (0 : NaturalModule)) + (0, v) := by simp
  rw [he, map_add, hs, hv]
  simp

theorem restriction_form (g : (graphLinear 5).fixedSubgroup) (v w : NaturalModule) :
    polarForm (restriction g v) (restriction g w) = polarForm v w := by
  have h := conjugated_form g (0, v) (0, w)
  simpa only [conjugated_apply, zero_mul, zero_add] using h

/-- The actual symplectic matrix induced on the canonical orthogonal complement. -/
noncomputable def restrictionSp (g : (graphLinear 5).fixedSubgroup) :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  ⟨(restriction g).toMatrix', by
    rw [SymplecticGroup.mem_iff']
    have hf : polarForm.comp (restriction g) (restriction g) = polarForm := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact restriction_form g v w
    have hm := congrArg LinearMap.BilinForm.toMatrix' hf
    rw [LinearMap.BilinForm.toMatrix'_comp] at hm
    simpa only [polarForm, LinearMap.BilinForm.toMatrix'_toBilin'] using hm⟩

theorem fixedExtension_surjective : Function.Surjective fixedExtension := by
  intro g
  obtain ⟨σ, hσ⟩ := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.surjective
    (restrictionSp g)
  have he (v : NaturalModule) : polarAction σ v = restriction g v := by
    rw [← polarRepresentation_apply]
    rw [Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply] at hσ
    rw [hσ]
    exact LinearMap.toMatrix'_mulVec (restriction g) v
  refine ⟨σ, Subtype.ext ?_⟩
  apply LinearEquiv.ext
  intro x
  obtain ⟨⟨a, v⟩, rfl⟩ := coordinates.surjective x
  change extension σ (coordinates (a, v)) = g.val (coordinates (a, v))
  rw [extension_coordinates, he]
  have h := congrArg coordinates (conjugated_apply g a v)
  simpa only [conjugated, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using h.symm

/-- The inverse of the required fixed-group model, with its concrete action retained. -/
noncomputable def fixedEquiv : S6 ≃* (graphLinear 5).fixedSubgroup :=
  MulEquiv.ofBijective fixedExtension
    ⟨fun _ _ h => extension_injective (congrArg Subtype.val h), fixedExtension_surjective⟩

theorem restriction_extension (σ : S6) (v : NaturalModule) :
    restriction (fixedExtension σ) v = polarAction σ v := by
  change (coordinates.symm (extension σ (coordinates (0, v)))).2 = _
  rw [extension_coordinates, coordinates.symm_apply_apply]

theorem restrictionSp_extension (σ : S6) :
    restrictionSp (fixedExtension σ) = polarRepresentation σ := by
  apply Subtype.ext
  change (restriction (fixedExtension σ)).toMatrix' = (polarLinearMap σ).toMatrix'
  congr 1
  apply LinearMap.ext
  exact restriction_extension σ

/-- Restriction identifies the fixed subgroup with the actual binary symplectic group. -/
noncomputable def fixedSpEquiv : (graphLinear 5).fixedSubgroup ≃*
    Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  fixedEquiv.symm.trans Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv

/-- The equivalence is the restriction matrix, rather than an abstract identification. -/
theorem fixedSpEquiv_apply (g : (graphLinear 5).fixedSubgroup) :
    fixedSpEquiv g = restrictionSp g := by
  obtain ⟨σ, rfl⟩ := fixedEquiv.surjective g
  change Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
    (fixedEquiv.symm (fixedEquiv σ)) = _
  rw [fixedEquiv.symm_apply_apply,
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
  exact (restrictionSp_extension σ).symm

/-- Restriction and extension preserve the natural action on the original five-space. -/
theorem fixedSpEquiv_action (g : (graphLinear 5).fixedSubgroup)
    (a : ZMod 2) (v : NaturalModule) :
    g.val (coordinates (a, v)) = coordinates (a, (fixedSpEquiv g).val *ᵥ v) := by
  rw [fixedSpEquiv_apply]
  change _ = coordinates (a, (restriction g).toMatrix' *ᵥ v)
  rw [LinearMap.toMatrix'_mulVec]
  simpa only [conjugated, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] using
    congrArg coordinates (conjugated_apply g a v)

private theorem swap_table (d e : Duad)
    (h : duadSet e = (duadSet d).image (Equiv.swap (0 : Letter) 1)) :
    (polarVector e).val = (polarVector d).val +
      polarForm (polarVector 0).val (polarVector d).val • (polarVector 0).val := by
  decide +revert

/-- A transposition acts as a rank-one symplectic transvection. -/
theorem polarAction_swap (v : NaturalModule) :
    polarAction (Equiv.swap (0 : Letter) 1) v =
      v + polarForm (polarVector 0).val v • (polarVector 0).val := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hv⟩
  have hdv : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← hdv, polarAction_vector]
  exact swap_table d _ (duadSet_smul _ d)

def swapDirection : Space 5 := coordinates (0, (polarVector 0).val)

def swapForm : Space 5 →ₗ[ZMod 2] ZMod 2 :=
  (polarForm (polarVector 0).val).comp
    ((LinearMap.snd (ZMod 2) (ZMod 2) NaturalModule).comp coordinates.symm.toLinearMap)

theorem swapForm_coordinates (a : ZMod 2) (v : NaturalModule) :
    swapForm (coordinates (a, v)) = polarForm (polarVector 0).val v := by
  simp [swapForm]

theorem swapDirection_ne_zero : swapDirection ≠ 0 := by decide

theorem swapForm_ne_zero : swapForm ≠ 0 := by
  intro h
  have hh := congrArg (fun f : Space 5 →ₗ[ZMod 2] ZMod 2 =>
    f (coordinates (0, (polarVector 1).val))) h
  rw [swapForm_coordinates] at hh
  exact (by decide : polarForm (polarVector 0).val (polarVector 1).val ≠ 0) hh

theorem swapForm_direction : swapForm swapDirection = 0 := by
  rw [swapDirection, swapForm_coordinates]
  exact polarForm_alt _

theorem extension_swap_isTransvection :
    IsTransvection (extension (Equiv.swap (0 : Letter) 1)) := by
  refine ⟨swapDirection, swapForm, swapDirection_ne_zero, swapForm_ne_zero,
    swapForm_direction, ?_⟩
  apply LinearEquiv.ext
  intro x
  obtain ⟨⟨a, v⟩, rfl⟩ := coordinates.surjective x
  change extension _ (coordinates (a, v)) =
    coordinates (a, v) + swapForm (coordinates (a, v)) • swapDirection
  rw [extension_coordinates, polarAction_swap, swapForm_coordinates,
    swapDirection, ← map_smul, ← map_add]
  congr 1
  simp

theorem extension_isTransvection (σ : S6) (hσ : σ.IsSwap) :
    IsTransvection (extension σ) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (0 : Letter) ≠ 1) hab)
  have ht := isTransvection_map_linear (by decide : 2 ≤ 5)
    (MulAut.conj (extension τ)) (extension (Equiv.swap (0 : Letter) 1))
  have h := ht.mpr extension_swap_isTransvection
  have he : MulAut.conj (extension τ) (extension (Equiv.swap (0 : Letter) 1)) =
      extension (Equiv.swap a b) := by
    change extension τ * extension (Equiv.swap (0 : Letter) 1) * (extension τ)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, hτ]
  exact he ▸ h

end BinaryLinear.SixSylowActors.Five.Standard

namespace BinaryLinear.SixSylowActors.Five

/-- Ordinary inverse transpose has the compatible S₆ fixed model, including the
actual transvection witnesses for the inverse images of all swaps. -/
theorem graph_fixedModel : Nonempty (FixedModel (graphLinear 5)) := by
  refine ⟨⟨Standard.fixedEquiv.symm, ?_⟩⟩
  intro σ hσ
  exact Standard.extension_isTransvection σ hσ

end BinaryLinear.SixSylowActors.Five
