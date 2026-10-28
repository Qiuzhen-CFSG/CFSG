module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Extraspecial.SignAction
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Extraspeciality of the literal octad kernel model

In the genuine shortened-Golay semidirect product, faithfulness forces a
central element's permutation part to be trivial. Complement transitivity
then leaves precisely the identity and the complementary-sixteen sign in
the center. The actual transvection action makes every square central, so
the central quotient is elementary abelian. Its nontriviality follows from
the previously proved order 512.

The monomial embedding sends the distinguished model sign to the literal
`complementSign`. Thus the center identification is also proved inside
`action.ker`, with its existing subgroup and quotient conventions.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(1)–(3), pp.132–133.
The final source fusion assembly remains in the separate consumer.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
open MathieuCode.CocodeOctad.Dynamics
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace KernelModel
/-- The distinguished complementary-sixteen sign in the actual semidirect product. -/
def centralSign : Model := SemidirectProduct.inl (Multiplicative.ofAdd complementWord)

lemma centralSign_ne_one : centralSign ≠ 1 := by
  intro h
  exact complementWord_ne_zero (congrArg (fun m : Model => m.left.toAdd) h)

lemma centralSign_sq : centralSign ^ 2 = 1 := by
  rw [centralSign, ← map_pow]
  apply congrArg SemidirectProduct.inl
  apply Multiplicative.toAdd.injective
  rw [pow_two]
  change complementWord + complementWord = 0
  exact signCode_add_self _

lemma centralSign_mem_center : centralSign ∈ Subgroup.center Model := by
  rw [Subgroup.mem_center_iff]
  intro m
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change m.left.toAdd + signCodeEquiv m.right complementWord = complementWord + m.left.toAdd
    rw [signCodeEquiv_complementWord, add_comm]
  · simp [centralSign]

lemma model_mem_center_iff (m : Model) :
    m ∈ Subgroup.center Model ↔ m = 1 ∨ m = centralSign := by
  constructor
  · intro hm
    have hr : m.right = 1 := by
      apply signCodeEquiv_faithful
      intro c
      have he := congrArg (fun x : Model => x.left.toAdd)
        (Subgroup.mem_center_iff.mp hm (SemidirectProduct.inl (Multiplicative.ofAdd c)))
      change c + m.left.toAdd = m.left.toAdd + signCodeEquiv m.right c at he
      rw [add_comm c] at he
      exact (add_left_cancel he).symm
    have hf : ∀ g : pointwise, signCodeEquiv g m.left.toAdd = m.left.toAdd := by
      intro g
      have he := congrArg (fun x : Model => x.left.toAdd)
        (Subgroup.mem_center_iff.mp hm (SemidirectProduct.inr g))
      change 0 + signCodeEquiv g m.left.toAdd = m.left.toAdd + signCodeEquiv m.right 0 at he
      simpa only [map_zero, zero_add, add_zero] using he
    rcases (signCode_fixed_iff m.left.toAdd).mp hf with h | h
    · left
      exact SemidirectProduct.ext (Multiplicative.toAdd.injective h) hr
    · right
      exact SemidirectProduct.ext (Multiplicative.toAdd.injective h) hr
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact centralSign_mem_center

lemma model_center_eq_zpowers : Subgroup.center Model = Subgroup.zpowers centralSign := by
  apply le_antisymm
  · intro m hm
    rcases (model_mem_center_iff m).mp hm with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr centralSign_mem_center

lemma model_center_card : Nat.card (Subgroup.center Model) = 2 := by
  rw [model_center_eq_zpowers, Nat.card_zpowers]
  exact orderOf_eq_prime centralSign_sq centralSign_ne_one

lemma model_sq_mem_center (m : Model) : m ^ 2 ∈ Subgroup.center Model := by
  have hr : (m ^ 2).right = 1 := by
    change (SemidirectProduct.rightHom : Model →* pointwise) (m ^ 2) = 1
    rw [map_pow]
    exact pointwise_sq m.right
  let b := signDual m.left.toAdd
    (octadTransvectionEquiv nativeOctad ((nativeEquiv.symm m.right)⁻¹)).toAdd.val
  have hl : (m ^ 2).left.toAdd = b • complementWord := by
    rw [pow_two]
    change m.left.toAdd + signCodeEquiv m.right m.left.toAdd = _
    rw [signCodeEquiv_transvection, ← add_assoc, signCode_add_self, zero_add]
  apply (model_mem_center_iff _).mpr
  rcases bit_cases b with h | h
  · left
    rw [h, zero_smul] at hl
    exact SemidirectProduct.ext (Multiplicative.toAdd.injective hl) hr
  · right
    rw [h, one_smul] at hl
    exact SemidirectProduct.ext (Multiplicative.toAdd.injective hl) hr

/-- The source extraspecial structure on the genuine sign/permutation kernel model. -/
theorem model_isExtraspecial : IsExtraspecial 2 Model := by
  have hs (q : Model ⧸ Subgroup.center Model) : q ^ 2 = 1 := by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Model) q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (m ^ 2)).mpr (model_sq_mem_center m)
  refine {
    center_order_p := model_center_card
    quotient_elementary_abelian := {
      toIsMulCommutative := ⟨⟨fun a b =>
        (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_iff_pow_eq_one.mpr (hs x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    quotient_nontrivial := ?_ }
  apply QuotientGroup.nontrivial_iff.mpr
  intro h
  have hc := model_center_card
  rw [h, Subgroup.card_top, model_card] at hc
  norm_num at hc

lemma kernelEquiv_centralSign :
    kernelEquiv centralSign = (⟨complementSign, complementSign_mem_kernel⟩ : action.ker) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [kernelEquiv_val]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [complementSign_apply]
  apply Subtype.ext
  funext i
  rw [monomialEmbedding_apply]
  change (if complementWord.val.val i = 0 then x.val i else -x.val i) =
    -(if (golayBasis 0).val i = 0 then x.val i else -x.val i)
  rw [complementWord_apply]
  rcases bit_cases ((golayBasis 0).val i) with h | h <;> simp [h, CharTwo.add_self_eq_zero]

end KernelModel

/-- The literal Leech octad kernel has precisely the complementary-sign center. -/
theorem kernel_center_eq_zpowers_complementSign :
    Subgroup.center action.ker =
      Subgroup.zpowers (⟨complementSign, complementSign_mem_kernel⟩ : action.ker) := by
  have hm : (Subgroup.center KernelModel.Model).map KernelModel.kernelEquiv.toMonoidHom =
      Subgroup.center action.ker := by
    ext k
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact (Subgroup.centerCongr KernelModel.kernelEquiv ⟨m, hm⟩).prop
    · intro hk
      exact ⟨KernelModel.kernelEquiv.symm k,
        (Subgroup.centerCongr KernelModel.kernelEquiv.symm ⟨k, hk⟩).prop,
        KernelModel.kernelEquiv.apply_symm_apply k⟩
  rw [← hm, KernelModel.model_center_eq_zpowers, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers KernelModel.kernelEquiv_centralSign

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
end
