module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.Affine
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules

/-!
# The actual block module of the binary affine group

The translations are exactly the two-core. Every vector is a displacement
for a linear automorphism, so the commutator layer U is all translations.
The natural action has no nonzero fixed vector, giving C_U(Affine) = 1.
The resulting quotient maps identify Affine/O₂ with SL and U/C_U with the
binary vector group, with the actual conjugation formula checked explicitly.

This supplies the intrinsic module calculation for the end-node blocks in
Aschbacher–Smith 2.3.9(7), printed pp.525–526, using C.1.7/C.1.12,
printed pp.123–124. No shortness or subnormal-subgroup classification is
assumed or concluded for an arbitrary subgroup of a local overgroup.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
open Subgroup ChapterC SemidirectProduct
open scoped commutatorElement

variable (d : ℕ)

def translations : Subgroup (Affine d) :=
  (rightHom : Affine d →* SL d).ker

instance translations_normal : (translations d).Normal :=
  inferInstanceAs (rightHom : Affine d →* SL d).ker.Normal

theorem range_inl_eq_translations :
    (inl : Multiplicative (Vector d) →* Affine d).range = translations d :=
  range_inl_eq_ker_rightHom

noncomputable def translationsEquiv : Multiplicative (Vector d) ≃* translations d :=
  (MonoidHom.ofInjective inl_injective).trans
    (MulEquiv.subgroupCongr (range_inl_eq_translations d))

theorem translationsEquiv_apply (v : Multiplicative (Vector d)) :
    (translationsEquiv d v : Affine d) = inl v := rfl

instance vector_elementary : IsElementaryAbelian 2 (Multiplicative (Vector d)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    apply Multiplicative.toAdd.injective
    ext i
    simp [pow_two, CharTwo.add_self_eq_zero]

instance translations_elementary : IsElementaryAbelian 2 (translations d) :=
  IsElementaryAbelian.of_surjective (translationsEquiv d).toMonoidHom
    (translationsEquiv d).surjective

theorem affine_twoCore_eq : pCore 2 (Affine d) = translations d := by
  have hSL : pCore 2 (SL d) = ⊥ := by
    apply (Subgroup.map_injective (f := (slEquivLinear d).toMonoidHom)
      (slEquivLinear d).injective)
    rw [pCore_map_iso, Subgroup.map_bot]
    exact BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot
  apply le_antisymm
  · let f : Affine d →* SL d := rightHom
    have hn : ((pCore 2 (Affine d)).map f).Normal :=
      Subgroup.Normal.map inferInstance f rightHom_surjective
    have hle : (pCore 2 (Affine d)).map f ≤ pCore 2 (SL d) :=
      le_sSup ⟨hn, pCore_isPGroup.map f⟩
    rw [hSL] at hle
    exact (Subgroup.map_eq_bot_iff (pCore 2 (Affine d))).mp (le_bot_iff.mp hle)
  · exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩

noncomputable def affineCoreQuotientEquiv :
    (Affine d ⧸ pCore 2 (Affine d)) ≃* SL d :=
  (QuotientGroup.quotientMulEquivOfEq (affine_twoCore_eq d)).trans
    (QuotientGroup.quotientKerEquivOfRightInverse rightHom inr rightHom_inr)

theorem affineCoreQuotientEquiv_mk (g : Affine d) :
    affineCoreQuotientEquiv d (QuotientGroup.mk' (pCore 2 (Affine d)) g) = g.right := rfl

theorem conjugate_inl (g : Affine d) (v : Multiplicative (Vector d)) :
    g * inl v * g⁻¹ = inl (naturalAction d g.right v) := by
  apply SemidirectProduct.ext
  · simp [mul_comm, mul_left_comm]
  · simp

private theorem natural_displacement (hd : 2 ≤ d) (w : Multiplicative (Vector d)) :
    ∃ (g : SL d) (v : Multiplicative (Vector d)), naturalAction d g v * v⁻¹ = w := by
  obtain ⟨g, v, hv⟩ := BinaryNaturalDual.VectorStabilizers.exists_natural_displacement
    (V := Vector d) (by simpa using hd) (Multiplicative.toAdd w)
  refine ⟨(slEquivLinear d).symm g, Multiplicative.ofAdd v, ?_⟩
  apply Multiplicative.toAdd.injective
  change Matrix.mulVec _ v + -v = _
  rw [← sub_eq_add_neg, ← slEquivLinear_apply]
  rwa [MulEquiv.apply_symm_apply]

theorem affine_blockU_eq (hd : 2 ≤ d) : blockU (Affine d) = translations d := by
  apply le_antisymm
  · rw [blockU, affine_twoCore_eq]
    exact commutator_le_left (translations d) ⊤
  · rw [← range_inl_eq_translations]
    rintro _ ⟨w, rfl⟩
    obtain ⟨g, v, rfl⟩ := natural_displacement d hd w
    have he : (inl (naturalAction d g v * v⁻¹) : Affine d) =
        ⁅(inr g : Affine d), inl v⁆ := by
      rw [map_mul, map_inv, inl_aut]
      simp only [commutatorElement_def, map_inv]
    rw [he, blockU, commutator_comm, affine_twoCore_eq]
    apply commutator_mem_commutator (mem_top _)
    change (inl v : Affine d).right = 1
    rfl

private theorem translation_fixed (hd : 2 ≤ d) (v : Multiplicative (Vector d))
    (hv : (inl v : Affine d) ∈ center (Affine d)) : v = 1 := by
  have hfix : ∀ g : BinaryLinear.GL (Vector d), g (Multiplicative.toAdd v) =
      Multiplicative.toAdd v := by
    intro g
    have hc := mem_center_iff.mp hv (inr ((slEquivLinear d).symm g))
    have he := congrArg SemidirectProduct.left hc
    simp only [mul_left, left_inr, right_inr, left_inl, right_inl, map_one,
      one_mul, mul_one] at he
    have he' := congrArg Multiplicative.toAdd he
    change slEquivLinear d ((slEquivLinear d).symm g) _ = _ at he'
    simpa only [MulEquiv.apply_symm_apply] using he'
  apply Multiplicative.toAdd.injective
  exact BinaryNaturalDual.VectorStabilizers.natural_fixed_eq_zero
    (by simpa using hd) hfix

theorem affine_blockFixed_eq_bot (hd : 2 ≤ d) : blockFixed (Affine d) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hxT : (x : Affine d) ∈ (inl : Multiplicative (Vector d) →* Affine d).range := by
    rw [range_inl_eq_translations, ← affine_blockU_eq d hd]
    exact x.property
  obtain ⟨v, hv⟩ := hxT
  have hc : (inl v : Affine d) ∈ center (Affine d) := hv.symm ▸ hx
  have hv1 := translation_fixed d hd v hc
  apply Subtype.ext
  change (x : Affine d) = 1
  rw [← hv, hv1, map_one]

noncomputable def affineBlockUEquiv (hd : 2 ≤ d) :
    blockU (Affine d) ≃* Multiplicative (Vector d) :=
  (MulEquiv.subgroupCongr (affine_blockU_eq d hd)).trans (translationsEquiv d).symm

theorem inl_affineBlockUEquiv (hd : 2 ≤ d) (u : blockU (Affine d)) :
    inl (affineBlockUEquiv d hd u) = (u : Affine d) := by
  exact congrArg Subtype.val ((translationsEquiv d).apply_symm_apply
    (MulEquiv.subgroupCongr (affine_blockU_eq d hd) u))

noncomputable def affineBlockModuleEquiv (hd : 2 ≤ d) :
    BlockModule (Affine d) ≃* Multiplicative (Vector d) :=
  ((QuotientGroup.quotientMulEquivOfEq (affine_blockFixed_eq_bot d hd)).trans
    (QuotientGroup.quotientBot)).trans (affineBlockUEquiv d hd)

theorem affineBlockModuleEquiv_mk (hd : 2 ≤ d) (u : blockU (Affine d)) :
    affineBlockModuleEquiv d hd (QuotientGroup.mk' (blockFixed (Affine d)) u) =
      affineBlockUEquiv d hd u := rfl

noncomputable def affineBlockModuleModel (hd : 2 ≤ d) :
    BlockModuleModel (Affine d) (naturalAction d) where
  quotientIso := affineCoreQuotientEquiv d
  moduleIso := affineBlockModuleEquiv d hd
  intertwining g u := by
    rw [affineBlockModuleEquiv_mk, affineCoreQuotientEquiv_mk,
      affineBlockModuleEquiv_mk]
    apply inl_injective (φ := naturalAction d)
    rw [inl_affineBlockUEquiv, ← conjugate_inl, inl_affineBlockUEquiv]
    rfl

theorem affine_isLinearBlockModel (hd : 2 ≤ d) :
    IsLinearBlockModel (Affine d)
      (Representation.specialLinearNatural (k := ZMod 2) d) := by
  exact ⟨naturalAction d, ⟨affineBlockModuleModel d hd⟩, fun _ _ => rfl⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes
end
