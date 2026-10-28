module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.OverlapGenerators

/-!
# The first-local words give the full canonical overlaps

The upper root words, a primitive diagonal element, and the field actor
supply the whole point stabilizer. Adding the Weyl word supplies the whole
pair stabilizer. The identifications retain the literal four overlap words.
-/
@[expose] public noncomputable section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup
open BenderSuzuki.Converse
open Sporadic.Janko3.SourceRecognition.Seventeen

private theorem model_uni (c : F) :
    modelEquiv (SemidirectProduct.inl (uni c)) = ModelAmalgam.rootHom (Multiplicative.ofAdd (fieldEquiv c)) := by
  apply SemidirectProduct.ext
  · change Theory.PSL2.quotientMap _ (GorensteinWalter.sl2RingEquiv fieldEquiv (uni c)) =
      Theory.PSL2.quotientMap _ (uni (fieldEquiv c))
    apply congrArg (Theory.PSL2.quotientMap _)
    apply Subtype.ext
    funext i j
    rw [GorensteinWalter.sl2RingEquiv_apply_entry]
    fin_cases i <;> fin_cases j <;> simp [uni_val]
  · exact map_one actorEquiv

private theorem model_tor (u : Fˣ) :
    modelEquiv (SemidirectProduct.inl (tor u)) =
      Theory.PSL2.BinaryFourFieldExtension.linearInclusion
        (ModelAmalgam.torusHom (Units.mapEquiv fieldEquiv.toMulEquiv u)) := by
  apply SemidirectProduct.ext
  · change Theory.PSL2.quotientMap _ (GorensteinWalter.sl2RingEquiv fieldEquiv (tor u)) =
      Theory.PSL2.quotientMap _ (tor (Units.mapEquiv fieldEquiv.toMulEquiv u))
    apply congrArg (Theory.PSL2.quotientMap _)
    apply Subtype.ext
    funext i j
    rw [GorensteinWalter.sl2RingEquiv_apply_entry]
    fin_cases i <;> fin_cases j <;> simp [tor_val,Units.coe_mapEquiv]
  · exact map_one actorEquiv

private theorem model_swap : modelEquiv swapGenerator = ModelAmalgam.swap := by
  apply SemidirectProduct.ext
  · change Theory.PSL2.quotientMap _ (GorensteinWalter.sl2RingEquiv fieldEquiv (weyl F)) =
      Theory.PSL2.quotientMap _ (weyl ModelAmalgam.F)
    apply congrArg (Theory.PSL2.quotientMap _)
    apply Subtype.ext
    funext i j
    rw [GorensteinWalter.sl2RingEquiv_apply_entry]
    fin_cases i <;> fin_cases j <;> simp [weyl_val]
  · exact map_one actorEquiv

private theorem model_inr (a : Two) :
    modelEquiv (SemidirectProduct.inr a) = SemidirectProduct.inr (actorEquiv a) := by
  apply SemidirectProduct.ext
  · exact map_one linearEquiv
  · rfl

private theorem diagonal_mem (S : Subgroup ComputableModel) (hd : diagonalGenerator ∈ S)
    (u : Fˣ) : SemidirectProduct.inl (tor u) ∈ S := by
  have hu : u ∈ zpowers primitiveUnit := by rw [primitiveUnit_generates]; trivial
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hu
  change SemidirectProduct.inl (torHom F (primitiveUnit ^ n)) ∈ S
  rw [map_zpow,map_zpow]
  exact S.zpow_mem hd n

private theorem field_mem (S : Subgroup ComputableModel) (hf : fieldGenerator ∈ S)
    (a : Two) : SemidirectProduct.inr a ∈ S := by
  have ha : a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 2) := by
    revert a
    decide +kernel
  rcases ha with rfl | rfl
  · simpa only [map_one] using S.one_mem
  · exact hf

private theorem overlap_le_image (S : Subgroup ComputableModel)
    (hd : diagonalGenerator ∈ S) (hf : fieldGenerator ∈ S) :
    ModelAmalgam.point ⊓ ModelAmalgam.pair ≤ S.map modelEquiv.toMonoidHom := by
  intro x hx
  obtain ⟨a,rfl⟩ := ModelAmalgam.torusLift_range.symm ▸ hx
  obtain ⟨u,hu⟩ := (Units.mapEquiv fieldEquiv.toMulEquiv).surjective a.left
  obtain ⟨b,hb⟩ := actorEquiv.surjective a.right
  refine ⟨SemidirectProduct.inl (tor u) * SemidirectProduct.inr b,
    S.mul_mem (diagonal_mem S hd u) (field_mem S hf b), ?_⟩
  rw [map_mul]
  change modelEquiv (SemidirectProduct.inl (tor u)) * modelEquiv (SemidirectProduct.inr b) = _
  rw [model_tor,model_inr,hu,hb]
  apply SemidirectProduct.ext
  · change ModelAmalgam.torusHom a.left * _ = ModelAmalgam.torusHom a.left
    simp
  · change 1 * a.right = a.right
    simp

private theorem model_mem_point (x : ComputableModel) (hx : x.left.val 1 0 = 0) :
    modelEquiv x ∈ ModelAmalgam.point := by
  rw [ModelAmalgam.mem_point,PBorel_eq_map]
  refine ⟨GorensteinWalter.sl2RingEquiv fieldEquiv x.left, ?_, rfl⟩
  apply (mem_Borel_iff _).mpr
  rw [GorensteinWalter.sl2RingEquiv_apply_entry,hx,map_zero]

private theorem model_mem_overlap (x : ComputableModel)
    (h10 : x.left.val 1 0 = 0) (h01 : x.left.val 0 1 = 0) :
    modelEquiv x ∈ ModelAmalgam.point ⊓ ModelAmalgam.pair := by
  rw [ModelAmalgam.mem_overlap]
  refine ⟨GorensteinWalter.sl2RingEquiv fieldEquiv x.left, ?_, rfl⟩
  constructor
  · apply (mem_stabilizer_pInf_iff _).mpr
    rw [GorensteinWalter.sl2RingEquiv_apply_entry,h10,map_zero]
  · apply (mem_stabilizer_pZero_iff _).mpr
    rw [GorensteinWalter.sl2RingEquiv_apply_entry,h01,map_zero]

private theorem point_image_le : pointWords.map modelEquiv.toMonoidHom ≤ ModelAmalgam.point := by
  rw [map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | ⟨rfl | h⟩
  · exact model_mem_point _ (by decide +kernel)
  · exact model_mem_point _ (by decide +kernel)

private theorem pair_image_le : pairWords.map modelEquiv.toMonoidHom ≤ ModelAmalgam.pair := by
  rw [map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | ⟨rfl | h⟩
  · exact (model_mem_overlap _ (by decide +kernel) (by decide +kernel)).2
  · have he : pairSecond = (pairSecond * swapGenerator) * swapGenerator := by
      have hs : swapGenerator * swapGenerator = 1 := by
        apply SemidirectProduct.ext
        · apply Subtype.ext
          funext i j
          fin_cases i <;> fin_cases j <;> decide +kernel
        · decide +kernel
      rw [mul_assoc,hs,mul_one]
    change modelEquiv pairSecond ∈ ModelAmalgam.pair
    rw [he,map_mul,model_swap]
    exact ModelAmalgam.pair.mul_mem
      (model_mem_overlap _ (by decide +kernel) (by decide +kernel)).2 ModelAmalgam.swap_mem_pair

/-- The literal first-local order-480 words give the standard point stabilizer. -/
theorem pointWords_image : pointWords.map modelEquiv.toMonoidHom = ModelAmalgam.point := by
  apply le_antisymm point_image_le
  intro x hx
  obtain ⟨⟨r,c⟩,he,_⟩ := ModelAmalgam.pointComplement.existsUnique (⟨x,hx⟩ : ModelAmalgam.point)
  have he' : ((r : ModelAmalgam.point) : Theory.PSL2.BinaryFourFieldExtension.Model) *
      ((c : ModelAmalgam.point) : Theory.PSL2.BinaryFourFieldExtension.Model) = x := congrArg Subtype.val he
  rw [←he']
  apply Subgroup.mul_mem
  · obtain ⟨t,ht⟩ := r.property
    refine ⟨SemidirectProduct.inl (uni (fieldEquiv.symm t.toAdd)), upper_mem_pointWords _, ?_⟩
    change modelEquiv (SemidirectProduct.inl (uni (fieldEquiv.symm t.toAdd))) = _
    rw [model_uni,fieldEquiv.apply_symm_apply]
    exact ht
  · exact overlap_le_image pointWords pointDiagonal_mem pointField_mem c.property

/-- The literal first-local order-60 words give the standard pair stabilizer. -/
theorem pairWords_image : pairWords.map modelEquiv.toMonoidHom = ModelAmalgam.pair := by
  apply le_antisymm pair_image_le
  have hstab : MulAction.stabilizer Theory.PSL2.BinaryFourFieldExtension.Model (pInf ModelAmalgam.F) ⊓
      MulAction.stabilizer Theory.PSL2.BinaryFourFieldExtension.Model (pZero ModelAmalgam.F) =
      ModelAmalgam.point ⊓ ModelAmalgam.pair := by
    ext x
    rw [ModelAmalgam.mem_overlap,PTorus_eq]
    change (x • pInf ModelAmalgam.F = pInf ModelAmalgam.F ∧ x • pZero ModelAmalgam.F = pZero ModelAmalgam.F) ↔ _
    simp only [ModelAmalgam.model_smul,ModelAmalgam.fieldPoint_inf,ModelAmalgam.fieldPoint_zero]
    rfl
  have hpair : ModelAmalgam.pair = ModelAmalgam.point ⊓ ModelAmalgam.pair ⊔ zpowers ModelAmalgam.swap :=
    ModelAmalgam.pair_generated.trans (congrArg (fun S => S ⊔ zpowers ModelAmalgam.swap) hstab)
  rw [hpair]
  apply sup_le
  · exact overlap_le_image pairWords pairDiagonal_mem pairField_mem
  · apply zpowers_le.mpr
    exact ⟨swapGenerator,pairSwap_mem,model_swap⟩

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
