module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Torus
/-!
# The literal pair stabilizer is S₃ × D₁₀

The diagonal-and-field overlap is extended by the Weyl involution exchanging
infinity and zero. Weyl inversion on the torus commutes with the field actor.
The resulting order-sixty coordinate group splits as D₆ × D₁₀, with D₆
identified with the actual symmetric group on three letters.

The map from these coordinates to PSL₂(16):2 is constructed using the actual
diagonal matrices, Weyl matrix and fourth-power field actor. Its image is
the full setwise pair stabilizer, and equal orders make it an isomorphism.
The finite checks are confined to the order-sixty coordinate group.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model amalgam used in Corollary 2.10.
-/

@[expose] public section
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.CyclicCoordinates

def inversion : MulAut AffineTorus where
  toFun x := ⟨x.left⁻¹, x.right⟩
  invFun x := ⟨x.left⁻¹, x.right⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp
  map_mul' := by decide +kernel

def weylAction : Two →* MulAut AffineTorus where
  toFun a := if a = 1 then 1 else inversion
  map_one' := by simp
  map_mul' a b := by
    apply DFunLike.ext
    intro x
    revert a b x
    decide +kernel

abbrev Normalizer := AffineTorus ⋊[weylAction] Two
instance : Fintype Normalizer := Fintype.ofEquiv (AffineTorus × Two) SemidirectProduct.equivProd.symm

def toDihedral (x : Normalizer) : DihedralGroup 3 × DihedralGroup 5 :=
  ((if x.right = 1 then DihedralGroup.r (x.left.left.toAdd.val : ZMod 3)
    else DihedralGroup.sr (-(x.left.left.toAdd.val : ZMod 3))),
   (if x.left.right = x.right then DihedralGroup.r (x.left.left.toAdd.val : ZMod 5)
    else DihedralGroup.sr (-(x.left.left.toAdd.val : ZMod 5))))

def dihedralHom : Normalizer →* (DihedralGroup 3 × DihedralGroup 5) where
  toFun := toDihedral
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def dihedralEquiv : Normalizer ≃* (DihedralGroup 3 × DihedralGroup 5) :=
  MulEquiv.ofBijective dihedralHom (by decide +kernel)

def trianglePerm : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | .r i => (Equiv.swap 0 1 * Equiv.swap 1 2) ^ i.val
  | .sr i => Equiv.swap 0 1 * (Equiv.swap 0 1 * Equiv.swap 1 2) ^ i.val

def trianglePermHom : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun := trianglePerm
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

noncomputable def trianglePermEquiv : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective trianglePermHom (by decide +kernel)

noncomputable def pairEquiv : Normalizer ≃* (Equiv.Perm (Fin 3) × DihedralGroup 5) :=
  dihedralEquiv.trans (MulEquiv.prodCongr trianglePermEquiv (MulEquiv.refl _))

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.CyclicCoordinates

@[expose] public noncomputable section
open Subgroup MulAction Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

def twoGenerator : CyclicCoordinates.Two := Multiplicative.ofAdd 1

theorem two_cases (a : CyclicCoordinates.Two) : a = 1 ∨ a = twoGenerator := by
  revert a
  decide +kernel

def swapHom : CyclicCoordinates.Two →* Model where
  toFun a := if a = 1 then 1 else swap
  map_one' := by simp
  map_mul' a b := by
    have htwo : (Multiplicative.ofAdd 1 : CyclicCoordinates.Two) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases two_cases a with rfl | rfl <;> rcases two_cases b with rfl | rfl <;>
      simp [twoGenerator, swap_square, htwo]

theorem swapHom_generator : swapHom twoGenerator = swap := by
  simp [swapHom, twoGenerator]

theorem field_weyl (a : Actor) : action a (PWeyl F) = PWeyl F := by
  change fieldAut a.val (quotientMap F (weyl F)) = quotientMap F (weyl F)
  rw [fieldAut_apply_quotientMap]
  apply congrArg (quotientMap F)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, weyl_val]

theorem swap_torus (u : Fˣ) :
    swap * linearInclusion (torusHom u) * swap⁻¹ = linearInclusion (torusHom u⁻¹) := by
  change linearInclusion (PWeyl F) * linearInclusion (torusHom u) *
    (linearInclusion (PWeyl F))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg linearInclusion
  change quotientMap F (weyl F) * quotientMap F (tor u) *
    (quotientMap F (weyl F))⁻¹ = quotientMap F (tor u⁻¹)
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (quotientMap F)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl_inv, weyl_val, tor_val, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_commutes_actor (a : Actor) : Commute swap (SemidirectProduct.inr a) := by
  apply SemidirectProduct.ext
  · change PWeyl F * action 1 1 = 1 * action a (PWeyl F)
    rw [field_weyl, map_one, one_mul, mul_one]
  · change 1 * a = a * 1
    simp

theorem torusLift_eq (x : Fˣ ⋊[unitsAction] Actor) :
    torusLift x = linearInclusion (torusHom x.left) * SemidirectProduct.inr x.right := by
  apply SemidirectProduct.ext
  · change torusHom x.left = torusHom x.left * action 1 1
    simp
  · change x.right = 1 * x.right
    simp

theorem swap_torusLift (x : Fˣ ⋊[unitsAction] Actor) :
    swap * torusLift x * swap⁻¹ = torusLift ⟨x.left⁻¹, x.right⟩ := by
  rw [torusLift_eq, torusLift_eq]
  change (MulAut.conj swap) (linearInclusion (torusHom x.left) *
      SemidirectProduct.inr x.right) = _
  rw [map_mul]
  change (swap * linearInclusion (torusHom x.left) * swap⁻¹) *
    (swap * SemidirectProduct.inr x.right * swap⁻¹) = _
  rw [swap_torus, (swap_commutes_actor x.right).eq, mul_inv_cancel_right]

theorem torusCoordinates_inversion (x : Fˣ ⋊[unitsAction] Actor) :
    CyclicCoordinates.inversion (torusCoordinates x) = torusCoordinates ⟨x.left⁻¹, x.right⟩ := by
  apply SemidirectProduct.ext
  · exact (map_inv unitsEquiv x.left).symm
  · rfl

def pairLift : CyclicCoordinates.Normalizer →* Model :=
  SemidirectProduct.lift (torusLift.comp torusCoordinates.symm.toMonoidHom) swapHom (by
    intro a
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := torusCoordinates.surjective x
    rcases two_cases a with rfl | rfl
    · simp only [map_one, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.one_apply]
    · change torusLift (torusCoordinates.symm
        (CyclicCoordinates.inversion (torusCoordinates x))) =
        swapHom twoGenerator * torusLift (torusCoordinates.symm (torusCoordinates x)) *
        (swapHom twoGenerator)⁻¹
      rw [torusCoordinates_inversion, torusCoordinates.symm_apply_apply,
        torusCoordinates.symm_apply_apply, swapHom_generator, swap_torusLift])

theorem pairLift_range : pairLift.range = pair := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change torusLift (torusCoordinates.symm x.left) * swapHom x.right ∈ pair
    apply pair.mul_mem
    · exact (torusLift_range ▸ (show torusLift (torusCoordinates.symm x.left) ∈ torusLift.range from
        ⟨_, rfl⟩)).2
    · rcases two_cases x.right with h | h
      · rw [h, map_one]
        exact pair.one_mem
      · rw [h, swapHom_generator]
        exact swap_mem_pair
  · have hp : stabilizer Model (pInf F) ⊓ stabilizer Model (pZero F) = point ⊓ pair := by
      ext x
      rw [mem_overlap, PTorus_eq]
      change (x • pInf F = pInf F ∧ x • pZero F = pZero F) ↔ _
      simp only [model_smul, fieldPoint_inf, fieldPoint_zero]
      rfl
    rw [pair_generated, hp]
    apply sup_le
    · intro x hx
      obtain ⟨y, hy⟩ := torusLift_range.symm ▸ hx
      refine ⟨SemidirectProduct.inl (torusCoordinates y), ?_⟩
      change SemidirectProduct.lift _ _ _ (SemidirectProduct.inl _) = x
      rw [SemidirectProduct.lift_inl]
      change torusLift (torusCoordinates.symm (torusCoordinates y)) = x
      rw [torusCoordinates.symm_apply_apply]
      exact hy
    · apply zpowers_le.mpr
      refine ⟨SemidirectProduct.inr twoGenerator, ?_⟩
      exact (SemidirectProduct.lift_inr _ _ _ _).trans swapHom_generator

theorem pairLift_injective : Function.Injective pairLift := by
  have hs : Function.Surjective (pairLift.rangeRestrict) := pairLift.rangeRestrict_surjective
  have hc : Nat.card CyclicCoordinates.Normalizer = Nat.card pairLift.range := by
    rw [pairLift_range, pair_card, SemidirectProduct.card, SemidirectProduct.card]
    norm_num [CyclicCoordinates.Fifteen, CyclicCoordinates.Two, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative]
  have hb := (Nat.bijective_iff_surjective_and_card pairLift.rangeRestrict).mpr ⟨hs, hc⟩
  intro x y h
  exact hb.1 (Subtype.ext h)

def pairEquiv : pair ≃* (Equiv.Perm (Fin 3) × DihedralGroup 5) :=
  ((MonoidHom.ofInjective pairLift_injective).trans
    (MulEquiv.subgroupCongr pairLift_range)).symm.trans CyclicCoordinates.pairEquiv

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
