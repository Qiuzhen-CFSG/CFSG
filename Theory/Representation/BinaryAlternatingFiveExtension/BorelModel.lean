module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.GroupTheory.PResidual.SupplementCommutator
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The actual residual and two-core in the binary A₄ extension

In the five-point core semidirect A₄, the fifth coordinate is a homomorphism.
Its kernel is the augmentation three-space semidirect A₄. The existing
Borel difference generators identify this kernel with the two-residual.
Its normal Sylow two-subgroup consists of the three-space and the regular
four-group, hence has order 32. Four generator tests identify its center;
squares lie in that center. The vector eight then supplies its Q₈ * Q₈ type
through the intrinsic extraspecial theorem.

Finite certificates use the literal order-192 model and its order-32 core,
with four test generators instead of a pairwise center enumeration. The full
representative check took 44 seconds and 2.1 GiB at the default limits.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup AlternatingFiveFlag AlternatingFiveBorel
abbrev V := Multiplicative (core (Fin 5))

def coreAut (g : Equiv.Perm (Fin 5)) : MulAut V where
  toFun v := Multiplicative.ofAdd (coreRepresentation (Fin 5) g v.toAdd)
  invFun v := Multiplicative.ofAdd (coreRepresentation (Fin 5) g⁻¹ v.toAdd)
  left_inv v := by
    change coreRepresentation (Fin 5) g⁻¹ (coreRepresentation (Fin 5) g v.toAdd) = v.toAdd
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  right_inv v := by
    change coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) g⁻¹ v.toAdd) = v.toAdd
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  map_mul' x y := by
    change coreRepresentation (Fin 5) g (x.toAdd + y.toAdd) =
      coreRepresentation (Fin 5) g x.toAdd + coreRepresentation (Fin 5) g y.toAdd
    exact map_add _ _ _

def coreAction : Equiv.Perm (Fin 5) →* MulAut V where
  toFun := coreAut
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 5) 1 v.toAdd) = v
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd (coreRepresentation (Fin 5) (g * h) v.toAdd) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) g (coreRepresentation (Fin 5) h v.toAdd))
    rw [map_mul, Module.End.mul_apply]

abbrev borelAction : B →* MulAut V := coreAction.comp ((alternatingGroup (Fin 5)).subtype.comp B.subtype)
abbrev BorelModel := V ⋊[borelAction] B
private instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4 = 4))
private instance : Fintype B := Subtype.fintype _
private instance : Fintype BorelModel := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private instance : DecidableEq BorelModel := SemidirectProduct.equivProd.injective.decidableEq

def height : BorelModel →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (x.left.toAdd.val 4)
  map_one' := rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (x.left.toAdd.val 4 + y.left.toAdd.val (x.right.val.val.symm 4)) = _
    rw [x.right.val.val.symm_apply_eq.mpr x.right.property.symm]
    rfl

abbrev residualModel : Subgroup BorelModel := height.ker

def coreModel : Subgroup BorelModel where
  carrier := {x | x.left.toAdd.val 4 = 0 ∧ x.right.val.val ∈ four}
  one_mem' := ⟨rfl, four.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    constructor
    · change (height (x * y)).toAdd = 0
      rw [map_mul]
      change x.left.toAdd.val 4 + y.left.toAdd.val 4 = 0
      rw [hx.1, hy.1, add_zero]
    · exact four.mul_mem hx.2 hy.2
  inv_mem' := by
    intro x hx
    constructor
    · change (height x⁻¹).toAdd = 0
      rw [map_inv]
      change -x.left.toAdd.val 4 = 0
      rw [hx.1, neg_zero]
    · exact four.inv_mem hx.2

private instance : DecidablePred (· ∈ coreModel) := fun x =>
  inferInstanceAs (Decidable (x.left.toAdd.val 4 = 0 ∧ x.right.val.val ∈ four))
private instance : Fintype coreModel := Subtype.fintype _
private instance : DecidablePred (· ∈ residualModel) := fun x =>
  inferInstanceAs (Decidable (height x = 1))
private instance : Fintype residualModel := Subtype.fintype _

theorem card_coreModel : Nat.card coreModel = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_residualModel : Nat.card residualModel = 96 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

def centralElement : coreModel := ⟨⟨Multiplicative.ofAdd FiveCentralizerGeometry.z, 1⟩, by decide +kernel⟩
private def generators : Fin 4 → coreModel := ![
  ⟨⟨Multiplicative.ofAdd ⟨![1,1,0,0,0], by decide +kernel⟩, 1⟩, by decide +kernel⟩,
  ⟨⟨Multiplicative.ofAdd ⟨![1,0,1,0,0], by decide +kernel⟩, 1⟩, by decide +kernel⟩,
  ⟨⟨1, ⟨⟨k₀, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩⟩, by decide +kernel⟩,
  ⟨⟨1, ⟨⟨k₁, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩⟩, by decide +kernel⟩]

private theorem centralElement_mem : centralElement ∈ center coreModel := by
  apply mem_center_iff.mpr
  exact (by decide +kernel : ∀ x : coreModel, x * centralElement = centralElement * x)
private theorem centralElement_ne : centralElement ≠ 1 := by decide +kernel
private theorem central_cases (x : coreModel) (hx : x ∈ center coreModel) :
    x = 1 ∨ x = centralElement := by
  have hc : ∀ x : coreModel, (∀ i : Fin 4, generators i * x = x * generators i) →
      x = 1 ∨ x = centralElement := by decide +kernel
  exact hc x (fun i => mem_center_iff.mp hx (generators i))

theorem card_center_coreModel : Nat.card (center coreModel) = 2 := by
  apply (Nat.card_eq_two_iff' (1 : center coreModel)).mpr
  refine ⟨⟨centralElement, centralElement_mem⟩, ?_, ?_⟩
  · exact fun h => centralElement_ne (congrArg Subtype.val h)
  · intro x hx
    rcases central_cases x x.property with h | h
    · exact (hx (Subtype.ext h)).elim
    · exact Subtype.ext h

theorem square_coreModel (x : coreModel) : x ^ 2 ∈ center coreModel := by
  have h : ∀ x : coreModel, x ^ 2 = 1 ∨ x ^ 2 = centralElement := by decide +kernel
  rcases h x with h | h
  · rw [h]; exact (center coreModel).one_mem
  · rw [h]; exact centralElement_mem

private theorem elementary_of_square {D : Type*} [Group D]
    (hs : ∀ x : D, x ^ 2 = 1) : IsElementaryAbelian 2 D := by
  have hi (x : D) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs x)
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  calc
    x * y = (x * y)⁻¹ := (hi _).symm
    _ = y * x := by rw [mul_inv_rev, hi, hi]

theorem coreModel_extraspecial : IsExtraspecial 2 coreModel := by
  refine { center_order_p := card_center_coreModel
           quotient_elementary_abelian := elementary_of_square ?_
           quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }
  · intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center coreModel) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (square_coreModel x)
  · intro he
    have hc := card_center_coreModel
    rw [he, Nat.card_congr (topEquiv : (⊤ : Subgroup coreModel) ≃* coreModel).toEquiv,
      card_coreModel] at hc
    omega

theorem residualModel_eq : pResidual 2 BorelModel = residualModel := by
  apply le_antisymm
  · exact pResidual_le_ker_of_isPGroup 2 height (IsPGroup.of_card (n := 1) (by
      rw [Nat.card_eq_fintype_card]; decide +kernel))
  · have hb (b : B) : SemidirectProduct.inr b ∈ pResidual 2 BorelModel :=
      map_pResidual_le 2 (SemidirectProduct.inr : B →* BorelModel)
        (mem_map_of_mem _ (borel_twoResidual ▸ mem_top b))
    have hw : three ≤ (pResidual 2 BorelModel).comap SemidirectProduct.inl := by
      apply three_le_of_differences
      intro g x
      have hc := commutator_le_left (pResidual 2 BorelModel) (⊤ : Subgroup BorelModel)
        (commutator_mem_commutator (hb g) (mem_top (SemidirectProduct.inl (Multiplicative.ofAdd x))))
      change (SemidirectProduct.inl (Multiplicative.ofAdd (rho g.val.val x - x)) : BorelModel) ∈ pResidual 2 BorelModel
      convert hc using 1
      rw [commutatorElement_def, ← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul]
      congr 1
      exact congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _)
    intro x hx
    rw [← SemidirectProduct.inl_left_mul_inr_right x]
    exact (pResidual 2 BorelModel).mul_mem (hw hx) (hb x.right)

theorem coreModel_le_residual : coreModel ≤ residualModel := fun _ hx => hx.1

instance coreModel_normal : coreModel.Normal where
  conj_mem x hx g := by
    constructor
    · change height (g * x * g⁻¹) = 1
      rw [map_mul, map_mul, map_inv, show height x = 1 from hx.1]
      simp
    · exact (normalizes_four_of_fixes g.right.val.val g.right.property x.right.val.val).mp hx.2

theorem core_residualModel : pCore 2 residualModel = coreModel.subgroupOf residualModel := by
  let P := coreModel.subgroupOf residualModel
  have hc : Nat.card P = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe coreModel_le_residual).toEquiv).trans card_coreModel
  let S : Sylow 2 residualModel := Sylow.ofCard P (by
    rw [hc, card_residualModel]; decide +kernel)
  let : (S : Subgroup residualModel).Normal := inferInstanceAs P.Normal
  apply le_antisymm (pCore_isPGroup.le_sylow_of_normal S)
  exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 5) hc⟩

noncomputable def borel_core_equiv : pCore 2 (pResidual 2 BorelModel) ≃* coreModel :=
  let e := MulEquiv.subgroupCongr residualModel_eq
  ((e.subgroupMap (pCore 2 (pResidual 2 BorelModel))).trans
    (MulEquiv.subgroupCongr ((pCore_map_iso 2 e).trans core_residualModel))).trans
      (subgroupOfEquivOfLe coreModel_le_residual)

private def eight : Subgroup coreModel :=
  ((SemidirectProduct.rightHom : BorelModel →* B).comp coreModel.subtype).ker
private instance : DecidablePred (· ∈ eight) := fun x => inferInstanceAs (Decidable (x.val.right = 1))
private instance : Fintype eight := Subtype.fintype _
private instance : eight.Normal := MonoidHom.normal_ker _
private theorem eight_card : Nat.card eight = 8 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel
private instance : IsElementaryAbelian 2 eight := elementary_of_square (by decide +kernel)
private theorem center_le_eight : center coreModel ≤ eight := by
  intro x hx
  rcases central_cases x hx with rfl | rfl <;> rfl

theorem coreModel_quaternion : Nonempty (QuaternionCentralProductData coreModel) := by
  let : IsExtraspecial 2 coreModel := coreModel_extraspecial
  obtain ⟨D,E,hD,hE,hgen,hi,hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary card_coreModel eight
      eight_card center_le_eight
  exact ⟨⟨D,E,hD,hE,hi,hcomm,hgen⟩⟩

noncomputable def coreModelQuaternionData : QuaternionCentralProductData coreModel :=
  Classical.choice coreModel_quaternion

/-- The actual two-core of the two-residual of the natural A₄ semidirect product is Q₈ * Q₈. -/
noncomputable def borelCoreQuaternionData : QuaternionCentralProductData (pCore 2 (pResidual 2 BorelModel)) :=
  coreModelQuaternionData.map borel_core_equiv.symm

end BinaryPermutation.AlternatingFiveExtension
