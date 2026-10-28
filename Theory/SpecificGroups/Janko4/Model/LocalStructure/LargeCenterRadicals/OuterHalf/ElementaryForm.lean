module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.InnerHalves
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The intrinsic outer-half form on elementary subgroups of J₄

Each nonidentity row is the character of the actual index-two solvable
residual in its full involution centralizer. The identity row is zero.
The two-core and characteristic-two centralizer calculations give diagonal
vanishing. Commuting-involution symmetry alone then gives a bilinear,
alternating form, possibly degenerate, preserved by the actual normalizer.

The symmetry premise remains explicit here so native elementary-normalizer
coverage can use this narrow leaf while the finite pair comparisons are proved
separately. No normalizer coverage or radical quotient assertion is assumed.

Source: Kleidman--Wilson, The Maximal Subgroups of J4 (1988), p.487,
Corollary 1.1.4. The underlying native model retains the attribution of the
imported involution-centralizer modules.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem first_center_le_residual :
    center InvolutionCentralizers.First.centralizer ≤
      solvableResidual InvolutionCentralizers.First.centralizer :=
  (center_le_centralizer _).trans
    (InvolutionCentralizers.first_characteristic_two.trans
      InvolutionCentralizers.First.twoCore_le_residual)

private theorem second_center_le_residual :
    center InvolutionCentralizers.Second.ambientCentralizer ≤
      solvableResidual InvolutionCentralizers.Second.ambientCentralizer := by
  open InvolutionCentralizers.Second in
  have hc := (center_le_centralizer (pCore 2 ambientCentralizer : Set ambientCentralizer)).trans
    InvolutionCentralizers.second_characteristic_two
  rw [ambient_twoCore_eq_kernel] at hc
  rw [← second_innerHalf_eq_residual]
  exact hc.trans (MonoidHom.ker_le_comap _ _)

/-- Every involution belongs to the residual of its own full centralizer. -/
theorem innerRelated_self (x : Model) (hx : orderOf x = 2) : InnerRelated x x := by
  let z : centralizer ({x} : Set Model) := ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : z ∈ center (centralizer ({x} : Set Model)) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property)
  suffices z ∈ solvableResidual (centralizer ({x} : Set Model)) from ⟨z, this, rfl⟩
  rcases InvolutionCentralizers.centralizer_equiv_first_or_second x hx with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  all_goals
    have he : e z ∈ center _ := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz w)
  · have hm := first_center_le_residual he
    rw [← map_solvableResidual_eq e.toMonoidHom e.surjective] at hm
    exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hm
  · have hm := second_center_le_residual he
    rw [← map_solvableResidual_eq e.toMonoidHom e.surjective] at hm
    exact (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hm

/-- The actual outer-half value, with the identity row defined to be zero. -/
@[expose] def outerValue (x y : Model) : ZMod 2 :=
  open Classical in if x = 1 ∨ InnerRelated x y then 0 else 1

@[simp] theorem outerValue_one_left (y : Model) : outerValue 1 y = 0 := by
  simp [outerValue]

@[simp] theorem outerValue_one_right (x : Model) : outerValue x 1 = 0 := by
  have h : InnerRelated x 1 := ((solvableResidual _).map _).one_mem
  simp [outerValue, h]

theorem outerValue_eq_zero_iff (x y : Model) (hx : x ≠ 1) :
    outerValue x y = 0 ↔ InnerRelated x y := by
  simp [outerValue, hx]

/-- The quotient of the full centralizer by its residual has order two. -/
theorem outerValue_mul_right (x : Model) (hx : orderOf x = 2)
    (y z : Model) (hy : Commute x y) (hz : Commute x z) :
    outerValue x (y * z) = outerValue x y + outerValue x z := by
  have hne : x ≠ 1 := by intro h; simp [h] at hx
  let u : centralizer ({x} : Set Model) := ⟨y, mem_centralizer_singleton_iff.mpr hy.eq.symm⟩
  let v : centralizer ({x} : Set Model) := ⟨z, mem_centralizer_singleton_iff.mpr hz.eq.symm⟩
  have hm : InnerRelated x (y * z) ↔ (InnerRelated x y ↔ InnerRelated x z) := by
    have h := (solvableResidual (centralizer ({x} : Set Model))).mul_mem_iff_of_index_two
      (involution_residual_index x hx) (a := u) (b := v)
    change InnerRelated x ((u * v : centralizer ({x} : Set Model)) : Model) ↔
      (InnerRelated x (u : Model) ↔ InnerRelated x (v : Model))
    have hr (w : centralizer ({x} : Set Model)) :
        InnerRelated x w ↔ w ∈ solvableResidual (centralizer ({x} : Set Model)) :=
      mem_map_iff_mem (centralizer ({x} : Set Model)).subtype_injective
    rw [hr, hr, hr]
    exact h
  by_cases hy' : InnerRelated x y <;> by_cases hz' : InnerRelated x z <;>
    simp [outerValue, hne, hm, hy', hz']

/-- Automorphisms preserve the value because they preserve the actual residuals. -/
theorem outerValue_equiv (e : Model ≃* Model) (x y : Model) :
    outerValue (e x) (e y) = outerValue x y := by
  unfold outerValue
  rw [map_eq_one_iff _ e.injective, innerRelated_equiv]

variable (X : Subgroup Model) [IsElementaryAbelian 2 X]

private theorem elementary_order (x : X) (hx : (x : Model) ≠ 1) : orderOf (x : Model) = 2 := by
  have hd := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property)
  exact ((Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left (by simpa using hx))

private theorem elementary_commute (x y : X) : Commute (x : Model) (y : Model) :=
  congrArg Subtype.val (mul_comm x y)

/-- Each row is linear, independently of symmetry. -/
@[expose] def outerRow (x : X) : Additive X →ₗ[ZMod 2] ZMod 2 :=
  ({ toFun := fun y => outerValue x y.toMul
     map_zero' := outerValue_one_right x
     map_add' := by
       intro y z
       by_cases hx : (x : Model) = 1
       · simp only [hx, outerValue_one_left, add_zero]
       · exact outerValue_mul_right x (elementary_order X x hx) y.toMul z.toMul
           (elementary_commute X x y.toMul) (elementary_commute X x z.toMul)
   } : Additive X →+ ZMod 2).toZModLinearMap 2

variable (hsym : ∀ x y : Model, orderOf x = 2 → orderOf y = 2 → Commute x y →
  (InnerRelated x y ↔ InnerRelated y x))

include hsym in
theorem outerValue_symm (x y : X) : outerValue x y = outerValue y x := by
  by_cases hx : (x : Model) = 1
  · simp [hx]
  by_cases hy : (y : Model) = 1
  · simp [hy]
  have hr := hsym x y (elementary_order X x hx) (elementary_order X y hy)
    (elementary_commute X x y)
  unfold outerValue
  by_cases hxy : InnerRelated x y
  · rw [if_pos (Or.inr hxy), if_pos (Or.inr (hr.mp hxy))]
  · rw [if_neg (not_or.mpr ⟨hx, hxy⟩),
      if_neg (not_or.mpr ⟨hy, fun h => hxy (hr.mpr h)⟩)]

/-- The intrinsic binary form on an elementary subgroup; only commuting-involution
symmetry is an input. No nondegeneracy condition is imposed. -/
@[expose] def elementaryForm : LinearMap.BilinForm (ZMod 2) (Additive X) :=
  ({ toFun := fun x => outerRow X x.toMul
     map_zero' := by
       ext y
       exact outerValue_one_left y.toMul
     map_add' := by
       intro x y
       ext z
       change outerValue ((x + y).toMul : Model) z.toMul =
         outerValue x.toMul z.toMul + outerValue y.toMul z.toMul
       rw [outerValue_symm X hsym (x + y).toMul z.toMul,
         outerValue_symm X hsym x.toMul z.toMul, outerValue_symm X hsym y.toMul z.toMul]
       exact (outerRow X z.toMul).map_add x y
    } : Additive X →+ (Additive X →ₗ[ZMod 2] ZMod 2)).toZModLinearMap 2

@[simp] theorem elementaryForm_apply (x y : Additive X) :
    elementaryForm X hsym x y = outerValue x.toMul y.toMul := rfl

theorem elementaryForm_isAlt : (elementaryForm X hsym).IsAlt := by
  intro x
  rw [elementaryForm_apply]
  by_cases hx : (x.toMul : Model) = 1
  · simp [hx]
  · exact (outerValue_eq_zero_iff _ _ hx).mpr
      (innerRelated_self x.toMul (elementary_order X x.toMul hx))

theorem elementaryForm_isSymm : (elementaryForm X hsym).IsSymm :=
  ⟨fun x y => outerValue_symm X hsym x.toMul y.toMul⟩

theorem elementaryForm_eq_zero_iff (x y : Additive X) (hx : x ≠ 0) :
    elementaryForm X hsym x y = 0 ↔ InnerRelated x.toMul y.toMul := by
  apply outerValue_eq_zero_iff
  intro h
  apply hx
  exact Additive.toMul.injective (Subtype.ext h)

/-- Simultaneous ambient conjugacy, with the literal embeddings retained. -/
theorem elementaryForm_equiv (Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (e : Model ≃* Model) (f : X ≃* Y) (hf : ∀ x : X, (f x : Model) = e x)
    (x y : Additive X) :
    elementaryForm Y hsym (Additive.ofMul (f x.toMul)) (Additive.ofMul (f y.toMul)) =
      elementaryForm X hsym x y := by
  change outerValue (f x.toMul) (f y.toMul) = outerValue x.toMul y.toMul
  rw [hf, hf]
  exact outerValue_equiv e x.toMul y.toMul

/-- Invariance under the actual normalizer action on X. -/
theorem elementaryForm_normalizer (g : normalizer (X : Set Model)) (x y : Additive X) :
    elementaryForm X hsym (Additive.ofMul (g • x.toMul)) (Additive.ofMul (g • y.toMul)) =
      elementaryForm X hsym x y :=
  elementaryForm_equiv X hsym X (MulAut.conj (g : Model))
    (X.normalizerMonoidHom g) (fun _ => rfl) x y

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
