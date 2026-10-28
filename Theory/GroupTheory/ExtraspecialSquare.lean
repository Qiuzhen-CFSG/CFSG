module
public import Theory.GroupTheory.BinarySquareForm
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Square geometry of extraspecial two-groups

Squaring on the literal central quotient gives a binary quadratic form.
The existing central-square construction supplies its polar form, which is
nondegenerate because a representative commuting with every group element
is central. Automorphisms fix the center and preserve this form, and their
linear isometry action has exactly the original central-quotient kernel.

An elementary subgroup has a totally singular image. Its order determines
the dimension of that image, and passage to the quotient preserves joins.
These facts construct the original eight-dimensional pair geometry in
Aschbacher--Smith F.9.5(6.ii), printed pp.319--320, and 12.6.26, p.831.
The exposed definitions retain the actual quotient and its square map.
-/

@[expose] public section
namespace Theory.GroupTheory.ExtraspecialSquare
open Subgroup
open scoped IsMulCommutative commutatorElement

abbrev Space (Q : Type*) [Group Q] := Additive (Q ⧸ center Q)

variable (Q : Type*) [Group Q] [IsExtraspecial 2 Q]

instance spaceAddCommGroup : AddCommGroup (Space Q) := by
  letI := IsExtraspecial.quotient_elementary_abelian 2 Q
  exact inferInstanceAs (AddCommGroup (Additive (Q ⧸ center Q)))

instance spaceModule : Module (ZMod 2) (Space Q) := by
  letI := IsExtraspecial.quotient_elementary_abelian 2 Q
  exact inferInstanceAs (Module (ZMod 2) (Additive (Q ⧸ center Q)))

def projection : Q →* Multiplicative (Space Q) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (center Q) x))
  map_one' := rfl
  map_mul' _ _ := rfl

omit [IsExtraspecial 2 Q] in
@[simp] theorem projection_apply (x : Q) :
    (projection Q x).toAdd = Additive.ofMul (QuotientGroup.mk' (center Q) x) := rfl

omit [IsExtraspecial 2 Q] in
theorem projection_ker : (projection Q).ker = center Q := by
  ext x
  exact QuotientGroup.eq_one_iff x

omit [IsExtraspecial 2 Q] in
theorem projection_surjective : Function.Surjective (projection Q) := by
  intro v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center Q) v.toAdd.toMul
  exact ⟨x,congrArg (fun q => Multiplicative.ofAdd (Additive.ofMul q)) hx⟩

theorem center_square (z : Q) (hz : z ∈ center Q) : z^2 = 1 := by
  have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : center Q))
  rw [IsExtraspecial.center_order_p 2 Q] at hh
  exact congrArg Subtype.val hh

noncomputable def centerCoordinate : center Q ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (IsExtraspecial.center_order_p 2 Q) (by simp)

noncomputable def form : QuadraticForm (ZMod 2) (Space Q) :=
  BinarySquareForm.quadraticForm (projection Q) (projection_ker Q)
    (projection_surjective Q) (center_square Q) (centerCoordinate Q).toMonoidHom

theorem form_mk (x : Q) :
    form Q (Additive.ofMul (QuotientGroup.mk' (center Q) x)) =
      (centerCoordinate Q ⟨x^2,IsExtraspecial.square_mem_center x⟩).toAdd :=
  BinarySquareForm.quadraticForm_coordinates (projection Q) (projection_ker Q)
    (projection_surjective Q) (center_square Q) (centerCoordinate Q).toMonoidHom x

@[simp] theorem form_mk_eq_zero (x : Q) :
    form Q (Additive.ofMul (QuotientGroup.mk' (center Q) x)) = 0 ↔ x^2=1 := by
  rw [form_mk]
  change centerCoordinate Q _ = 1 ↔ _
  rw [(centerCoordinate Q).map_eq_one_iff]
  exact Subtype.ext_iff

theorem commutator_mem_center (x y : Q) : ⁅x,y⁆ ∈ center Q :=
  BinarySquareForm.commutator_mem_center (projection Q) (projection_ker Q) x y

theorem polar_mk (x y : Q) :
    (form Q).polarBilin (Additive.ofMul (QuotientGroup.mk' (center Q) x))
      (Additive.ofMul (QuotientGroup.mk' (center Q) y)) =
      (centerCoordinate Q ⟨⁅x,y⁆,commutator_mem_center Q x y⟩).toAdd :=
  BinarySquareForm.polarBilin_coordinates (projection Q) (projection_ker Q)
    (projection_surjective Q) (center_square Q) (centerCoordinate Q).toMonoidHom x y

theorem polar_nondegenerate : (form Q).polarBilin.Nondegenerate := by
  have hsep : (form Q).polarBilin.SeparatingLeft := by
    intro v hv
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center Q) v.toMul
    have he : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul hx.symm
    subst v
    have hcentral : x ∈ center Q := by
      apply mem_center_iff.mpr
      intro y
      have hh := hv (Additive.ofMul (QuotientGroup.mk' (center Q) y))
      rw [polar_mk] at hh
      have hc : (⟨⁅x,y⁆,commutator_mem_center Q x y⟩ : center Q) = 1 := by
        apply (centerCoordinate Q).injective
        exact (congrArg Multiplicative.ofAdd hh).trans (centerCoordinate Q).map_one.symm
      exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hc)).symm
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff x).mpr hcentral)
  refine ⟨hsep,?_⟩
  intro v hv
  apply hsep v
  intro w
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]
  exact hv w

private theorem fixes_center (a : MulAut Q) (z : center Q) : a (z:Q) = z := by
  let e := centerCongr a
  have he : e z = z := by
    by_cases hz : z=1
    · simp [hz]
    · obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp
        (IsExtraspecial.center_order_p 2 Q)
      have hn : e z ≠ 1 := fun h => hz (e.injective (h.trans e.map_one.symm))
      exact (hw (e z) hn).trans (hw z hz).symm
  exact congrArg Subtype.val he

theorem form_invariant (a : MulAut Q) (v : Q ⧸ center Q) :
    form Q (Additive.ofMul (quotientAut (center Q) a v)) = form Q (Additive.ofMul v) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  rw [quotientAut_apply_mk,form_mk,form_mk]
  congr 2
  apply Subtype.ext
  change (a x)^2=x^2
  rw [←map_pow]
  exact fixes_center Q a ⟨x^2,IsExtraspecial.square_mem_center x⟩

noncomputable def linearAction : MulAut Q →* (Space Q ≃ₗ[ZMod 2] Space Q) where
  toFun a := {
    toFun := fun v => Additive.ofMul (quotientAut (center Q) a v.toMul)
    invFun := fun v => Additive.ofMul ((quotientAut (center Q) a).symm v.toMul)
    left_inv := fun v => (quotientAut (center Q) a).symm_apply_apply v
    right_inv := fun v => (quotientAut (center Q) a).apply_symm_apply v
    map_add' := fun v w => congrArg Additive.ofMul (map_mul (quotientAut (center Q) a) v.toMul w.toMul)
    map_smul' := by
      intro r v
      have binary : ∀ r : ZMod 2, r=0 ∨ r=1 := by decide
      rcases binary r with rfl | rfl
      · simp only [RingHom.id_apply,zero_smul]
        exact congrArg Additive.ofMul (map_one (quotientAut (center Q) a))
      · simp only [one_smul,RingHom.id_apply] }
  map_one' := by
    ext v
    exact congrArg (fun e : MulAut (Q ⧸ center Q) => Additive.ofMul (e v.toMul))
      (map_one (quotientAut (center Q)))
  map_mul' a b := by
    ext v
    exact congrArg (fun e : MulAut (Q ⧸ center Q) => Additive.ofMul (e v.toMul))
      (map_mul (quotientAut (center Q)) a b)

@[simp] theorem linearAction_apply (a : MulAut Q) (v : Q ⧸ center Q) :
    linearAction Q a (Additive.ofMul v) = Additive.ofMul (quotientAut (center Q) a v) := rfl

noncomputable def isometryAction : MulAut Q →* (form Q).isometrySubgroup :=
  (linearAction Q).codRestrict (form Q).isometrySubgroup
    (fun a => (QuadraticMap.mem_isometrySubgroup _ _).mpr (fun v => form_invariant Q a v.toMul))

@[simp] theorem isometryAction_apply (a : MulAut Q) (v : Q ⧸ center Q) :
    (isometryAction Q a).val (Additive.ofMul v) = Additive.ofMul (quotientAut (center Q) a v) := rfl

theorem isometryAction_eq_one_iff (a : MulAut Q) :
    isometryAction Q a = 1 ↔ quotientAut (center Q) a = 1 := by
  constructor
  · intro h
    ext v
    exact congrArg Additive.toMul (congrArg (fun b : (form Q).isometrySubgroup =>
      b.val (Additive.ofMul v)) h)
  · intro h
    apply Subtype.ext
    ext v
    change Additive.ofMul (quotientAut (center Q) a v.toMul) = v
    rw [h]
    rfl

theorem singular_displacement (a : MulAut Q) (hs : ∀ x : Q, (a x * x⁻¹)^2=1) :
    ∀ v, form Q ((isometryAction Q a).val v-v)=0 := by
  intro v
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (center Q) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul hx.symm
  rw [hv,isometryAction_apply,quotientAut_apply_mk,←ofMul_div,←map_div]
  exact (form_mk_eq_zero Q _).mpr (by simpa only [div_eq_mul_inv] using hs x)

/-- The original subgroup's image in the actual central quotient. -/
noncomputable def imageSpace (A : Subgroup Q) : Submodule (ZMod 2) (Space Q) where
  carrier := {v | v.toMul ∈ A.map (QuotientGroup.mk' (center Q))}
  zero_mem' := (A.map (QuotientGroup.mk' (center Q))).one_mem
  add_mem' := fun hx hy => (A.map (QuotientGroup.mk' (center Q))).mul_mem hx hy
  smul_mem' := by
    intro a v hv
    have binary : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide
    rcases binary a with rfl | rfl
    · rw [zero_smul]
      exact (A.map (QuotientGroup.mk' (center Q))).one_mem
    · simpa only [one_smul] using hv

variable [Finite Q]

omit [Finite Q] in
theorem imageSpace_card (A : Subgroup Q) (hz : center Q ≤ A) :
    2 * Nat.card (imageSpace Q A) = Nat.card A := by
  let e : imageSpace Q A ≃ A.map (QuotientGroup.mk' (center Q)) := {
    toFun := fun v => ⟨v.val.toMul,v.property⟩
    invFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map A (QuotientGroup.mk' (center Q))
  rwa [QuotientGroup.ker_mk',inf_eq_right.mpr hz,IsExtraspecial.center_order_p 2 Q] at hh

omit [Finite Q] in
theorem imageSpace_singular (A : Subgroup Q) [IsElementaryAbelian 2 A] :
    ∀ v ∈ imageSpace Q A, form Q v=0 := by
  intro v hv
  obtain ⟨x,hx,he⟩ := hv
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul he.symm
  rw [hv,form_mk_eq_zero]
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem imageSpace_finrank (A : Subgroup Q) (hz : center Q ≤ A)
    (n : ℕ) (ha : Nat.card A = 2^(n+1)) :
    Module.finrank (ZMod 2) (imageSpace Q A) = n := by
  have hh := imageSpace_card Q A hz
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := imageSpace Q A)
  rw [hc,Nat.card_zmod,ha,pow_succ] at hh
  have he : 2 ^ Module.finrank (ZMod 2) (imageSpace Q A) = 2^n := by omega
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) he

theorem space_finrank (n : ℕ) (hc : Nat.card Q = 2^(n+1)) :
    Module.finrank (ZMod 2) (Space Q) = n := by
  have hh := card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [IsExtraspecial.center_order_p 2 Q,hc,pow_succ] at hh
  have he : Nat.card (Space Q)=2^n := by change Nat.card (Q ⧸ center Q)=2^n; omega
  have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space Q)
  rw [he,Nat.card_zmod] at hf
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hf.symm

omit [Finite Q] in
/-- Passage to the central quotient preserves the join of the original subgroups. -/
theorem imageSpace_sup (A B : Subgroup Q) :
    imageSpace Q (A ⊔ B) = imageSpace Q A ⊔ imageSpace Q B := by
  let := IsExtraspecial.quotient_elementary_abelian 2 Q
  let φ : Subgroup (Q ⧸ center Q) ≃o Submodule (ZMod 2) (Space Q) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  have he (C : Subgroup Q) : imageSpace Q C = φ (C.map (QuotientGroup.mk' (center Q))) := rfl
  rw [he,he,he,←φ.map_sup,Subgroup.map_sup]

omit [Finite Q] in
theorem imageSpace_top : imageSpace Q ⊤ = ⊤ := by
  ext v
  change v.toMul ∈ (⊤ : Subgroup Q).map (QuotientGroup.mk' (center Q)) ↔ True
  rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective (center Q))]
  trivial

end Theory.GroupTheory.ExtraspecialSquare
