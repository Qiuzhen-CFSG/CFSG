module
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# Recognizing PSL3(4) graph and field cosets from two cubic signs

For an automorphism preserving the standard unipotent group, displacement on
its Borel quotient detects the coefficient automorphism through the root torus.
Equality of GL determinants detects equality in the outer diagonal quotient.
Consequently a mixed graph-field actor fixes that quotient, while the source
requires inversion of a nontrivial outer cubic. The two factor signs determine
the graph or square-field coset, and inner changes of coordinates preserve it.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136;
GLS3, Theorem 2.5.12 and the standard matrix automorphisms of Section 2.7.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.RootTorusControl Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Four.SylowCosetRecognition
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem unipotent_centralizes :
    unipotent F ≤ centralizer (projectiveCenter F : Set PSL(3,F)) := by
  intro u hu
  apply mem_centralizer_iff.mpr
  rintro z hz
  rw [projectiveCenter_eq_mapped_center] at hz
  obtain ⟨z,hz,rfl⟩ := hz
  exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u,hu⟩)).symm

/-- Root-torus displacement detects the literal coefficient automorphism. -/
theorem coefficient_of_rootTorus_displacement
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (u v : Fˣ)
    (h : projectiveActor F m σ ε (rootTorus F u) * (rootTorus F v)⁻¹ ∈ unipotent F) :
    Units.map σ.toMonoidHom u = v := by
  obtain ⟨a,ha,he⟩ := actor_rootTorus_factor F m σ ε hU u
  have hz : rootTorus F (Units.map σ.toMonoidHom u * v⁻¹) ∈ unipotent F := by
    have hh := (unipotent F).mul_mem ((unipotent F).inv_mem ha) h
    simpa only [he,map_mul,map_inv,←mul_assoc,inv_mul_cancel,one_mul] using hh
  exact mul_inv_eq_one.mp (rootTorus_eq_one_of_centralizes F _ (unipotent_centralizes F hz))

/-- Fixing the actual Borel quotient removes the coefficient factor. -/
theorem coefficient_eq_one_of_borel_fixed
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (h : ∀ x ∈ borel F, projectiveActor F m σ ε x*x⁻¹ ∈ unipotent F) : σ = 1 := by
  apply RingEquiv.ext
  intro x
  by_cases hx : x=0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have he := coefficient_of_rootTorus_displacement F m σ ε hU u u
      (h _ (rootTorus_le_borel F ⟨u,rfl⟩))
    exact congrArg Units.val he

/-- Inverting the Borel quotient gives square Frobenius over the field of order four. -/
theorem coefficient_square_of_borel_inverted (hF : Nat.card F=4)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (h : ∀ x ∈ borel F, projectiveActor F m σ ε x*x ∈ unipotent F) :
    ∀ x : F, σ x=x^2 := by
  intro x
  by_cases hx : x=0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have he := coefficient_of_rootTorus_displacement F m σ ε hU u u⁻¹
      (by simpa only [map_inv,inv_inv] using h _ (rootTorus_le_borel F ⟨u,rfl⟩))
    have hc : u^3=1 := by
      have hk : Nat.card Fˣ=3 := by rw [Nat.card_units,hF]
      simpa only [hk] using (pow_card_eq_one' : u^Nat.card Fˣ=1)
    have hi : u⁻¹=u^2 := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [←pow_succ] using hc
    exact (congrArg Units.val he).trans (congrArg Units.val hi)


open Matrix.PSL3.OuterSolvable.OddPrimeCoverage


omit [Finite F] [CharP F 2] in
private theorem linear_outer_eq_of_det (a b : GL (Fin 3) F)
    (h : GeneralLinearGroup.det a = GeneralLinearGroup.det b) :
    linearOuterAction F a = linearOuterAction F b := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply det_ker_le_linearOuterAction_ker F
  change GeneralLinearGroup.det (a*b⁻¹) = 1
  rw [map_mul,map_inv,h,mul_inv_cancel]

omit [Finite F] [CharP F 2] in
private theorem linear_outer_commute (a b : GL (Fin 3) F) :
    Commute ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F a)) ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)) := by
  exact congrArg Subtype.val ((innerDiagonalOuter_isMulCommutative F).is_comm.comm
    (⟨linearOuterAction F a, a,rfl⟩ : innerDiagonalOuter F)
    (⟨linearOuterAction F b, b,rfl⟩ : innerDiagonalOuter F))

omit [Finite F] [CharP F 2] in
private theorem inverseTranspose_det (b : GL (Fin 3) F) :
    GeneralLinearGroup.det (inverseTransposeGL F b) = (GeneralLinearGroup.det b)⁻¹ := by
  apply Units.ext
  exact (Matrix.det_transpose b.inv).trans (congrArg Units.val (map_inv GeneralLinearGroup.det b))

omit [Finite F] [CharP F 2] in
/-- The mixed graph-field actor fixes the genuine outer diagonal quotient. -/
theorem outer_field_graph_commute (hF : Nat.card F=4) (σ : F ≃+* F)
    (hσ : ∀ x : F, σ x=x^2) (b : GL (Fin 3) F) :
    Commute ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F)) ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)) := by
  have hd : GeneralLinearGroup.det
      (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F b)) =
      GeneralLinearGroup.det b := by
    rw [GeneralLinearGroup.map_det,inverseTranspose_det]
    have he (u : Fˣ) : Units.map σ.toMonoidHom u=u^2 := Units.ext (hσ u)
    change Units.map σ.toMonoidHom (GeneralLinearGroup.det b)⁻¹=GeneralLinearGroup.det b
    rw [he]
    have hcube : (GeneralLinearGroup.det b)^3=1 := by
      have hk : Nat.card Fˣ=3 := by rw [Nat.card_units,hF]
      simpa only [hk] using (pow_card_eq_one' : (GeneralLinearGroup.det b)^Nat.card Fˣ=1)
    apply inv_injective
    simp only [←inv_pow,inv_inv]
    symm
    apply inv_eq_of_mul_eq_one_left
    simpa only [←pow_succ] using hcube
  have hswap : (Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F) * linearConj F b =
      linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F b)) *
        (Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F) := by
    rw [mul_assoc, graph_linearConj, ←mul_assoc, field_linearConj, mul_assoc]
  change (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) _ * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) _ = (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) _ * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) _
  rw [← map_mul,hswap,map_mul]
  exact congrArg (· * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F))
    (linear_outer_eq_of_det F _ b hd)

omit [Finite F] [CharP F 2] in
private theorem mixed_outer_commute (hF : Nat.card F=4) (m : GL (Fin 3) F)
    (σ : F ≃+* F) (hσ : ∀ x : F, σ x=x^2) (b : GL (Fin 3) F) :
    Commute ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (projectiveActor F m σ true))
      ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)) := by
  have he : projectiveActor F m σ true =
      linearConj F (m * GeneralLinearGroup.map σ.toRingHom (reversalGL F)) *
        (Matrix.PSL3.OuterSolvable.fieldAction F σ * graph F) := by
    simp only [projectiveActor,↓reduceIte,oppositionGraph,map_mul]
    rw [mul_assoc,←mul_assoc (Matrix.PSL3.OuterSolvable.fieldAction F σ),field_linearConj]
    group
  rw [he,map_mul]
  exact (linear_outer_commute F _ b).mul_left (outer_field_graph_commute F hF σ hσ b)

omit [Finite F] [CharP F 2] in
private theorem cubic_commute_not_inverted {H : Type*} [Group H] {a b : H}
    (hb3 : b^3=1) (hb : b≠1) (hc : Commute a b)
    (hi : a*b*a⁻¹*b=1) : False := by
  have hb2 : b*b=1 := by simpa only [hc.eq,mul_inv_cancel_right] using hi
  apply hb
  have hh : b^3=b := by rw [pow_succ,pow_two,hb2,one_mul]
  exact hh.symm.trans hb3

/-- The component quotient and opposite outer cubic recognize the graph coset. -/
theorem graph_of_factor_signs (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (hfix : ∀ x ∈ borel F, projectiveActor F m σ ε x*x⁻¹ ∈ unipotent F)
    (b : GL (Fin 3) F) (hb3 : ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b))^3=1)
    (hb : (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)≠1)
    (hinv : (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (projectiveActor F m σ ε) * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b) *
      ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (projectiveActor F m σ ε))⁻¹ * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)=1) :
    ∃ a : GL (Fin 3) F, projectiveActor F m σ ε=linearConj F a*graph F := by
  have hσ := coefficient_eq_one_of_borel_fixed F m σ ε hU hfix
  subst σ
  cases ε with
  | false =>
    have he : projectiveActor F m 1 false=linearConj F m := by simp [projectiveActor]
    rw [he] at hinv
    exact False.elim (cubic_commute_not_inverted hb3 hb (linear_outer_commute F m b) hinv)
  | true =>
    exact ⟨m*reversalGL F, by simp [projectiveActor,oppositionGraph,map_mul,mul_assoc]⟩

/-- Inverting both cubic factors recognizes the square-field coset. -/
theorem field_of_factor_signs (hF : Nat.card F=4)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hU : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F)
    (hinverted : ∀ x ∈ borel F, projectiveActor F m σ ε x*x ∈ unipotent F)
    (b : GL (Fin 3) F) (hb3 : ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b))^3=1)
    (hb : (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)≠1)
    (hinv : (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (projectiveActor F m σ ε) * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b) *
      ((QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (projectiveActor F m σ ε))⁻¹ * (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))) (linearConj F b)=1) :
    (∀ x : F, σ x=x^2) ∧ ∃ a : GL (Fin 3) F,
      projectiveActor F m σ ε=linearConj F a*Matrix.PSL3.OuterSolvable.fieldAction F σ := by
  have hσ := coefficient_square_of_borel_inverted F hF m σ ε hU hinverted
  refine ⟨hσ,?_⟩
  cases ε with
  | false => exact ⟨m,by simp [projectiveActor]⟩
  | true => exact False.elim (cubic_commute_not_inverted hb3 hb
      (mixed_outer_commute F hF m σ hσ b) hinv)


end Matrix.PSL3Four.SylowCosetRecognition

namespace Matrix.PSL3Four.SylowCosetRecognition
open Matrix.PSL3.OuterSolvable Subgroup
open scoped MatrixGroups
variable (F : Type*) [Field F]

/-- Inner changes of projective coordinates preserve every displayed linear coset. -/
theorem linear_coset_of_outer_eq (α β δ : MulAut PSL(3,F))
    (he : QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) α =
      QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) β)
    (a : Matrix.GeneralLinearGroup (Fin 3) F) (hβ : β=linearConj F a*δ) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 3) F, α=linearConj F b*δ := by
  have hk : α*β⁻¹ ∈ MulAut.innerSubgroup PSL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (α*β⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  obtain ⟨c,hc⟩ := inner_le_innerDiagonal F hk
  refine ⟨c*a,?_⟩
  rw [map_mul,hc,mul_assoc (α*β⁻¹),←hβ,inv_mul_cancel_right]

end Matrix.PSL3Four.SylowCosetRecognition

