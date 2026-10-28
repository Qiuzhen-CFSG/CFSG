module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import Theory.SpecificGroups.SU3.SylowOmega
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Central roots and the Weyl commutator torus in SU₃

The first omega subgroup of the literal Hermitian root range is the additive
fixed field in the upper-right matrix entry. The full diagonal torus has
commutator with the Weyl involution equal to the fixed-field torus: its
parameter is the field norm. A six-factor root–Weyl word supplies every
fixed-field torus element, and squaring in the finite fixed field supplies
its transitive action on the nonzero central roots. Projection equations
retain the actual SU₃ and PSU₃ carriers, including the scalar center.

Source: GLS4, Chapter 4, Lemma 3.2(d),(h), and Chapter 2, Section 16.
-/

open Matrix Subgroup BenderSuzuki.External
open BenderSuzuki.MatrixGroups
namespace BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

@[expose] public def specialCentral : Multiplicative (fixedField J) →* J.specialSubgroup :=
  (hermitianUnipotentSU J hJ).comp (centralCoord J)

omit [CharP E 2] in
public theorem specialRoot_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

theorem coord_square_iff (x : hermitianUnipotentCoord J) :
    x ^ 2 = 1 ↔ ∃ b : Multiplicative (fixedField J), centralCoord J b = x := by
  rw [EvenSemilinear.square_eq_one_iff_first_zero]
  constructor
  · intro hx
    have hb : J.conj x.val.2 = x.val.2 := by
      have hp := x.property
      rw [hx, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    exact ⟨.ofAdd ⟨x.val.2, hb⟩, Subtype.ext (Prod.ext hx.symm rfl)⟩
  · rintro ⟨b, rfl⟩
    rfl

theorem omega_range {G : Type*} [Group G]
    (f : hermitianUnipotentCoord J →* G) (hf : Function.Injective f) :
    omegaOneAmbient f.range = (f.comp (centralCoord J)).range := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro _ ⟨x, rfl⟩ hx
    have hs : x ^ 2 = 1 := hf (by simpa only [map_pow, map_one] using hx)
    obtain ⟨b, rfl⟩ := (coord_square_iff J x).mp hs
    exact ⟨b, rfl⟩
  · rintro _ ⟨b, rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl
    · exact ⟨centralCoord J b, rfl⟩
    · change f (centralCoord J b) ^ 2 = 1
      rw [← map_pow, (coord_square_iff J _).mpr ⟨b, rfl⟩, map_one]

public theorem special_omega : omegaOneAmbient (specialRoot J hJ) = (specialCentral J hJ).range :=
  omega_range J _ (specialRoot_injective J hJ)

public theorem projective_omega : omegaOneAmbient (projectiveRoot J hJ) = (centralMap J hJ).range :=
  omega_range J _ (EvenInner.root_injective J hJ)

public theorem projection_central (b : Multiplicative (fixedField J)) :
    J.specialToProjective (specialCentral J hJ b) = centralMap J hJ b := by
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  rfl

omit [CharP E 2] in
public theorem projection_weyl : J.specialToProjective (hermitianWeylSU J hJ) =
    hermitianWeylPSU J hJ := by
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  rfl

public theorem projection_rootGenerated :
    (rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ)).map
      J.specialToProjective =
      rootGenerated (projectiveRoot J hJ) (hermitianWeylPSU J hJ) := by
  rw [rootGenerated, rootGenerated, Subgroup.map_sup, MonoidHom.map_zpowers, projection_weyl,
    special_omega, projective_omega, ← MonoidHom.range_comp]
  congr 1
  congr 1
  apply MonoidHom.ext
  intro b
  exact projection_central J hJ b

@[expose] public def fixedTorus : (fixedField J)ˣ →* J.specialSubgroup :=
  (hermitianTorusSU J hJ).comp (Units.map (fixedField J).subtype.toMonoidHom)

omit [CharP E 2] in
public theorem weyl_inv : (hermitianWeylSU J hJ)⁻¹ = hermitianWeylSU J hJ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylSU, hermitianWeylGL, hermitianWeylMatrix,
      Matrix.mul_apply, Fin.sum_univ_three]

omit [CharP E 2] in
theorem weyl_ne_one : hermitianWeylSU J hJ ≠ 1 := by
  intro h
  have h' := congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h
  exact one_ne_zero h'

public theorem central_val (b : Multiplicative (fixedField J)) :
    (specialCentral J hJ b).val.val = !![1,0,(b.toAdd:E);0,1,0;0,0,1] := by
  change !![1,0,(b.toAdd:E);0,1,-J.conj 0;0,0,1] = _
  simp

omit [CharP E 2] in
theorem fixedTorus_val (a : (fixedField J)ˣ) :
    (fixedTorus J hJ a).val.val =
      !![((a : fixedField J) : E)⁻¹,0,0;0,1,0;0,0,((a : fixedField J) : E)] := by
  have ha : ((a : fixedField J) : E) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedTorus, hermitianTorusSU, hermitianTorusGL, hermitianTorusMatrix,
      fixedField_mem, ha]

open scoped commutatorElement

omit [CharP E 2] in
theorem torus_commutator (k : Eˣ) :
    ⁅hermitianTorusSU J hJ k, hermitianWeylSU J hJ⁆ =
      fixedTorus J hJ ((inverseNorm J k)⁻¹) := by
  rw [commutatorElement_def, weyl_inv, ← map_inv]
  apply Subtype.ext
  apply Units.ext
  change (hermitianTorusMatrix J k * hermitianWeylMatrix *
    hermitianTorusMatrix J k⁻¹ * hermitianWeylMatrix) = _
  rw [fixedTorus_val]
  have hk := k.ne_zero
  have hc := (map_ne_zero J.conj).mpr hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, hermitianWeylMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, inverseNorm_val, Units.val_inv_eq_inv_val,
      mul_comm]
  field_simp

theorem torus_word (a : (fixedField J)ˣ) :
    specialCentral J hJ (.ofAdd ((a : fixedField J)⁻¹)) * hermitianWeylSU J hJ *
      specialCentral J hJ (.ofAdd (a : fixedField J)) * hermitianWeylSU J hJ *
      specialCentral J hJ (.ofAdd ((a : fixedField J)⁻¹)) * hermitianWeylSU J hJ =
        fixedTorus J hJ a := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [central_val, central_val, fixedTorus_val]
  change (!![1,0,((a : fixedField J):E)⁻¹;0,1,0;0,0,1] * hermitianWeylMatrix *
    !![1,0,((a : fixedField J):E);0,1,0;0,0,1] * hermitianWeylMatrix *
    !![1,0,((a : fixedField J):E)⁻¹;0,1,0;0,0,1] * hermitianWeylMatrix) = _
  have ha : ((a : fixedField J) : E) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      CharTwo.neg_eq, CharTwo.add_self_eq_zero, ha]

public theorem fixedTorus_le_generated : (fixedTorus J hJ).range ≤
    rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ) := by
  let H := rootGenerated (specialRoot J hJ) (hermitianWeylSU J hJ)
  have hU (b) : specialCentral J hJ b ∈ H := by
    apply Subgroup.mem_sup_left
    rw [special_omega]
    exact ⟨b, rfl⟩
  have hW : hermitianWeylSU J hJ ∈ H := Subgroup.mem_sup_right (mem_zpowers _)
  rintro _ ⟨a, rfl⟩
  rw [← torus_word]
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hU _) hW)
    (hU _)) hW) (hU _)) hW

theorem fixedTorus_action (a : (fixedField J)ˣ) (b : fixedField J) :
    fixedTorus J hJ a * specialCentral J hJ (.ofAdd b) * (fixedTorus J hJ a)⁻¹ =
      specialCentral J hJ (.ofAdd (((a : fixedField J)⁻¹)^2 * b)) := by
  have hm : fixedTorus J hJ a * specialCentral J hJ (.ofAdd b) =
      specialCentral J hJ (.ofAdd (((a : fixedField J)⁻¹)^2 * b)) * fixedTorus J hJ a := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [fixedTorus_val, central_val, central_val]
    have ha : ((a : fixedField J) : E) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
  rw [hm, mul_assoc, mul_inv_cancel, mul_one]

public theorem fixedTorus_transitive [Finite E] (b c : fixedField J) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ a : (fixedField J)ˣ,
      fixedTorus J hJ a * specialCentral J hJ (.ofAdd b) * (fixedTorus J hJ a)⁻¹ =
        specialCentral J hJ (.ofAdd c) := by
  have hsurj : Function.Surjective (fun a : fixedField J => a ^ 2) :=
    Finite.surjective_of_injective fun _ _ h => CharTwo.sq_inj.mp h
  obtain ⟨a, ha⟩ := hsurj (c / b)
  change a ^ 2 = c / b at ha
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at ha
    exact div_ne_zero hc hb ha.symm
  refine ⟨(Units.mk0 a ha0)⁻¹, ?_⟩
  rw [fixedTorus_action]
  change specialCentral J hJ (.ofAdd ((a⁻¹)⁻¹ ^ 2 * b)) = _
  rw [inv_inv, ha, div_mul_cancel₀ _ hb]

omit [CharP E 2] in
public theorem special_commutator [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ⁅specialTorus J hJ, zpowers (hermitianWeylSU J hJ)⁆ = (fixedTorus J hJ).range := by
  classical
  apply le_antisymm
  · rw [commutator_le]
    rintro _ ⟨k, rfl⟩ s hs
    have ho : orderOf (hermitianWeylSU J hJ) = 2 := by
      apply (orderOf_eq_prime_iff).mpr
      refine ⟨?_, weyl_ne_one J hJ⟩
      rw [pow_two]
      conv_lhs => lhs; rw [← weyl_inv J hJ]
      exact inv_mul_cancel _
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have hi' := Finset.mem_range.mp hi
    interval_cases i
    · simp
    · simp only [pow_one, torus_commutator]
      exact ⟨_, rfl⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := inverseNorm_surjective J hcard hfixed a⁻¹
    have hm := commutator_mem_commutator
      (show hermitianTorusSU J hJ k ∈ specialTorus J hJ from ⟨k, rfl⟩)
      (mem_zpowers (hermitianWeylSU J hJ))
    rwa [torus_commutator, hk, inv_inv] at hm

omit [CharP E 2] in
public theorem projection_root (x : hermitianUnipotentCoord J) :
    J.specialToProjective (hermitianUnipotentSU J hJ x) = hermitianUnipotentPSU J hJ x := by
  apply Subtype.ext
  rw [J.specialToProjective_apply_val]
  rfl

omit [CharP E 2] in
public theorem projection_torus : (specialTorus J hJ).map J.specialToProjective = projectiveTorus J hJ := by
  rw [specialTorus, projectiveTorus, ← MonoidHom.range_comp]
  congr 1
  apply MonoidHom.ext
  intro k
  apply Subtype.ext
  rw [MonoidHom.comp_apply, J.specialToProjective_apply_val]
  rfl


end BenderSuzuki.ZD.RankOneModelGeometry.UnitaryStandardRoots
