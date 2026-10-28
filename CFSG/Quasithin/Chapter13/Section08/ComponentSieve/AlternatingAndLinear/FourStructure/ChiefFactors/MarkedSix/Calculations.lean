module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Bounds
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Calculations.Finite

/-!
# Rank and fixed-codimension bounds in the exterior square

Identify the genuine exterior square with the six minor coordinates
01, 02, 03, 12, 13, 23. The radical of the standard plane consists of
upper-block-unipotent matrices, faithfully parametrized by four binary entries.
Its exterior action is the operator `Calculations.step`.

Quadraticity forces the parameter vectors to be mutually perpendicular for
the determinant polar form. Two independent vectors have just four common
perpendiculars, so a quadratic subgroup has order at most four. A nonidentity
operator fixes at most sixteen vectors, and two distinct nonidentity operators
have at most eight common fixed vectors. Cardinality and rank-nullity give the
strict fixed-codimension bound. These finite counts are kernel-checked in
`Calculations.Finite`; the identifications and injections used here are proved.
Linear conjugation transports both conclusions to every binary two-plane.

The exterior coordinate construction follows `Alignment.ExteriorGeometry`,
using the attributed ATLAS bivector formulas and basis theorem. No comparison
with a deleted permutation module or offender catalogue is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed p.961 (PDF p.978), the intrinsic
calculation needed in the application of B.3.2(6), printed p.84.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
open Alignment Representation Representation.BinaryOffender
open Atlas.Order20160A8.Bivectors
open Calculations

private noncomputable def coordinates : ExteriorSquare →ₗ[ZMod 2] Six :=
  LinearMap.pi fun i => exteriorPower.pairingDual (ZMod 2) NaturalSpace 2
    (exteriorPower.ιMulti (ZMod 2) 2
      ![LinearMap.proj (first i), LinearMap.proj (second i)])

private theorem coordinates_wedge (v : Fin 2 → NaturalSpace) :
    coordinates (exteriorPower.ιMulti (ZMod 2) 2 v) = wedge (v 0) (v 1) := by
  ext i
  fin_cases i <;>
    simp [coordinates, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, first, second, wedge]

private theorem coordinates_surjective : Function.Surjective coordinates := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun (ZMod 2) (Fin 6)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨exteriorPower.ιMulti (ZMod 2) 2
    ![Pi.single (first i) 1, Pi.single (second i) 1], ?_⟩
  simp only [coordinates_wedge, Matrix.cons_val_zero, Matrix.cons_val_one,
    wedge_basis, Pi.basisFun_apply]

private noncomputable def coordinatesEquiv : ExteriorSquare ≃ₗ[ZMod 2] Six :=
  LinearEquiv.ofBijective coordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using exteriorSquare_finrank)).mpr coordinates_surjective,
    coordinates_surjective⟩


private def standardPlane : Submodule (ZMod 2) NaturalSpace where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩; simp_all
  smul_mem' := by rintro a x ⟨hx, hx'⟩; simp_all

private def parameters (g : BinaryLinear.GL NaturalSpace) : Four :=
  ![g (Pi.single 2 1) 0, g (Pi.single 3 1) 0,
    g (Pi.single 2 1) 1, g (Pi.single 3 1) 1]

private def blockMap (a : Four) : NaturalSpace →ₗ[ZMod 2] NaturalSpace where
  toFun v := ![v 0 + a 0 * v 2 + a 1 * v 3,
    v 1 + a 2 * v 2 + a 3 * v 3, v 2, v 3]
  map_add' v w := by
    ext i; fin_cases i <;> simp [mul_add] <;> ring
  map_smul' c v := by
    ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

private theorem radical_block (g : BinaryLinear.GL NaturalSpace)
    (hg : g ∈ BinaryLinear.radical standardPlane) :
    g.toLinearMap = blockMap (parameters g) := by
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro i
  have h0 := hg.1 (Pi.single 0 1) (show Pi.single 0 1 ∈ standardPlane by simp [standardPlane])
  have h1 := hg.1 (Pi.single 1 1) (show Pi.single 1 1 ∈ standardPlane by simp [standardPlane])
  have h2 := hg.2 (Pi.single 2 1)
  have h3 := hg.2 (Pi.single 3 1)
  change (g (Pi.single 2 1) 2 - 1 = 0 ∧ g (Pi.single 2 1) 3 - 0 = 0) at h2
  change (g (Pi.single 3 1) 2 - 0 = 0 ∧ g (Pi.single 3 1) 3 - 1 = 0) at h3
  simp only [sub_eq_zero] at h2 h3
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [Pi.basisFun_apply, blockMap, parameters, h0, h1, h2.1, h2.2, h3.1, h3.2]

private theorem parameters_injective (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane) :
    Function.Injective (fun g : A => parameters g) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  rw [radical_block g (hA g.property), radical_block h (hA h.property)]
  exact congrArg blockMap he

private theorem parameters_one : parameters 1 = 0 := by
  ext i; fin_cases i <;> simp [parameters]

private def stepMap (a : Four) : Six →ₗ[ZMod 2] Six where
  toFun := step a
  map_add' x y := by
    ext j; fin_cases j <;> simp [step, mul_add] <;> ring
  map_smul' c x := by
    ext j; fin_cases j <;> simp [step, smul_eq_mul] <;> ring

set_option maxHeartbeats 4000000 in
private theorem coordinates_block (a : Four) (v : ExteriorSquare) :
    coordinates (exteriorPower.map 2 (blockMap a) v) = step a (coordinates v) := by
  suffices coordinates.comp (exteriorPower.map 2 (blockMap a)) =
      (stepMap a).comp coordinates from LinearMap.congr_fun this v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, coordinates_wedge]
  change wedge (blockMap a (v 0)) (blockMap a (v 1)) = step a (wedge (v 0) (v 1))
  ext j; fin_cases j <;>
    simp [blockMap, wedge, step, CharTwo.sub_eq_add] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 by decide]

private theorem coordinates_action (g : BinaryLinear.GL NaturalSpace)
    (hg : g ∈ BinaryLinear.radical standardPlane) (v : ExteriorSquare) :
    coordinatesEquiv (modelAction g v) = step (parameters g) (coordinatesEquiv v) := by
  change coordinates (exteriorPower.map 2 g.toLinearMap v) = _
  rw [radical_block g hg]
  exact coordinates_block _ _

private theorem parameters_ne_zero (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane) {a : A} (ha : a ≠ 1) :
    parameters a ≠ 0 := by
  intro hz
  exact ha (parameters_injective A hA (hz.trans parameters_one.symm))

private theorem quadratic_pairing (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane) (hq : IsQuadratic modelAction A)
    (a b : A) : pairing (parameters a) (parameters b) = 0 := by
  have h := congrArg coordinatesEquiv
    (hq a a.property b b.property (coordinatesEquiv.symm (Pi.single 5 1)))
  simp only [coordinates_action a (hA a.property), coordinates_action b (hA b.property),
    map_sub, LinearEquiv.apply_symm_apply] at h
  have hc := congrFun h 0
  simp [step, CharTwo.sub_eq_add] at hc
  dsimp [pairing]
  linear_combination (norm := ring_nf) hc
  simp [show (2 : ZMod 2) = 0 by decide]

private theorem card_le_two {X : Type*} (a b : X)
    (h : ∀ x : X, x = a ∨ x = b) : Nat.card X ≤ 2 := by
  classical
  let f : Bool → X := fun t => if t then a else b
  have hf : Function.Surjective f := by
    intro x
    rcases h x with hx | hx
    · exact ⟨true, hx.symm⟩
    · exact ⟨false, hx.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

private theorem standard_quadratic_rank
    (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane) (hq : IsQuadratic modelAction A) :
    rank A ≤ 2 := by
  classical
  suffices hc : Nat.card A ≤ 4 by
    exact (Nat.log_monotone hc).trans (by decide : Nat.log 2 4 ≤ 2)
  by_cases hbot : A = ⊥
  · simp [hbot]
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  by_cases hsmall : ∀ b : A, b = 1 ∨ b = a
  · exact (card_le_two 1 a hsmall).trans (by decide)
  push Not at hsmall
  obtain ⟨b, hb, hba⟩ := hsmall
  let f : A → {c : Four // pairing (parameters a) c = 0 ∧
      pairing (parameters b) c = 0} :=
    fun c => ⟨parameters c, quadratic_pairing A hA hq a c,
      quadratic_pairing A hA hq b c⟩
  have hf : Function.Injective f := by
    intro c d h
    exact parameters_injective A hA (congrArg Subtype.val h)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := {c : Four // pairing (parameters a) c = 0 ∧
    pairing (parameters b) c = 0}), perp_card _ _ (parameters_ne_zero A hA ha)
    (parameters_ne_zero A hA hb) (fun h => hba (parameters_injective A hA h.symm))] at hc
  exact hc

private theorem fixed_card_bound
    (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane) (a : A) (ha : a ≠ 1) :
    Nat.card (fixedSpace modelAction A) ≤ 16 := by
  let f : fixedSpace modelAction A → {x : Six // step (parameters a) x = x} :=
    fun v => ⟨coordinatesEquiv v, by
      rw [← coordinates_action a (hA a.property)]
      exact congrArg coordinatesEquiv (v.property a)⟩
  have hf : Function.Injective f := by
    intro v w h
    have hh := congrArg Subtype.val h
    exact Subtype.ext (coordinatesEquiv.injective hh)
  exact (Nat.card_le_card_of_injective f hf).trans
    (by simpa only [Nat.card_eq_fintype_card] using
      fixed_card (parameters a) (parameters_ne_zero A hA ha))

private theorem common_fixed_card_bound
    (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    Nat.card (fixedSpace modelAction A) ≤ 8 := by
  let f : fixedSpace modelAction A →
      {x : Six // step (parameters a) x = x ∧ step (parameters b) x = x} :=
    fun v => ⟨coordinatesEquiv v,
      by
        rw [← coordinates_action a (hA a.property)]
        exact congrArg coordinatesEquiv (v.property a),
      by
        rw [← coordinates_action b (hA b.property)]
        exact congrArg coordinatesEquiv (v.property b)⟩
  have hf : Function.Injective f := by
    intro v w h
    have hh := congrArg Subtype.val h
    exact Subtype.ext (coordinatesEquiv.injective hh)
  exact (Nat.card_le_card_of_injective f hf).trans
    (by
      simpa only [Nat.card_eq_fintype_card] using
        common_fixed_card (parameters a) (parameters b) (parameters_ne_zero A hA ha)
          (parameters_ne_zero A hA hb) (fun h => hab (parameters_injective A hA h)))

private theorem fixed_finrank_bound
    (A : Subgroup (BinaryLinear.GL NaturalSpace)) (n : ℕ)
    (hc : Nat.card (fixedSpace modelAction A) ≤ 2 ^ n) :
    Module.finrank (ZMod 2) (fixedSpace modelAction A) ≤ n := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem standard_small_fixedCodim
    (A : Subgroup (BinaryLinear.GL NaturalSpace))
    (hA : A ≤ BinaryLinear.radical standardPlane)
    (he : IsElementaryTwo A) (hr : rank A ≤ 2) : rank A < fixedCodim modelAction A := by
  classical
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp he.1
  have hd := fixedCodim_add_finrank modelAction A
  rw [exteriorSquare_finrank] at hd
  by_cases hsmall : ∀ b : A, b = 1 ∨ b = a
  · have hc := fixed_finrank_bound A 4 (fixed_card_bound A hA a ha)
    have hr' : rank A ≤ 1 := by
      exact (Nat.log_monotone (card_le_two 1 a hsmall)).trans
        (by decide : Nat.log 2 2 ≤ 1)
    omega
  · push Not at hsmall
    obtain ⟨b, hb, hba⟩ := hsmall
    have hc := fixed_finrank_bound A 3
      (common_fixed_card_bound A hA a b ha hb (Ne.symm hba))
    omega

private noncomputable def planeEquiv : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] standardPlane where
  toFun v := ⟨![v 0, v 1, 0, 0], rfl, rfl⟩
  invFun v := ![v.val 0, v.val 1]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by
    ext i
    fin_cases i <;> simp [v.property.1, v.property.2]

private theorem standardPlane_finrank : Module.finrank (ZMod 2) standardPlane = 2 := by
  rw [← planeEquiv.finrank_eq]
  simp

private theorem quadratic_map_conj {H U : Type*} [Group H]
    [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) H U} {A : Subgroup H}
    (hq : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : U) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (v : U) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using hh


/-- On the genuine exterior square, quadratic subgroups of every plane
radical have rank at most two, and its nontrivial elementary subgroups of
rank at most two have strictly larger fixed codimension. -/
theorem exteriorRadicalBounds : ExteriorRadicalBounds := by
  constructor
  · intro P hP A hA hq
    obtain ⟨g, hg⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq
      P standardPlane (hP.trans standardPlane_finrank.symm)
    have hrad : A.map (MulAut.conj g).toMonoidHom ≤ BinaryLinear.radical standardPlane := by
      rw [← hg, ← BinaryLinear.OuterCyclic.radical_map_conj]
      exact Subgroup.map_mono hA
    simpa only [rank_map_conj] using
      standard_quadratic_rank _ hrad (quadratic_map_conj hq g)
  · intro P hP A hA he hr
    obtain ⟨g, hg⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq
      P standardPlane (hP.trans standardPlane_finrank.symm)
    have hrad : A.map (MulAut.conj g).toMonoidHom ≤ BinaryLinear.radical standardPlane := by
      rw [← hg, ← BinaryLinear.OuterCyclic.radical_map_conj]
      exact Subgroup.map_mono hA
    simpa only [rank_map_conj, fixedCodim_map_conj] using
      standard_small_fixedCodim _ hrad (he.map_conj g) (by simpa only [rank_map_conj] using hr)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix
