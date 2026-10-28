module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.GroupTheory.Hall.PointwiseFixer

/-!
# Full Borel torus fixers in even projective special linear groups

A Borel-preserving automorphism of PSL3(2^n), n > 1, that fixes the whole
Borel torus modulo the unipotent subgroup can move the diagram only when
n = 2. The graph-field obstruction applies to the two residual torus axes.
Pointwise fixation of an actual odd Hall subgroup gives the required full
quotient fixation. At field size four, the torus and every odd Hall subgroup
have order three and lie in the point-parabolic solvable residual.

Source: Aschbacher--Smith, 14.2.12, printed pp.983--984.
-/

public section
open scoped MatrixGroups
open Subgroup

namespace Matrix.PSL3.CartanActions.FullTorusFixer
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.CartanActions.BorelQuotient
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem map_unipotent_of_map_borel {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (a : MulAut PSL(3,F)) (hB : (borel F).map a.toMonoidHom = borel F) :
    (unipotent F).map a.toMonoidHom = unipotent F := by
  have hc : (borel F).pCoreIn 2 = unipotent F := by
    rw [pCoreIn, twoCore_eq F hF,
      map_subgroupOf_eq_of_le (unipotent_le_borel F)]
  rw [← hc, map_pCoreIn_of_injective 2 _ _ a.injective, hB]

theorem degree_eq_two_of_fixed_torus {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut PSL(3,F)) (hB : (borel F).map a.toMonoidHom = borel F)
    (hfix : ∀ x ∈ torus F, a x * x⁻¹ ∈ unipotent F)
    (hmove : ¬ (PreservesPointType F a ∧ PreservesLineType F a)) : n = 2 := by
  by_contra hn2
  have hs := map_unipotent_of_map_borel hF a hB
  have ha : a ∈ standard F := by
    rw [standard_eq_top_of_two_power_card F (by omega) hF]
    trivial
  obtain ⟨m, σ, he | he⟩ := ResidualLinear.standard_opposition_factorization a ha
  · apply hmove
    apply (mem_diagramTrivial_iff F a).mp
    apply (mem_diagramTrivial F a).mpr
    intro b
    rw [he]
    exact linearField_mapsParabolicType F _ ((ExtensionBorel.linearField F).mul_mem
      (Subgroup.mem_sup_left ⟨m,rfl⟩) (Subgroup.mem_sup_right ⟨σ,rfl⟩)) b
  · apply ResidualLinear.linear_graph_field_not_fixed hF hn hn2 m σ
      (by rwa [← he])
    intro u hu
    simpa only [← he] using hfix (torusMap F (u,1)) ⟨(u,1),rfl⟩

theorem degree_eq_two_of_pointwise_torus {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut PSL(3,F)) (hB : (borel F).map a.toMonoidHom = borel F)
    (hfix : ∀ x ∈ torus F, a x = x)
    (hmove : ¬ (PreservesPointType F a ∧ PreservesLineType F a)) : n = 2 := by
  apply degree_eq_two_of_fixed_torus hF hn a hB _ hmove
  intro x hx
  rw [hfix x hx, mul_inv_cancel]
  exact (unipotent F).one_mem

omit [CharP F 2] in
theorem borel_twoCore_index_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Odd (pCore 2 (borel F)).index := by
  rw [index_eq_card, Nat.card_congr (quotientTorusEquiv F hF).toEquiv,
    Nat.card_congr (torusEquiv F).toEquiv]
  apply Odd.of_dvd_nat _ (Subgroup.card_range_dvd (torusMap F))
  rw [Nat.card_prod]
  exact (units_odd F hF).mul (units_odd F hF)

theorem degree_eq_two_of_fixed_hall {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut PSL(3,F)) (hB : (borel F).map a.toMonoidHom = borel F)
    (D : Subgroup (borel F)) (hD : IsHallSubgroup OddHall.oddPrimes D)
    (hfix : ∀ d ∈ D, a d.val = d.val)
    (hmove : ¬ (PreservesPointType F a ∧ PreservesLineType F a)) : n = 2 := by
  let aB : MulAut (borel F) := (a.subgroupMap (borel F)).trans (MulEquiv.subgroupCongr hB)
  have hh : ∀ d ∈ D, aB d = d := fun d hd => Subtype.ext (hfix d hd)
  apply degree_eq_two_of_fixed_torus hF hn a hB _ hmove
  intro x hx
  let b : borel F := ⟨x,torus_le_borel F hx⟩
  have h := mem_map_of_mem (borel F).subtype
    (OddHall.fixed_mod_core_of_pointwise_hall (borel_twoCore_index_odd hF) aB D hD hh b)
  rw [twoCore_eq F hF, map_subgroupOf_eq_of_le (unipotent_le_borel F)] at h
  exact h

omit [CharP F 2] in
theorem card_torus_of_card_four (hF : Nat.card F = 4) : Nat.card (torus F) = 3 := by
  have h := card_torus_mul_scalar F
  norm_num [hF] at h
  omega

omit [Finite F] [CharP F 2] in
theorem torus_le_pointLocal_of_card_four (hF : Nat.card F = 4) :
    torus F ≤ pointLocal F := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have ha : a ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := a)
    simpa [Nat.card_units, hF] using h
  have he : torusMap F (a,b) = torusMap F (1,b*a⁻¹) := by
    apply (ResidualParameters.projective_parameters_eq_iff _ _).mpr
    constructor
    · simp [mul_left_comm]
    · simpa using ha
  rw [he]
  apply mem_map_of_mem (projection F)
  rw [mem_pointLocalSL_iff, torusSL_val]
  simp

omit [CharP F 2] in
theorem torus_inf_pointResidual_of_card_four (hF : Nat.card F = 4) :
    torus F ⊓ (solvableResidual (pointParabolic F)).map (pointParabolic F).subtype =
      torus F := by
  rw [ParabolicResiduals.pointParabolic_residual F (by omega)]
  exact inf_eq_left.mpr (torus_le_pointLocal_of_card_four hF)

omit [CharP F 2] in
theorem borel_le_pointLocal_of_card_four (hF : Nat.card F = 4) :
    borel F ≤ pointLocal F := by
  intro g hg
  obtain ⟨d,u,hu,he⟩ := borel_factorization F g hg
  rw [he]
  exact (pointLocal F).mul_mem ((unipotent_le_pointLocal F) hu)
    (torus_le_pointLocal_of_card_four hF ⟨d,rfl⟩)

omit [CharP F 2] in
theorem hall_card_and_inf_pointResidual_of_card_four (hF : Nat.card F = 4)
    (D : Subgroup (borel F)) (hD : IsHallSubgroup OddHall.oddPrimes D) :
    Nat.card D = 3 ∧
      D.map (borel F).subtype ⊓
        (solvableResidual (pointParabolic F)).map (pointParabolic F).subtype =
      D.map (borel F).subtype := by
  have hc := borel_twoCore_index_odd (n := 2) (by norm_num; exact hF)
  let S : Sylow 2 (borel F) := pCore_isPGroup.toSylow hc.not_two_dvd_nat
  have he := (OddHall.sylow_complement_of_hall S hD).symm.index_eq_card
  have hd : Nat.card D = 3 := by
    have hq : (pCore 2 (borel F)).index = 3 := by
      rw [index_eq_card, Nat.card_congr (quotientTorusEquiv F (n := 2) (by norm_num; exact hF)).toEquiv,
        Nat.card_congr (torusEquiv F).toEquiv]
      exact card_torus_of_card_four hF
    exact he.symm.trans hq
  refine ⟨hd,?_⟩
  rw [ParabolicResiduals.pointParabolic_residual F (by omega)]
  apply inf_eq_left.mpr
  exact (map_le_range _ _).trans ((by rw [range_subtype] :
    (borel F).subtype.range ≤ borel F).trans (borel_le_pointLocal_of_card_four hF))

end Matrix.PSL3.CartanActions.FullTorusFixer
