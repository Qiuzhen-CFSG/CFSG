module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.FourActors.Coordinate

/-!
# Corank-three cores for the degree-four H.9 actors

The A₀ core is already full at corank two. For A₁ an outer diagonal
vector enlarges its six-dimensional corank-two core. For A₂ the fixed
hyperplanes of two transvections span the natural summand; the actual
outer interchange then supplies the dual summand. Conjugation through
the exhaustive three-class catalogue gives dimension at least seven.

Source: Aschbacher--Smith, H.9.3 and12.1.10, printed pp.391--392,794.
-/

public noncomputable section
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
variable (d : CoordinateAction 4)
local instance : Finite M := Finite.of_injective permutationEquiv permutationEquiv.injective

private theorem core_mono (A : Subgroup M) {j k : ℕ} (hjk : j ≤ k) :
    actorCore d A j ≤ actorCore d A k :=
  generatedCore_le _ fun _ h => fixedSpace_le_generatedCore _ (h.trans hjk)

private theorem element_fixed_le_core (A : Subgroup M)
    (hcard : Nat.card A = 16) (b : A) (hb : orderOf b = 2) :
    fixedSpace (action d b) ≤ actorCore d A 3 := by
  have hc : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers, hb]
  have hi : (Subgroup.zpowers b).index = 8 := by
    have hh := (Subgroup.zpowers b).index_mul_card
    rw [hc, hcard] at hh
    omega
  intro v hv
  apply fixedSpace_le_generatedCore (d.representation.comp A.subtype)
    (X := Subgroup.zpowers b) (by rw [hi]; decide)
  rw [Representation.BinaryOffender.mem_fixedSpace_zpowers_iff]
  exact (mem_fixedSpace _ _).mp hv

/-- The outer diagonal supplies a vector outside the corank-two core of A₁. -/
theorem A1_core_strict : actorCore d A1 2 < actorCore d A1 3 := by
  let := PermutationCatalogue.A1_elementary
  apply lt_of_le_of_ne (core_mono d A1 (by decide))
  intro he
  have ht : transposition ^ 2 = 1 := by
    simpa only [transposition_order] using pow_orderOf_eq_one transposition
  let x : X := ![0,0,1,0]
  let v := outerDiagonalEquiv d transposition ht transposition_outer x
  let b : A1 := ⟨transposition, transposition_mem_A1⟩
  have hb : orderOf b = 2 := (Subgroup.orderOf_coe b).symm.trans transposition_order
  have hv := element_fixed_le_core d A1 PermutationCatalogue.A1_card b hb v.property
  rw [← he, (Parameters.A1_parameters d).2.1] at hv
  have hfix := (mem_fixedSpace _ _).mp hv
  rw [action_apply, A1Module.r_eq, d.on_inner, naturalDualRepresentation_apply] at hfix
  have hx := (A1Module.natural_r_fixed _).mp (congrArg Prod.fst hfix)
  rw [show (v : V).1 = x from outerDiagonalEquiv_fst d transposition ht transposition_outer x] at hx
  change (1 : ZMod 2) = 0 at hx
  exact one_ne_zero hx

/-- At corank three the three transvection axes generate the entire A₂ module. -/
theorem A2_core_eq_top : actorCore d A2 3 = ⊤ := by
  let := PermutationCatalogue.A2_elementary
  have haxis (i : Fin 3) (x : X) (hx : x ∈ fixedSpace (A2Module.axisLinear i)) :
      (x, (0 : Module.Dual (ZMod 2) X)) ∈ actorCore d A2 3 := by
    let b : A2 := ⟨MulAut.conj (A2Module.axisLinear i),
      (A2Module.conj_axisLinear_mem i).1⟩
    have hb : b ≠ 1 := by
      intro hh
      have he : MulAut.conj (A2Module.axisLinear i) = MulAut.conj (1 : G) := by
        simpa only [b, Subgroup.coe_one, map_one] using congrArg Subtype.val hh
      exact A2Module.axisLinear_ne_one i
        (MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot he)
    have hb2 : b ^ 2 = 1 := by
      apply Subtype.ext
      change (MulAut.conj (A2Module.axisLinear i)) ^ 2 = 1
      rw [← map_pow, A2Module.axisLinear_square, map_one]
    apply element_fixed_le_core d A2 PermutationCatalogue.A2_card b
      (orderOf_eq_prime hb2 hb)
    rw [mem_fixedSpace, action_apply]
    change d.representation (MulAut.conj (A2Module.axisLinear i)) (x, 0) = (x, 0)
    rw [d.on_inner, naturalDualRepresentation_apply, map_zero, (mem_fixedSpace _ _).mp hx]
  have hn : naturalSummand ≤ actorCore d A2 3 := by
    intro v hv
    have hx : v.1 ∈ fixedSpace (A2Module.axisLinear 0) ⊔ fixedSpace (A2Module.axisLinear 1) := by
      rw [Parameters.A2_axes_span (by decide : (0 : Fin 3) ≠ 1)]
      trivial
    obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hx
    have h := (actorCore d A2 3).add_mem (haxis 0 x hx) (haxis 1 y hy)
    have hv2 := (mem_naturalSummand v).mp hv
    have hv0 : (v.1, (0 : Module.Dual (ZMod 2) X)) = v := Prod.ext rfl hv2.symm
    simpa only [Prod.mk_add_mk, zero_add, he, hv0] using h
  have hd := Submodule.map_mono (f := (action d transposition).toLinearMap) hn
  have he : A2.map (MulAut.conj transposition).toMonoidHom = A2 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer transposition_mem_A2)
  rw [ZeroClosure.FourActors.natural_map_outer d transposition transposition_outer,
    ZeroClosure.FourActors.core_conjugate, he] at hd
  apply top_unique
  rw [← summands_complementary.sup_eq_top]
  exact sup_le hn hd

/-- Every elementary actor of order sixteen has a corank-three core of dimension at least seven. -/
theorem coordinate_core_finrank (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) :
    7 ≤ Module.finrank (ZMod 2) (actorCore d A 3) := by
  have hrep (i : Fin 3) : 7 ≤ Module.finrank (ZMod 2)
      (actorCore d (PermutationCatalogue.actor i) 3) := by
    fin_cases i
    · have ht : actorCore d A0 3 = ⊤ := top_unique (by
        rw [← (Parameters.A0_parameters d).2]
        exact core_mono d A0 (by decide))
      change 7 ≤ Module.finrank (ZMod 2) (actorCore d A0 3)
      rw [ht, finrank_top]
      norm_num [V, CoordinateSpace, X, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
    · have hl := Submodule.finrank_lt_finrank_of_lt (A1_core_strict d)
      rw [(Parameters.A1_parameters d).2.1, (Parameters.A1_parameters d).2.2] at hl
      exact hl
    · change 7 ≤ Module.finrank (ZMod 2) (actorCore d A2 3)
      rw [A2_core_eq_top, finrank_top]
      norm_num [V, CoordinateSpace, X, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
  obtain ⟨i,a,he⟩ := PermutationCatalogue.actor_exhaustive A hcard
  have hd := (Submodule.equivMapOfInjective (action d a).toLinearMap
    (action d a).injective (actorCore d A 3)).finrank_eq
  rw [ZeroClosure.FourActors.core_conjugate, he] at hd
  rw [hd]
  exact hrep i
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FourGeometry
