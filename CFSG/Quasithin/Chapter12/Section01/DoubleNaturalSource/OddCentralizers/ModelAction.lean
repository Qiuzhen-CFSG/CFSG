module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Action
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.Inputs
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.ModelAction.LargePrime
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Linear
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Finite doubled-action inputs for 12.1.9

The component quotient is the literal natural action on the first summand of
the selected `n ⊕ n*` coordinates.  Its image in the full action quotient has
index two, so every odd actor is represented by the inner linear group.  The
binary displacement calculation on the natural summand and its dual gives
codimension at least four.  The alternating form is then nondegenerate on
the odd fixed space by coprime averaging. The literal Sylow image in the full
model also supplies the large-prime permutability input, using the binary
three-free overgroup theorem.

Source: Aschbacher--Smith, 12.1.9, printed pp.793--794.
-/

@[expose] public noncomputable section
open Subgroup Module Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

noncomputable def componentRangeEquiv : LinearGroup n ≃* B.componentEmbedding.range :=
  B.component.symm.trans (MonoidHom.ofInjective B.componentEmbedding_injective)

omit [Finite G] [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
theorem componentRange_index : B.componentEmbedding.range.index = 2 := by
  let : Finite (LinearGroup n) := Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  have hr : Nat.card B.componentEmbedding.range = Nat.card (LinearGroup n) :=
    Nat.card_congr B.componentRangeEquiv.symm.toEquiv
  have hi : Nat.card (MulAut.innerSubgroup (LinearGroup n)) = Nat.card (LinearGroup n) :=
    Nat.card_congr (ModelOrbits.AutomorphismModel.innerEquiv (by have := B.degree; omega)).symm.toEquiv
  have ha := (MulAut.innerSubgroup (LinearGroup n)).index_mul_card
  rw [ModelOrbits.AutomorphismModel.inner_index B.degree, hi] at ha
  have hq := B.componentEmbedding.range.index_mul_card
  rw [hr, Nat.card_congr B.full.toEquiv, ← ha] at hq
  exact Nat.mul_right_cancel (Nat.card_pos (α := LinearGroup n)) hq

theorem odd_map_le_index_two {A H : Type*} [Group A] [Finite A] [Group H]
    (f : A →* H) (J : Subgroup H) (hJ : J.index = 2) (ho : Odd (Nat.card A)) :
    f.range ≤ J := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨k, hk⟩ := ho
  have hp : f a ^ (k * 2 + 1) = 1 := by
    rw [show k * 2 + 1 = Nat.card A by omega, ← map_pow, pow_card_eq_one', map_one]
  have hh : f a ^ (k * 2) ∈ J := by
    rw [mul_comm, pow_mul]
    exact J.pow_mem (J.sq_mem_of_index_two hJ (f a)) k
  have hone : f a ^ (k * 2) * f a ∈ J := by rw [← pow_succ, hp]; exact J.one_mem
  exact (J.mul_mem_cancel_left hh).mp hone

noncomputable def oddActorMap (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G)) : X →* LinearGroup n :=
  B.componentRangeEquiv.symm.toMonoidHom.comp
    ((B.actionProjection.comp (inclusion hXM)).codRestrict B.componentEmbedding.range
      (fun x => odd_map_le_index_two _ _ B.componentRange_index ho ⟨x, rfl⟩))

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
private theorem oddActorMap_embedding (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G)) (x : X) :
    B.componentEmbedding (B.component.symm (B.oddActorMap X ho hXM x)) =
      B.actionProjection (inclusion hXM x) := by
  exact congrArg Subtype.val (B.componentRangeEquiv.apply_symm_apply
    ⟨B.actionProjection (inclusion hXM x), _⟩)

private theorem oddActorMap_coordinates (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G)) (x : X)
    (w : Additive (componentOrbit V (T : Subgroup G))) :
    B.linearCoordinates (B.quotientRepresentation (B.actionProjection (inclusion hXM x)) w) =
      naturalDualRepresentation (B.oddActorMap X ho hXM x) (B.linearCoordinates w) := by
  rw [← B.oddActorMap_embedding X ho hXM x, B.componentEmbedding_coordinates,
    B.component.apply_symm_apply]

omit [Finite G] in
private theorem fixedSpace_eq_invariants (X : Subgroup G) (hXM : X ≤ normalizer (L : Set G)) :
    B.fixedSpace X =
      Representation.invariants (B.quotientRepresentation.comp (B.actionProjection.comp (inclusion hXM))) := by
  ext w
  rw [fixedSpace, mem_subgroupSpace]
  constructor
  · intro hw x
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (x : G) * (w.toMul : G) * (x : G)⁻¹ = (w.toMul : G)
    rw [mem_centralizer_iff.mp hw x x.property, mul_inv_cancel_right]
  · intro hw
    apply mem_centralizer_iff.mpr
    intro x hx
    have he := congrArg (fun z => (z.toMul : G)) (hw (⟨x,hx⟩ : X))
    change x * (w.toMul : G) * x⁻¹ = (w.toMul : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he

private theorem fixedSpace_map_oddActor (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G)) :
    (B.fixedSpace X).map B.linearCoordinates.toLinearMap =
      Representation.BinaryOffender.fixedSpace naturalDualRepresentation
        (B.oddActorMap X ho hXM).range := by
  ext v
  rw [Submodule.mem_map_equiv, B.fixedSpace_eq_invariants X hXM]
  constructor
  · intro hv a
    obtain ⟨x, hx⟩ := a.property
    change naturalDualRepresentation a.val v = v
    rw [← hx]
    have he := B.oddActorMap_coordinates X ho hXM x (B.linearCoordinates.symm v)
    have hfix := hv x
    simp only [MonoidHom.comp_apply] at hfix
    rw [hfix, B.linearCoordinates.apply_symm_apply] at he
    exact he.symm
  · intro hv x
    apply B.linearCoordinates.injective
    simp only [MonoidHom.comp_apply]
    rw [B.oddActorMap_coordinates X ho hXM, B.linearCoordinates.apply_symm_apply]
    exact hv ⟨_, x, rfl⟩

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
private theorem oddActorMap_range_ne_bot (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G))
    (hn : ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    (B.oddActorMap X ho hXM).range ≠ ⊥ := by
  intro he
  apply hn
  intro x hx
  apply mem_centralizer_iff.mpr
  intro w hw
  have hx1 : B.oddActorMap X ho hXM ⟨x,hx⟩ = 1 :=
    mem_bot.mp (he ▸ (show B.oddActorMap X ho hXM ⟨x,hx⟩ ∈
      (B.oddActorMap X ho hXM).range from ⟨_, rfl⟩))
  have hq : B.actionProjection (inclusion hXM ⟨x,hx⟩) = 1 := by
    rw [← B.oddActorMap_embedding X ho hXM ⟨x,hx⟩, hx1, map_one, map_one]
  have hh := B.quotientAction_projection_apply (inclusion hXM ⟨x,hx⟩) ⟨w,hw⟩
  rw [hq, map_one, MulAut.one_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

private theorem odd_fixedSpace_nondegenerate (X : Subgroup G) (ho : Odd (Nat.card X))
    (hXM : X ≤ normalizer (L : Set G)) :
    (B.quadratic.comp (B.fixedSpace X).subtype).polarBilin.Nondegenerate := by
  let ρ : Representation (ZMod 2) X (Additive (componentOrbit V (T : Subgroup G))) :=
    B.quotientRepresentation.comp (B.actionProjection.comp (inclusion hXM))
  let : Fintype X := Fintype.ofFinite X
  have hc : (Fintype.card X : ZMod 2) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_eq_one_of_odd_of_two_eq_zero ho (by decide)
  let : Invertible (Fintype.card X : ZMod 2) :=
    invertibleOfNonzero (by rw [hc]; exact one_ne_zero)
  have hQ (x : X) (w : Additive (componentOrbit V (T : Subgroup G))) :
      B.quadratic (ρ x w) = B.quadratic w := by
    change BinaryNaturalDual.quadratic
      (B.linearCoordinates (B.quotientRepresentation (B.actionProjection (inclusion hXM x)) w)) = _
    rw [B.oddActorMap_coordinates X ho hXM]
    rw [naturalDualRepresentation_apply]
    exact BinaryNaturalDual.quadratic_invariant _ _
  have hAlt : B.quadratic.polarBilin.IsAlt := by
    intro w
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simpa only [two_smul] using ZModModule.add_self (B.quadratic w)
  have hpres (x : X) (v w : Additive (componentOrbit V (T : Subgroup G))) :
      B.quadratic.polarBilin (ρ x v) (ρ x w) = B.quadratic.polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [← map_add, hQ, hQ, hQ]
  rw [QuadraticMap.polarBilin_comp]
  change (LinearMap.BilinForm.restrict B.quadratic.polarBilin (B.fixedSpace X)).Nondegenerate
  rw [B.fixedSpace_eq_invariants X hXM]
  exact SymplecticConjugatePair.OddOrder.invariants_nondegenerate ρ
    B.quadratic.polarBilin hAlt B.polar_nondegenerate hpres

private theorem square_eq_one_of_displacement_le_one
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (e : U ≃ₗ[ZMod 2] U)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1) :
    e ^ 2 = 1 := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change e.toLinearMap v = 0
      rw [he, LinearMap.transvection.apply, ho, one_smul, ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv, map_zero] at ho
    exact (zero_ne_one ho).elim
  apply LinearEquiv.ext
  intro x
  change e (e x) = x
  have hex (x : U) : e x = x + f x • v := congrArg (fun l : U →ₗ[ZMod 2] U => l x) he
  simp only [hex, map_add, map_smul, hfv, smul_zero, add_zero]
  simp [add_assoc, ZModModule.add_self]

private theorem four_le_model_fixedCodim
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (A : Subgroup (BinaryLinear.GL U))
    [Finite A] (hodd : Odd (Nat.card A)) (hne : A ≠ ⊥) :
    4 ≤ Representation.BinaryOffender.fixedCodim naturalDualRepresentation A := by
  obtain ⟨g, hg, hg1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  let ρ : Representation (ZMod 2) (BinaryLinear.GL U) U :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hgodd : Odd (orderOf g) := by
    have hh := hodd.of_dvd_nat (orderOf_dvd_natCard (⟨g, hg⟩ : A))
    simpa only [Subgroup.orderOf_mk] using hh
  have htwo : 2 ≤ Representation.BinaryOffender.fixedCodim ρ (zpowers g) := by
    by_contra h
    have hdρ : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≤ 1 := by
      rw [← Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank ρ g]
      omega
    have hd : Module.finrank (ZMod 2) (LinearMap.range (g.toLinearMap - LinearMap.id)) ≤ 1 := by
      have heqρ : ρ g = g.toLinearMap := rfl
      rw [heqρ] at hdρ
      exact hdρ
    have hs : g ^ 2 = 1 := square_eq_one_of_displacement_le_one g hd
    have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hs
    have ho : orderOf g = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with ho | ho
      · exact ho
      · exact (hgodd.not_two_dvd_nat (by simp [ho])).elim
    exact hg1 (orderOf_eq_one_iff.mp ho)
  have hfour : 4 ≤ Representation.BinaryOffender.fixedCodim naturalDualRepresentation (zpowers g) := by
    have heq : naturalDualRepresentation (V := U) = ρ.prod ρ.dual := by
      ext g v <;> simp [ρ, BinaryNaturalDual.naturalDualRepresentation,
        Representation.prod, Representation.dual]
    rw [heq]
    rw [Representation.BinaryOffender.fixedCodim_prod,
      Representation.BinaryOffender.fixedCodim_zpowers_dual]
    omega
  have hA := Representation.BinaryOffender.fixedCodim_add_finrank naturalDualRepresentation A
  have hgrp := Representation.BinaryOffender.fixedCodim_add_finrank naturalDualRepresentation (zpowers g)
  have hle : Representation.BinaryOffender.fixedSpace naturalDualRepresentation A ≤
      Representation.BinaryOffender.fixedSpace naturalDualRepresentation (zpowers g) := by
    exact Representation.BinaryOffender.fixedSpace_antitone naturalDualRepresentation
      (zpowers_le.mpr hg)
  have hm := Submodule.finrank_mono hle
  omega

private theorem odd_fixed_codim
    (X : Subgroup G) (ho : Odd (Nat.card X)) (hXM : X ≤ normalizer (L : Set G))
    (hn : ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    4 ≤ finrank (ZMod 2)
      ((Additive (componentOrbit V (T : Subgroup G))) ⧸ B.fixedSpace X) := by
  have hrange : (B.oddActorMap X ho hXM).range ≠ ⊥ :=
    B.oddActorMap_range_ne_bot X ho hXM hn
  let E := B.linearCoordinates
  have hmap := B.fixedSpace_map_oddActor X ho hXM
  have hmodeladd := Representation.BinaryOffender.fixedCodim_add_finrank
    naturalDualRepresentation (B.oddActorMap X ho hXM).range
  have htargetadd := Submodule.finrank_quotient_add_finrank (B.fixedSpace X)
  have hfixed : finrank (ZMod 2) (B.fixedSpace X) =
      finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace
        naturalDualRepresentation (B.oddActorMap X ho hXM).range) := by
    rw [← hmap, E.finrank_map_eq]
  let _ : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  have horange : Odd (Nat.card (B.oddActorMap X ho hXM).range) :=
    ho.of_dvd_nat (Subgroup.card_range_dvd (B.oddActorMap X ho hXM))
  have hmodel := four_le_model_fixedCodim (B.oddActorMap X ho hXM).range horange hrange
  have hmodeldim : finrank (ZMod 2) (BinaryNaturalDual.Space (BinaryLinear.OuterCyclic.Space n)) = 2 * n := by
    simp [BinaryNaturalDual.Space, BinaryLinear.OuterCyclic.Space, Module.finrank_prod]
    omega
  have htargetdim := B.finrank_eq
  have hcoord : finrank (ZMod 2) (Additive (componentOrbit V (T : Subgroup G))) =
      finrank (ZMod 2) (BinaryNaturalDual.Space (BinaryLinear.OuterCyclic.Space n)) := by
    rw [B.finrank_eq, hmodeldim]
  omega

theorem oddActionGeometry_of_doubled
    (X : Subgroup G) (ho : Odd (Nat.card X)) (hXM : X ≤ normalizer (L : Set G))
    (hn : ¬ X ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    (B.quadratic.comp (B.fixedSpace X).subtype).polarBilin.Nondegenerate ∧
      4 ≤ finrank (ZMod 2)
        ((Additive (componentOrbit V (T : Subgroup G))) ⧸ B.fixedSpace X) := by
  exact ⟨B.odd_fixedSpace_nondegenerate X ho hXM, B.odd_fixed_codim X ho hXM hn⟩

theorem oddActionGeometry
    : B.OddActionGeometry := by
  intro X ho hXM hn
  exact B.oddActionGeometry_of_doubled X ho hXM hn

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
