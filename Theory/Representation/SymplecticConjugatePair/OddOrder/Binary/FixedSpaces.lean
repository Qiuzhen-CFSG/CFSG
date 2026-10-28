module

public import Theory.Representation.SymplecticConjugatePair.OddOrder
public import Theory.SpecificGroups.SymplecticFour.Binary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Binary odd-prime fixed spaces and the exceptional graph map

For a prime-order permutation of the sixteen vectors, the fixed-vector count
is congruent to sixteen modulo the prime. An odd-order symplectic fixed space
has dimension zero or two, so the second possibility forces the prime to be
three.

An element of order three fixing a nonzero vector is conjugate into the point
parabolic. Its genuine `C₂ × S₄` model has just one cubic conjugacy class.
A representative acts on one hyperbolic pair; its graph image has no fixed
vectors. Matrix conjugation transports this calculation to the whole class.
The point-parabolic equivalence includes entrywise transport from any field
of order two, so the statement uses the given coefficient field throughout.

Source: Aschbacher–Smith, H.7, printed p.389 of `refs/quasithin.pdf`, combined
manuscript of 1 March 2004. The imported geometric and field-transport modules
retain the attribution for their ATLAS adaptations.
-/

public section

open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open SymplecticConjugatePair.OddOrder Representation Module
open scoped Matrix
namespace SymplecticConjugatePair.OddOrder.Binary
variable {F : Type*} [Field F]
/-- Conjugation transports the actual natural fixed vectors by the conjugating matrix. -/
theorem naturalFixed_conj_eq_bot_iff (k g : Sp F) :
    naturalFixed (k*g*k⁻¹) = ⊥ ↔ naturalFixed g = ⊥ := by
  have step (k g : Sp F) (h : naturalFixed (k*g*k⁻¹) = ⊥) : naturalFixed g = ⊥ := by
    rw [Submodule.eq_bot_iff] at h ⊢
    intro v hv
    have hv' : g • v = v := (mem_naturalFixed g v).mp hv
    have hk : k • v ∈ naturalFixed (k*g*k⁻¹) := by
      rw [mem_naturalFixed]
      change (k*g*k⁻¹) • (k • v) = k • v
      simp [mul_smul, hv']
    have he := h _ hk
    exact (toLinear k).injective (he.trans (map_zero _).symm)
  refine ⟨step k g, fun h => ?_⟩
  apply step k⁻¹ (k*g*k⁻¹)
  simpa [mul_assoc] using h

/-- Having zero natural fixed space is constant on matrix conjugacy classes. -/
theorem naturalFixed_isConj_eq_bot_iff {g h : Sp F} (hc : IsConj g h) :
    naturalFixed g = ⊥ ↔ naturalFixed h = ⊥ := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp hc
  exact (naturalFixed_conj_eq_bot_iff k g).symm

variable [Finite F] [CharP F 2]
/-- An odd prime other than three has zero natural fixed space over the binary field. -/
theorem naturalFixed_eq_bot_of_prime_ne_three (hF : Nat.card F = 2) {g : Sp F}
    (hp : (orderOf g).Prime) (ho : Odd (orderOf g)) (h3 : orderOf g ≠ 3) :
    naturalFixed g = ⊥ := by
  classical
  let : Fact (orderOf g).Prime := ⟨hp⟩
  have hg : g ≠ 1 := fun h => hp.ne_one (by simp [h])
  have hpg : IsPGroup (orderOf g) (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers])
  have hm := hpg.card_modEq_card_fixedPoints (Vector F)
  have he : MulAction.fixedPoints (Subgroup.zpowers g) (Vector F) =
      (naturalFixed g : Set (Vector F)) := by rfl
  rw [he] at hm
  change Nat.card (Vector F) ≡ Nat.card (naturalFixed g) [MOD orderOf g] at hm
  rw [Module.natCard_eq_pow_finrank (K := F) (V := Vector F),
    Module.natCard_eq_pow_finrank (K := F) (V := naturalFixed g), hF] at hm
  have hd : finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hd] at hm
  rcases natural_codim_cases hg ho with h | h
  · have hr : finrank F (naturalFixed g) = 2 := by
      have := (naturalFixed g).finrank_quotient_add_finrank
      omega
    rw [hr] at hm
    have hdvd : orderOf g ∣ 12 := (Nat.modEq_iff_dvd' (by decide)).mp hm.symm
    have h2 : orderOf g ≠ 2 := by intro h; obtain ⟨k, hk⟩ := ho; omega
    have hh : orderOf g ∣ 3 ∨ orderOf g ∣ 4 :=
      (hp.dvd_mul).mp (show orderOf g ∣ 3*4 from hdvd)
    rcases hh with hh | hh
    · exact False.elim (h3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hh))
    · have hh' : orderOf g ∣ 2 := hp.dvd_of_dvd_pow (show orderOf g ∣ 2^2 from hh)
      exact False.elim (h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh'))
  · apply Submodule.finrank_eq_zero.mp
    have := (naturalFixed g).finrank_quotient_add_finrank
    omega

private lemma product_cubic_conjugate
    (x y : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))
    (hx : orderOf x = 3) (hy : orderOf y = 3) : IsConj x y := by
  have hc (z : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) (hz : orderOf z = 3) :
      z.1 = 1 ∧ orderOf z.2 = 3 := by
    have hpow : z ^ 3 = 1 := hz ▸ pow_orderOf_eq_one z
    have hfst : z.1 = 1 := (show ∀ p : Equiv.Perm (Fin 2), p^3 = 1 → p = 1 by
      decide +kernel) z.1 (congrArg Prod.fst hpow)
    refine ⟨hfst, orderOf_eq_prime (p := 3) (congrArg Prod.snd hpow) ?_⟩
    intro hsnd
    have hz1 : z = 1 := Prod.ext hfst hsnd
    simp [hz1] at hz
  obtain ⟨hx1, hx2⟩ := hc x hx
  obtain ⟨hy1, hy2⟩ := hc y hy
  have hcycle (p : Equiv.Perm (Fin 4)) (hp : orderOf p = 3) : p.cycleType = {3} := by
    have hi := Equiv.Perm.isCycle_of_prime_order' (σ := p)
      (by rw [hp]; decide) (by rw [hp]; decide)
    rw [hi.cycleType, ← hi.orderOf, hp]
  obtain ⟨k, hk⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_of_cycleType_eq ((hcycle x.2 hx2).trans (hcycle y.2 hy2).symm))
  exact isConj_iff.mpr ⟨(1,k), Prod.ext (by simp [hx1, hy1]) hk⟩

open Representation.OneCohomology.SymplecticFour
open Matrix
private def cubic : Sp F := rootElement 2 1 * rootElement 3 1

local notation "I" => Fin 2 ⊕ Fin 2
local notation "a" => (Sum.inl (0 : Fin 2) : I)
local notation "b" => (Sum.inl (1 : Fin 2) : I)
local notation "c" => (Sum.inr (0 : Fin 2) : I)
local notation "d" => (Sum.inr (1 : Fin 2) : I)

omit [Finite F] in
private lemma cubic_order : orderOf (cubic (F := F)) = 3 := by
  apply orderOf_eq_prime (p := 3)
  · apply Subtype.ext
    ext i j
    change ((rootMatrix 2 (1 : F) * rootMatrix 3 1 : Matrix I I F)^3) i j = (1 : Matrix I I F) i j
    rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, pow_succ, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        Matrix.fromBlocks, Matrix.single, Matrix.one_apply, CharTwo.add_self_eq_zero]
  · intro h
    have hh := congrArg (fun g : Sp F => g.val b d) h
    simp [cubic, rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.single] at hh

omit [Finite F] [CharP F 2] in
private lemma cubic_mem_point : cubic (F := F) ∈ pointParabolic := by
  rw [mem_pointParabolic_iff]
  simp [cubic, rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single]

private lemma graph_cubic_fixed : naturalFixed (graphAut (cubic (F := F))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_naturalFixed] at hv
  simp only [cubic, map_mul, graphAut_apply, graphEnd_root] at hv
  have ha := congrFun hv a
  have hb := congrFun hv b
  have hc := congrFun hv c
  have hd := congrFun hv d
  simp [rootPermutation, rootParameter,
    symplecticNatural_apply, rootElement, rootMatrix, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks, Matrix.single,
    CharTwo.neg_eq] at ha hb hc hd
  ext i
  rcases i with i|i <;> fin_cases i <;> simp_all

/-- The exceptional graph map sends the cubic class with nonzero fixed vectors
to the class with zero natural fixed space. -/
theorem graph_fixed_eq_bot_of_order_three (hF : Nat.card F = 2) {g : Sp F}
    (hg : orderOf g = 3) (hfix : naturalFixed g ≠ ⊥) :
    naturalFixed (graphAut g) = ⊥ := by
  obtain ⟨v, hv, hv0⟩ := (naturalFixed g).ne_bot_iff.mp hfix
  have he : e (F := F) 0 ≠ 0 := by
    intro h
    have := congrFun h a
    simp [Theory.SpecificGroups.SymplecticFour.e] at this
  obtain ⟨k, hk⟩ := TwoLocalCover.nonzero_vector_transitive hv0 he
  have hkg : k*g*k⁻¹ ∈ pointParabolic := by
    change k*g*k⁻¹ ∈ stabilizer (point F)
    rw [mem_stabilizer_iff]
    intro w hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change toLinear (k*g*k⁻¹) (t • e 0) ∈ point F
    rw [map_smul]
    have hfixed : (k*g*k⁻¹) • e (F := F) 0 = e 0 := by
      rw [← hk, mul_smul, mul_smul, inv_smul_smul]
      have hgv : g • v = v := (mem_naturalFixed g v).mp hv
      rw [hgv]
    rw [show toLinear (k*g*k⁻¹) (e 0) = e 0 from hfixed]
    exact Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_singleton _))
  let x : pointParabolic (F := F) := ⟨k*g*k⁻¹, hkg⟩
  let y : pointParabolic (F := F) := ⟨cubic, cubic_mem_point⟩
  let E := Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicEquivProd hF
  have hx : orderOf (E x) = 3 := by
    rw [E.orderOf_eq, ← Subgroup.orderOf_coe]
    change orderOf ((MulAut.conj k) g) = 3
    rw [MulEquiv.orderOf_eq, hg]
  have hy : orderOf (E y) = 3 := by
    rw [E.orderOf_eq, ← Subgroup.orderOf_coe]
    exact cubic_order
  have hc := E.symm.toMonoidHom.map_isConj (product_cubic_conjugate (E x) (E y) hx hy)
  simp only [MulEquiv.coe_toMonoidHom, E.symm_apply_apply] at hc
  have hc' : IsConj (k*g*k⁻¹) (cubic (F := F)) :=
    (pointParabolic (F := F)).subtype.map_isConj hc
  have hc'' : IsConj g (cubic (F := F)) := (isConj_iff.mpr ⟨k, rfl⟩).trans hc'
  exact (naturalFixed_isConj_eq_bot_iff (graphAut.toMonoidHom.map_isConj hc'')).mpr
    graph_cubic_fixed

end SymplecticConjugatePair.OddOrder.Binary
