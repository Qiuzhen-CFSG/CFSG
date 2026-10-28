module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Mathlib.GroupTheory.Commutator.Basic
public import Theory.GroupTheory.SylowPrimeActors

/-!
# Split-prime actors on the original symplectic Sylow group

The first and last positive-root involutions have commutator theta(1,1).
The actual diagonal torus element with parameters (a,1) sends this to
theta(a²,a), so every nontrivial parameter moves the derived subgroup of the
full Sylow two-group. Cauchy's theorem selects each split-prime order, and
central two-kernel lifting preserves that order and the original Sylow.

This argument uses the checked root coordinates of the full symplectic Sylow;
it needs no auxiliary description of its entire derived subgroup.
Source: Aschbacher–Smith, The Classification of Quasithin Groups, proof of
2.5.7, printed p.556.
-/

public section
open Matrix Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.SplitPrimeActor
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2]

private theorem first_involution : (element (1:F) 0 0 0)^2=1 := by
  rw [element_square]
  simpa [theta] using (element_zero (F:=F))
private theorem last_involution : (element (0:F) 0 0 1)^2=1 := by
  rw [element_square]
  simpa [theta] using (element_zero (F:=F))

theorem central_commutator :
    ⁅element (1:F) 0 0 0, element 0 0 0 1⁆ = theta (1:F) 1 := by
  have hi : (element (1:F) 0 0 0)⁻¹=element 1 0 0 0 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using (first_involution (F:=F))
  have hj : (element (0:F) 0 0 1)⁻¹=element 0 0 0 1 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_two] using (last_involution (F:=F))
  rw [commutatorElement_def, hi, hj]
  have h : element (1:F) 0 0 0 * element 0 0 0 1 = element 1 0 0 1 := by
    rw [element_mul]
    simp only [zero_add, add_zero, mul_zero]
  calc
    element (1:F) 0 0 0 * element 0 0 0 1 * element 1 0 0 0 * element 0 0 0 1 =
        (element (1:F) 0 0 0 * element 0 0 0 1)^2 := by rw [pow_two,mul_assoc]
    _ = theta (1:F) 1 := by rw [h,element_square]; simp

theorem central_parameter_mem_derived :
    parameter (Multiplicative.ofAdd (1:F),Multiplicative.ofAdd (1:F)) ∈
      ⁅unipotent (F:=F),unipotent (F:=F)⁆ := by
  change (theta (1:F) 1 : Sp F) ∈ _
  rw [←central_commutator]
  change (unipotent (F:=F)).subtype ⁅element (1:F) 0 0 0,element 0 0 0 1⁆ ∈ _
  rw [map_commutatorElement]
  exact commutator_mem_commutator (element (1:F) 0 0 0).property
    (element (0:F) 0 0 1).property

noncomputable def actorHom : Fˣ →* Sp F where
  toFun a := diagonalTorusHom (a,1)
  map_one' := map_one diagonalTorusHom
  map_mul' a b := by simpa using map_mul diagonalTorusHom (a,1) (b,1)

theorem actor_moves_derived (a : Fˣ) (ha : a ≠ 1) :
    actorHom a ∉ centralizer
      ((⁅unipotent (F:=F),unipotent (F:=F)⁆ : Subgroup (Sp F)) : Set (Sp F)) := by
  intro hc
  have hh := hc _ (central_parameter_mem_derived (F:=F))
  have hw := diagonalTorus_weights (a,1) (1:F) 1
  change actorHom a * parameter _ * (actorHom a)⁻¹ = _ at hw
  rw [←hh, mul_inv_cancel_right] at hw
  have he := parameter_injective hw
  have ha1 : (1:F) = (a:F) := by
    simpa using congrArg (fun x : Multiplicative F × Multiplicative F => x.2.toAdd) he
  exact ha (Units.ext ha1.symm)

theorem actor_ne_one (a : Fˣ) (ha : a ≠ 1) : actorHom a ≠ 1 := by
  intro h
  apply actor_moves_derived a ha
  rw [h]
  exact one_mem _

variable [Finite F]
theorem standard_prime_actor {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card F-1) :
    ∃ X : Subgroup (Sp F), Nat.card X=p ∧
      X ≤ normalizer (unipotent (F:=F) : Set (Sp F)) ∧
      ¬ X ≤ centralizer
        ((⁅unipotent (F:=F),unipotent (F:=F)⁆ : Subgroup (Sp F)) : Set (Sp F)) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p
    (by simpa only [Nat.card_units] using hd : p ∣ Nat.card Fˣ)
  have ha1 : a≠1 := by
    intro h
    rw [h,orderOf_one] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  have ht : (actorHom a)^p=1 := by
    rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
  refine ⟨zpowers (actorHom a),?_,?_,?_⟩
  · rw [Nat.card_zpowers,orderOf_eq_prime ht (actor_ne_one a ha1)]
  · exact zpowers_le.mpr (diagonalTorus_normalizes (a,1))
  · exact fun h => actor_moves_derived a ha1 (h (mem_zpowers _))
variable {E : Type*} [Group E] [Finite E]
/-- The actual split-prime actor on every central two-cover of the symplectic model. -/
theorem prime_actor_on_cover
    (α : E →* Sp F) (hα : Function.Surjective α)
    (h2 : IsPGroup 2 α.ker) (hc : α.ker ≤ center E)
    {n : ℕ} (hn : 1≤n) (hF : Nat.card F=2^n)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hd : p ∣ 2^n-1) (S : Sylow 2 E) :
    ∃ X : Subgroup E, Nat.card X=p ∧ X ≤ normalizer (S : Set E) ∧
      ¬ X ≤ centralizer ((⁅(S : Subgroup E),(S : Subgroup E)⁆ : Subgroup E) : Set E) := by
  obtain ⟨β,hβ,hker,hS⟩ := exists_sylow_aligned_map α hα S (unipotentSylow hF hn)
  change (S : Subgroup E).map β=unipotent (F:=F) at hS
  have hb2 : IsPGroup 2 β.ker := by rw [hker]; exact h2
  have hbc : β.ker ≤ center E := by rw [hker]; exact hc
  obtain ⟨A,hA,hN,hm⟩ := standard_prime_actor (F:=F) (hF ▸ hd)
  obtain ⟨X,_,hcard,hXN,hmove⟩ := lift_odd_sylow_actor β hβ hb2 hbc S A
    (hA ▸ ho) (hS.symm ▸ hN) (by simpa only [hS] using hm)
  exact ⟨X,hcard.trans hA,hXN,hmove⟩

end Theory.SpecificGroups.SymplecticFour.SplitPrimeActor
