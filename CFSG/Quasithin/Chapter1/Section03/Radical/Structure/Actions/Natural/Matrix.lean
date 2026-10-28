module

public import Theory.SpecificGroups.SL2.Affine.Action
public import Theory.SpecificGroups.Quaternion.PresentationHom
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Quaternion matrices in the natural radical branch

Over a prime field of odd order, write −1 as a sum of two squares. The matrices
`!![0,1; -1,0]` and `!![a,b; b,-a]` then generate an injective copy of Q₈,
with central involution −I. Sylow conjugacy puts this copy in any prescribed
Sylow two-subgroup, preserving its central involution.

A proper nontrivial invariant subgroup of the natural plane has prime order.
Its automorphism group is abelian, so the quaternion commutator acts trivially.
But that commutator acts by inversion, impossible on a nontrivial odd group.
This proves irreducibility for the Sylow restriction, not just the whole SL₂.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(3),
pp.43–45, and the natural radical actions on pp.509 and 513. The first matrix
and its square calculation also occur in `SL2.PrimeIcosahedral`; the sum of
squares and quaternion presentation use the cited imported APIs.
-/

@[expose] public section

open Matrix Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalActions.Natural
variable {F : Type*} [Field F]

private def qi : SL(2,F) := ⟨!![0, 1; -1, 0], by simp⟩
private def qj (a b : F) (h : a ^ 2 + b ^ 2 = -1) : SL(2,F) :=
  ⟨!![a, b; b, -a], by simp [Matrix.det_fin_two]; linear_combination -h⟩

private theorem qi_sq : (qi : SL(2,F)) ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem qj_sq (a b : F) (h : a ^ 2 + b ^ 2 = -1) : qj a b h ^ 2 = -1 := by
  apply Subtype.ext
  change (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

private theorem qj_qi (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    qj a b h * qi = qi⁻¹ * qj a b h := by
  apply Subtype.ext
  change (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] =
    Matrix.adjugate !![0, 1; -1, 0] * !![a, b; b, -a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]

private theorem quaternion_injective {G : Type*} [Group G] (f : QuaternionGroup 2 →* G)
    (h : f (.a 2) ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  change f x = 1 at hx
  change x = 1
  by_contra hne
  have cases : ∀ x : QuaternionGroup 2, x ≠ 1 → x = .a 2 ∨ x ^ 2 = .a 2 := by decide
  rcases cases x hne with rfl | he
  · exact h hx
  · apply h
    rw [← he, map_pow, hx, one_pow]

private theorem exists_quaternion (hn : (-1 : F) ≠ 1) (a b : F) (h : a ^ 2 + b ^ 2 = -1) :
    ∃ f : QuaternionGroup 2 →* SL(2,F), Function.Injective f ∧ f (.a 2) = -1 := by
  have hfour : (qi : SL(2,F)) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, qi_sq]
    simp
  let f := QuaternionGroup.liftOfRelations (qi : SL(2,F)) (qj a b h)
    hfour ((qj_sq a b h).trans qi_sq.symm) (qj_qi a b h)
  have hc : f (.a 2) = -1 := by
    rw [show (QuaternionGroup.a 2 : QuaternionGroup 2) = (.a 1) ^ 2 by decide,
      map_pow]
    simp only [f, QuaternionGroup.liftOfRelations_a_one, qi_sq]
  refine ⟨f, quaternion_injective f ?_, hc⟩
  rw [hc]
  intro he
  exact hn (by simpa using congrArg (fun g : SL(2,F) => g.val 0 0) he)

/-- A concrete quaternion subgroup with its central involution identified. -/
theorem sylow_quaternion [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hF : Nat.card F = p) (S : Sylow 2 SL(2,F)) :
    ∃ f : QuaternionGroup 2 →* S, Function.Injective f ∧ (f (.a 2) : SL(2,F)) = -1 := by
  let : Fintype F := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F Fact.out (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hn0 : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by linear_combination -h
    exact Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) hp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
  have hn : (-1 : F) ≠ 1 := by
    intro h
    exact hn0 (e.injective (by simpa using h))
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  obtain ⟨f, hf, hc⟩ := exists_quaternion hn (e a) (e b)
    (by simpa using congrArg e hab)
  have hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card])
  have hR : IsPGroup 2 f.range := hQ.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨T, hT⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2,F) T S
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hm (x : QuaternionGroup 2) : f' x ∈ (S : Subgroup SL(2,F)) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact smul_mem_pointwise_smul (f x) (MulAut.conj g) T (hT ⟨x, rfl⟩)
  let j : QuaternionGroup 2 →* S := f'.codRestrict S hm
  refine ⟨j, fun x y h => hf ((MulAut.conj g).injective (congrArg Subtype.val h)), ?_⟩
  change g * f (.a 2) * g⁻¹ = -1
  rw [hc]
  simp


section Abstract
variable {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]

private theorem quaternion_irreducible (hp : Odd p) (hc : Nat.card V = p ^ 2)
    (ρ : QuaternionGroup 2 →* MulAut V)
    (hz : ∀ x : V, ρ (.a 2) x = x⁻¹)
    (A : Subgroup V) (hA : ∀ g x, x ∈ A → ρ g x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  have hd : Nat.card A ∣ p ^ 2 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  interval_cases k
  · exact Or.inl (A.eq_bot_of_card_eq (by simpa using he))
  · have hcard : Nat.card A = p := by simpa using he
    let : IsCyclic A := isCyclic_of_prime_card hcard
    let ψ : QuaternionGroup 2 →* MulAut A :=
      { toFun := fun g =>
          { toFun := fun x => ⟨ρ g x, hA g x x.property⟩
            invFun := fun x => ⟨ρ g⁻¹ x, hA g⁻¹ x x.property⟩
            left_inv := fun x => Subtype.ext (by simp)
            right_inv := fun x => Subtype.ext (by simp)
            map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : V) (y : V)) }
        map_one' := by ext x; change ρ 1 (x : V) = (x : V); simp
        map_mul' := by
          intro g h; ext x
          change ρ (g * h) (x : V) = ρ g (ρ h (x : V))
          rw [map_mul]; rfl }
    have hcomm (g h : QuaternionGroup 2) : ψ g * ψ h = ψ h * ψ g := by
      apply (IsCyclic.mulAutMulEquiv A).injective
      simp only [map_mul]
      exact mul_comm _ _
    have hzψ : ψ (.a 2) = 1 := by
      rw [show (QuaternionGroup.a 2 : QuaternionGroup 2) =
        .a 1 * .xa 0 * (.a 1)⁻¹ * (.xa 0)⁻¹ by decide]
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hinv (x : A) : x⁻¹ = x := by
      apply Subtype.ext
      have heq := congrArg (fun f : MulAut A => (f x : V)) hzψ
      change ρ (.a 2) (x : V) = (x : V) at heq
      exact (hz x).symm.trans heq
    have htrivial (x : A) : x = 1 := by
      have hs : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := pow_two x
             _ = x⁻¹ * x := congrArg (fun y => y * x) (hinv x).symm
             _ = 1 := inv_mul_cancel x
      have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hs
      have hdp : orderOf x ∣ p := hcard ▸ orderOf_dvd_natCard x
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.mpr hp) hd2 hdp)
    exact Or.inl (by apply bot_unique; intro x hx; exact congrArg Subtype.val (htrivial ⟨x, hx⟩))
  · exact Or.inr (A.eq_top_of_card_eq (he.trans hc.symm))

end Abstract

/-- Every Sylow two-subgroup acts irreducibly on the prime-field plane. -/
theorem sylow_irreducible [Finite F] {p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hF : Nat.card F = p) (S : Sylow 2 SL(2,F))
    (A : Subgroup (Multiplicative (Fin 2 → F)))
    (hA : ∀ (g : S) x, x ∈ A → Matrix.SL2.naturalAction F g x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  obtain ⟨f, _, hz⟩ := sylow_quaternion hp hF S
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hc : Nat.card (Multiplicative (Fin 2 → F)) = p ^ 2 := by
    let : Fintype F := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin] using congrArg (fun n => n ^ 2) hF
  let ρ := ((Matrix.SL2.naturalAction F).comp (S : Subgroup SL(2,F)).subtype).comp f
  apply quaternion_irreducible ho hc ρ ?_ A (fun g x hx => hA (f g) x hx)
  intro x
  change Matrix.SL2.naturalAction F (f (.a 2)) x = x⁻¹
  rw [hz]
  apply Multiplicative.toAdd.injective
  change (- (1 : Matrix (Fin 2) (Fin 2) F)) *ᵥ x.toAdd = -x.toAdd
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec]

end CFSG.Quasithin.Chapter1.RadicalActions.Natural
