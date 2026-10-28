module

public import Theory.GroupTheory.PGroup.HomocyclicPrimeAction
public import Theory.GroupTheory.PGroup.SL2OmegaObstruction

/-!
# Prime-order automorphisms at every higher homocyclic exponent

For P≅C(p^e)², e≥2 and p>3, restriction to Ω₂(P) gives the actual
C(p²)² action from A.1.30. Every order-p automorphism therefore fixes
Ω₁(P). The omega-action kernel and transvection-generation argument then
exclude an injective SL₂(p) action on P. This keeps all higher exponents,
rather than replacing the original prime core by an elementary plane.

Source: Aschbacher--Smith A.1.30, p.27, as used in 3.2.14, p.585.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace HomocyclicPrimeAction
variable {p : ℕ} [Fact p.Prime]

private noncomputable def cyclicOmegaPrimeEquiv (n k : ℕ) (hk : k ≤ n) :
    omega (Multiplicative (ZMod (p^n))) (p := p) k ≃*
      Multiplicative (ZMod (p^k)) := by
  rw [OmegaAction.omega_eq_pow_ker]
  apply mulEquivOfCyclicCardEq
  rw [IsCyclic.card_powMonoidHom_ker]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact Nat.gcd_eq_right (pow_dvd_pow p hk)

private noncomputable def productOmegaPrimeEquiv (n k : ℕ) (hk : k ≤ n) :
    omega (Multiplicative (ZMod (p^n)) × Multiplicative (ZMod (p^n))) (p := p) k ≃*
      (Multiplicative (ZMod (p^k)) × Multiplicative (ZMod (p^k))) := by
  have he : omega (Multiplicative (ZMod (p^n)) × Multiplicative (ZMod (p^n))) (p := p) k =
      (omega (Multiplicative (ZMod (p^n))) (p := p) k).prod
        (omega (Multiplicative (ZMod (p^n))) (p := p) k) := by
    simp only [OmegaAction.omega_eq_pow_ker]
    ext x
    change x ^ (p^k) = 1 ↔ x.1 ^ (p^k) = 1 ∧ x.2 ^ (p^k) = 1
    exact Prod.ext_iff
  exact (MulEquiv.subgroupCongr he).trans ((prodEquiv _ _).trans
    ((cyclicOmegaPrimeEquiv n k hk).prodCongr (cyclicOmegaPrimeEquiv n k hk)))

variable {P : Type*} [Group P] {n : ℕ}

/-- The actual characteristic second omega subgroup is the square-exponent
plane. This equivalence supplies the restriction in A.1.30. -/
def omegaTwoEquiv (hn : 2 ≤ n)
    (e : P ≃* Multiplicative (Fin 2 → ZMod (p^n))) :
    omega P (p := p) 2 ≃*
      (Multiplicative (ZMod (p^2)) × Multiplicative (ZMod (p^2))) := by
  let c := (AddEquiv.toMultiplicative
    (LinearEquiv.finTwoArrow (ZMod (p^n)) (ZMod (p^n))).toAddEquiv).trans
      (MulEquiv.prodMultiplicative _ _)
  exact ((e.trans c).omega p 2).trans (productOmegaPrimeEquiv n 2 hn)

/-- A.1.30's fixation statement on the original group at every exponent ≥p². -/
theorem fixes_omega_of_higher_exponent (hp : 3 < p) (hn : 2 ≤ n)
    (e : P ≃* Multiplicative (Fin 2 → ZMod (p^n)))
    (a : MulAut P) (ha : a ^ p = 1) : ∀ x ∈ omega₁ P (p := p), a x = x := by
  let : IsMulCommutative P := ⟨⟨fun x y => e.injective (by simp only [map_mul,mul_comm])⟩⟩
  let Q := omega P (p := p) 2
  let b : MulAut Q := OmegaAction.omegaRestriction P p 2 a
  have hb : b ^ p = 1 := by
    change (OmegaAction.omegaRestriction P p 2 a) ^ p = 1
    rw [← map_pow,ha,map_one]
  intro x hx
  have hx1 : x ^ p = 1 := by
    change x ∈ omega P (p := p) 1 at hx
    rw [OmegaAction.omega_eq_pow_ker] at hx
    simpa only [MonoidHom.mem_ker,powMonoidHom_apply,pow_one] using hx
  have hx2 : x ∈ Q := subset_closure (by
    change x ^ (p^2) = 1
    rw [show p ^ 2 = p * p by ring, pow_mul, hx1, one_pow])
  have hxQ : (⟨x,hx2⟩ : Q) ∈ omega₁ Q (p := p) := by
    apply subset_closure
    apply Subtype.ext
    simpa only [coe_pow,pow_one,coe_one] using hx1
  exact congrArg Subtype.val
    (fixes_omega_of_equiv hp (omegaTwoEquiv hn e) b hb ⟨x,hx2⟩ hxQ)

/-- The original higher homocyclic group admits no faithful SL₂(p) action. -/
theorem not_injective_SL2_of_higher_exponent [Finite P]
    (hp : 3 < p) (hn : 2 ≤ n)
    (e : P ≃* Multiplicative (Fin 2 → ZMod (p^n)))
    (f : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* MulAut P) :
    ¬ Function.Injective f := by
  let : IsMulCommutative P := ⟨⟨fun x y => e.injective (by simp only [map_mul,mul_comm])⟩⟩
  have hP : IsPGroup p P := (standardHomocyclicCover_isPGroup (Fin 2) p n).of_equiv e.symm
  exact not_injective_SL2_mulAut_of_prime_order_fixes_omega (by omega) hP
    (fun a ha => fixes_omega_of_higher_exponent hp hn e a (ha ▸ pow_orderOf_eq_one a)) f

end HomocyclicPrimeAction
