module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus.Geometry
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Full primary coefficients for the paired unitary torus

A cyclic coefficient group supplies two coordinate generators. Roots of unity
of order r^vᵣ(p−1) are fixed by p-Frobenius, and the preceding faithful matrix
map gives a projective torus of order r^(2vᵣ(p−1)). This retains the higher
r-power coefficients. This calculation does not by itself assert that the
ambient index is prime to r.

Source: Aschbacher–Smith A.2.17, printed p.39, the degree-four cover input.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open OddFourRanks.Defining ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F) (C : Subgroup Fˣ)
variable (hC : ∀ u : C, J.conj (u.val : F) = (u.val : F))

/-- Two coordinate generators generate the entire paired torus image. -/
theorem closure_pair (u : C) (hu : ∀ a, a ∈ zpowers u) :
    closure ({projective J C hC ![u,1], projective J C hC ![1,u]} :
      Set (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J))) =
        (projective J C hC).range := by
  let t := projective J C hC
  apply le_antisymm
  · apply (closure_le _).mpr
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨_, rfl⟩
    · rcases hz with rfl
      exact ⟨_, rfl⟩
  · rintro _ ⟨a,rfl⟩
    have hsingle (i : Fin 2) : t (Pi.mulSingle i (a i)) ∈
        closure ({t ![u,1],t ![1,u]} : Set _) := by
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp (hu (a i))
      rw [← hk, Pi.mulSingle_zpow, map_zpow]
      apply zpow_mem
      apply subset_closure
      fin_cases i
      · left
        congr 1
        ext j
        fin_cases j <;> simp
      · right
        congr 1
        ext j
        fin_cases j <;> simp
    have he : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) := by
      ext i
      fin_cases i <;> simp
    rw [he, map_mul]
    exact mul_mem (hsingle 0) (hsingle 1)

/-- The paired torus has the square of the full coefficient-group order. -/
theorem card_range [Finite F] (ho : (Nat.card C).Coprime 2) :
    Nat.card (projective J C hC).range = Nat.card C ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (projective_injective J C hC ho)).toEquiv, Nat.card_fun, Nat.card_fin]

/-- All swap geometry is supplied by the actual matrices; only the ambient index is separate. -/
theorem exists_pair [Finite F] :
    ∃ x y s : ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J),
      closure ({x,y} : Set _) = (projective J C hC).range ∧
      Commute x y ∧ s*x*s⁻¹ = y ∧ s*y*s⁻¹ = x ∧ x ^ Nat.card C = 1 := by
  obtain ⟨u,hu⟩ := IsCyclic.exists_generator (α := C)
  refine ⟨projective J C hC ![u,1], projective J C hC ![1,u], swap J,
    closure_pair J C hC u hu, (Commute.all _ _).map _, ?_, ?_, ?_⟩
  · simpa using swap_projective J C hC ![u,1]
  · simpa using swap_projective J C hC ![1,u]
  · have hp : (![u,1] : Fin 2 → C) ^ Nat.card C = 1 := by
      funext i
      exact pow_card_eq_one'
    rw [← map_pow, hp, map_one]

/-- Roots whose order divides p−1 are fixed by the stored p-Frobenius. -/
theorem roots_fixed {p m : ℕ} (hp : 1 ≤ p)
    (hc : ∀ x, J.conj x = x ^ p) (hm : m ∣ p - 1)
    (u : rootsOfUnity m F) : J.conj (u.val : F) = (u.val : F) := by
  rw [hc]
  have hu : (u.val : F) ^ (p - 1) = 1 := by
    obtain ⟨k,hk⟩ := hm
    rw [hk, pow_mul, (mem_rootsOfUnity' m u.val).mp u.property, one_pow]
  calc
    (u.val : F) ^ p = (u.val : F) ^ (p - 1 + 1) := by rw [Nat.sub_add_cancel hp]
    _ = _ := by rw [pow_succ, hu, one_mul]

/-- The full r-primary divisor of p−1, without truncating to elementary torsion. -/
def primaryExponent (p r : ℕ) : ℕ := r ^ (p - 1).factorization r

theorem primaryExponent_dvd (p r : ℕ) : primaryExponent p r ∣ p - 1 :=
  Nat.ordProj_dvd (p - 1) r

theorem primaryExponent_odd (p : ℕ) {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) :
    (primaryExponent p r).Coprime 2 := by
  apply Nat.Coprime.pow_left
  exact (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
    (fun h => hr ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp h))

/-- The canonical paired torus retains every r-power in the split coefficient group. -/
def primaryProjective {p : ℕ} [Fact p.Prime] (r : ℕ)
    (hc : ∀ x, J.conj x = x ^ p) :
    (Fin 2 → rootsOfUnity (primaryExponent p r) F) →*
      ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J) :=
  projective J _ (roots_fixed J (Fact.out : p.Prime).one_lt.le hc (primaryExponent_dvd p r))

/-- Each coefficient group has its full intended order. -/
theorem card_primary_coefficients [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) :
    Nat.card (rootsOfUnity (primaryExponent p r) F) = primaryExponent p r := by
  let : NeZero (primaryExponent p r) := ⟨pow_ne_zero _ (Fact.out : r.Prime).ne_zero⟩
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hF]
  apply (primaryExponent_dvd p r).trans
  have hp := (Fact.out : p.Prime).one_lt.le
  have he : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have hs : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp
    nlinarith [Nat.sub_add_cancel hp, Nat.sub_add_cancel hs]
  rw [he]
  exact dvd_mul_right _ _

/-- The actual projective paired torus has order r^(2vᵣ(p−1)). -/
theorem card_primary_range [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) (hr : r ≠ 2) :
    Nat.card (primaryProjective J r hc).range = primaryExponent p r ^ 2 := by
  have he := card_primary_coefficients (r := r) hF
  simpa only [primaryProjective, he] using
    card_range J _ (roots_fixed J (Fact.out : p.Prime).one_lt.le hc
      (primaryExponent_dvd p r)) (by rw [he]; exact primaryExponent_odd p hr)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus
