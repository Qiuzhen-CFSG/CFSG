module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# A size bound for transitive central involutions

Suppose a central elementary subgroup contains every involution and
its nonidentity elements are conjugate under automorphisms. An element
of order four would give a square root in every nonidentity direction.
Multiplication by the central elementary subgroup makes each root fiber
at least that large, forcing the ambient order to be at least its square.
Below this bound, the two-group is the elementary subgroup itself.

The application identifies the unitary actor's two-core in Rudvalis,
in the setup of Aschbacher–Smith 4.2.13, printed pp.611–612.
-/

public section
namespace Theory.GroupTheory
open Subgroup
open scoped IsMulCommutative

/-- Central transitive involutions force a two-group smaller than their
squared cardinality to be elementary. The square-root fibers each contain
an entire coset of the central elementary subgroup. -/
theorem eq_top_of_transitive_central_involutions
    {P : Type*} [Group P] [Finite P] (hp : IsPGroup 2 P)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : E ≤ center P)
    (hinv : ∀ x : P, x ^ 2 = 1 → x ∈ E)
    (ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ a : MulAut P, a x = y)
    (hsmall : Nat.card P < Nat.card E * Nat.card E) : E = ⊤ := by
  classical
  have hfour (x : P) (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
    by_contra hx2
    have hxE : x ^ 2 ∈ E := hinv _ (by simpa only [←pow_mul] using hx)
    have hroot : ∀ z : E, ∃ r : P, r ^ 2 = (z : P) := by
      intro z
      by_cases hz : (z : P) = 1
      · exact ⟨1,by rw [hz,one_pow]⟩
      · obtain ⟨a,ha⟩ := ht (x^2) hxE z z.property hx2 hz
        exact ⟨a x,(map_pow a x 2).symm.trans ha⟩
    let r : E → P := fun z => Classical.choose (hroot z)
    have hr (z : E) : r z ^ 2 = (z : P) := Classical.choose_spec (hroot z)
    let f : E × E → P := fun z => z.1 * r z.2
    have hs (z : E × E) : f z ^ 2 = (z.2 : P) := by
      have hc : Commute (z.1 : P) (r z.2) := (mem_center_iff.mp (hE z.1.property) _).symm
      change ((z.1 : P) * r z.2)^2 = _
      rw [hc.mul_pow,elemPow_eq_one_of_isElementaryAbelian _ z.1.property,one_mul,hr]
    have hf : Function.Injective f := by
      intro a b hab
      have h2 : a.2 = b.2 := Subtype.ext ((hs a).symm.trans ((congrArg (fun x => x^2) hab).trans (hs b)))
      apply Prod.ext _ h2
      apply Subtype.ext
      change (a.1 : P) * r a.2 = (b.1 : P) * r b.2 at hab
      rw [h2] at hab
      exact mul_right_cancel hab
    have hc := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hc
    omega
  have hexp (n : ℕ) : ∀ x : P, x ^ (2 ^ n) = 1 → x ^ 2 = 1 := by
    induction n with
    | zero =>
        intro x hx
        have hx1 : x = 1 := by simpa only [pow_zero,pow_one] using hx
        rw [hx1,one_pow]
    | succ n ih =>
      intro x hx
      apply hfour
      have hh := ih (x^2) (by rw [←pow_mul,←pow_succ']; exact hx)
      simpa only [←pow_mul] using hh
  apply top_unique
  intro x _
  obtain ⟨n,hn⟩ := hp x
  exact hinv x (hexp n x hn)
end Theory.GroupTheory
