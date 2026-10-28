module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Theory.SpecificGroups.PSL4Three.LocalThree.Trace
public import Theory.SpecificGroups.PSL4Three.LocalThree.InvolutionCentralizer.Split
public import Theory.SpecificGroups.PSL4Three.LocalThree.InvolutionCentralizer.Nonsplit
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.ProjectiveTransfer

/-!
# Involution centralizers in the actual PSL₄(3) quotient

Every lift of a projective involution squares to I or -I. In the first
case, its trace-zero eigenspaces give an ordinary centralizer order
dividing 2304. In the second case, the quadratic-field action gives the
bound 5760. The general central-kernel transfer bounds the full projective
centralizer order by four times the ordinary centralizer order. This
retains lifts that anticommute with the involution, and neither resulting
bound is divisible by 27.

An order-two subgroup contains a nonidentity involution; centralizer
containment then proves the subgroup version. Elementary abelianness need
not be assumed separately at order two.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Subgroup
noncomputable section
namespace Matrix.PSL4Three.LocalThree

/-- The full projective centralizer of any nonidentity involution has no factor 27. -/
public theorem projective_involution_centralizer_three_part (z : P) (hne : z ≠ 1)
    (hsq : z ^ 2 = 1) : ¬ 3 ^ 3 ∣ Nat.card (centralizer ({z} : Set P)) := by
  obtain ⟨g, rfl⟩ := project_surjective z
  have hker : project.ker = center SL := by
    ext x
    exact project_eq_one_iff x
  have hd : Nat.card (centralizer ({project g} : Set P)) ∣
      4 * Nat.card (centralizer ({g} : Set SL)) := by
    have h := centralizer_pair_card_dvd_of_central_kernel project project_surjective
      (le_of_eq hker) g g
    rw [Set.insert_eq_of_mem (Set.mem_singleton (project g)),
      Set.insert_eq_of_mem (Set.mem_singleton g), hker, card_center,
      show (2 : ℕ) ^ 2 = 4 by decide] at h
    exact h
  obtain ⟨c, hc, he⟩ := square_scalar g hsq
  have hc' : c = 1 ∨ c = -1 :=
    (by decide : ∀ c : ZMod 3, c ^ 2 = 1 → c = 1 ∨ c = -1) c hc
  have ht := trace_eq_zero_of_projective_involution g hne hsq
  intro hdiv
  rcases hc' with rfl | rfl
  · have h := InvolutionCentralizer.split_card_dvd g (by simpa [pow_two] using he) ht
    have hb := hdiv.trans (hd.trans (Nat.mul_dvd_mul_left 4 h))
    exact (by decide : ¬ 3 ^ 3 ∣ 4 * 2304) hb
  · have h := InvolutionCentralizer.nonsplit_card_dvd g (by simpa [pow_two] using he)
    have hb := hdiv.trans (hd.trans (Nat.mul_dvd_mul_left 4 h))
    exact (by decide : ¬ 3 ^ 3 ∣ 4 * 5760) hb

/-- The centralizer of every order-two subgroup has three-part at most nine. -/
public theorem centralizer_three_part_of_card_eq_two
    (A : Subgroup P) (hA : Nat.card A = 2) :
    ¬ 3 ^ 3 ∣ Nat.card (centralizer (A : Set P)) := by
  obtain ⟨a, hane, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hsq : (a : P) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hA] at h
    exact congrArg Subtype.val h
  have hne : (a : P) ≠ 1 := fun h => hane (Subtype.ext h)
  have hle : centralizer (A : Set P) ≤ centralizer ({(a : P)} : Set P) :=
    centralizer_le (Set.singleton_subset_iff.mpr a.property)
  intro hd
  exact projective_involution_centralizer_three_part a hne hsq
    (hd.trans (card_dvd_of_le hle))
end Matrix.PSL4Three.LocalThree
