module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
import Mathlib.Tactic.Group

/-!
# Adjusting Janko's order-four generator

If a permutation conjugates Janko's `m` to its square and its own square has
six fixed points, conjugation by a power of `m` gives the square conditions
used in the terminal enumeration. The square inverts `m`. Its fixed points
inject into the six `m`-orbits, so it has one in every orbit; a power of `m`
moves the point in the first five-cycle to 1. This changes the generator `n`
and leaves the selected eleven- and five-generators in the subgroup.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), p.18, DOI 10.1016/0021-8693(68)90002-1.
The scan replaces `n` by `n^(m^i)`. Here conjugation acts on the left;
all five powers are available, so reversing the conjugator has no effect
on the existence statement. The source label 22 is 0 in `Fin 22`.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
open JankoModel

set_option maxRecDepth 100000

private def mOrbit : Fin 22 → Fin 6 := fun x =>
  if x = 11 then 4 else if x = 0 then 5 else
  if x ∈ ({1, 4, 5, 9, 3} : Finset (Fin 22)) then 0 else
  if x ∈ ({2, 8, 10, 7, 6} : Finset (Fin 22)) then 1 else
  if x ∈ ({12, 15, 16, 20, 14} : Finset (Fin 22)) then 2 else 3

private theorem same_orbit_compare : ∀ x y : Fin 22, mOrbit x = mOrbit y →
    ∃ i : Fin 5, (m ^ i.val) x = y ∧ ((m ^ (4 * i.val)) x = y → x = y) := by
  decide +kernel

private theorem fixed_injective (s : Equiv.Perm (Fin 22))
    (hs : SemiconjBy s m (m ^ 4)) :
    Function.Injective (fun x : {x : Fin 22 // s x = x} => mOrbit x.val) := by
  intro x y hxy
  obtain ⟨i, hi, huniq⟩ := same_orbit_compare x y hxy
  apply Subtype.ext
  apply huniq
  have h := congrArg (fun g : Equiv.Perm (Fin 22) => g x) (hs.pow_right i.val).eq
  simpa only [Equiv.Perm.mul_apply, pow_mul, hi, x.property, y.property] using h.symm

private theorem orbit_singletons : ∀ x : Fin 22,
    (mOrbit x = 4 → x = 11) ∧ (mOrbit x = 5 → x = 0) := by
  decide +kernel

private theorem orbit_first (x : Fin 22) (hx : mOrbit x = 0) :
    ∃ i : Fin 5, (m ^ i.val) x = 1 := by
  obtain ⟨i, hi, _⟩ := same_orbit_compare x 1 hx
  exact ⟨i, hi⟩

private theorem m_pow_conj (k : ℕ) : (MulAut.conj (m ^ k)) m = m := by
  change m ^ k * m * (m ^ k)⁻¹ = m
  rw [(Commute.refl m).pow_left k |>.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem normalize_reflection (s : Equiv.Perm (Fin 22))
    (hs : SemiconjBy s m (m ^ 4))
    (hfixed : (Finset.univ.filter (fun x => s x = x)).card = 6) :
    ∃ i : Fin 5, let t := (MulAut.conj (m ^ i.val)) s
      t 1 = 1 ∧ t 3 = 4 ∧ t 5 = 9 ∧ t 11 = 11 ∧ t 0 = 0 := by
  have hf : Function.Surjective (fun x : {x : Fin 22 // s x = x} => mOrbit x.val) :=
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fixed_injective s hs, by simpa only [Fintype.card_subtype, Fintype.card_fin] using hfixed⟩).2
  obtain ⟨x, hx⟩ := hf 0
  obtain ⟨i, hi⟩ := orbit_first x hx
  obtain ⟨a, ha⟩ := hf 4
  obtain ⟨b, hb⟩ := hf 5
  have hs11 : s 11 = 11 := (orbit_singletons a).1 ha ▸ a.property
  have hs0 : s 0 = 0 := (orbit_singletons b).2 hb ▸ b.property
  let t := (MulAut.conj (m ^ i.val)) s
  have ht1 : t 1 = 1 := by
    change (m ^ i.val) (s ((m ^ i.val)⁻¹ 1)) = 1
    rw [← hi]
    have hinv : (m ^ i.val)⁻¹ ((m ^ i.val) x) = x := by
      change ((m ^ i.val)⁻¹ * (m ^ i.val)) x = x
      rw [inv_mul_cancel, Equiv.Perm.one_apply]
    rw [hinv, x.property]
  have htm : SemiconjBy t m (m ^ 4) := by
    let f := MulAut.conj (m ^ i.val)
    change f s * m = m ^ 4 * f s
    calc
      f s * m = f s * f m := by rw [m_pow_conj]
      _ = f (s * m) := (f.map_mul s m).symm
      _ = f (m ^ 4 * s) := congrArg f hs.eq
      _ = f (m ^ 4) * f s := f.map_mul _ _
      _ = m ^ 4 * f s := by rw [map_pow f, m_pow_conj]
  have ht3 : t 3 = 4 := by
    have h := congrArg (fun g : Equiv.Perm (Fin 22) => g 1) (htm.pow_right 4).eq
    have ha : (m ^ 4) 1 = 3 := by decide +kernel
    have hb : ((m ^ 4) ^ 4) 1 = 4 := by decide +kernel
    simpa only [Equiv.Perm.mul_apply, ha, ht1, hb] using h
  have ht5 : t 5 = 9 := by
    have h := congrArg (fun g : Equiv.Perm (Fin 22) => g 1) (htm.pow_right 2).eq
    have ha : (m ^ 2) 1 = 5 := by decide +kernel
    have hb : ((m ^ 4) ^ 2) 1 = 9 := by decide +kernel
    simpa only [Equiv.Perm.mul_apply, ha, ht1, hb] using h
  have hmfix : ∀ j : Fin 5, (m ^ j.val) 11 = 11 ∧ (m ^ j.val) 0 = 0 ∧
      (m ^ j.val)⁻¹ 11 = 11 ∧ (m ^ j.val)⁻¹ 0 = 0 := by decide +kernel
  refine ⟨i, ?_⟩
  refine ⟨ht1, ht3, ht5, ?_, ?_⟩
  · change (m ^ i.val) (s ((m ^ i.val)⁻¹ 11)) = 11
    rw [(hmfix i).2.2.1, hs11, (hmfix i).1]
  · change (m ^ i.val) (s ((m ^ i.val)⁻¹ 0)) = 0
    rw [(hmfix i).2.2.2, hs0, (hmfix i).2.1]

/-- Adjust the order-four generator by a power of the fixed order-five element.
Only the normalizer relation and the six fixed points of its square are needed. -/
public theorem exists_power_squareNormalized (n : Equiv.Perm (Fin 22))
    (hconj : n * m * n⁻¹ = m ^ 2)
    (hfixed : (Finset.univ.filter (fun x => (n ^ 2) x = x)).card = 6) :
    ∃ i : Fin 5, SquareNormalized ((MulAut.conj (m ^ i.val)) n) := by
  have hn : SemiconjBy n m (m ^ 2) := by
    change n * m = m ^ 2 * n
    rw [← hconj, mul_assoc, inv_mul_cancel, mul_one]
  have hs : SemiconjBy (n ^ 2) m (m ^ 4) := by
    have h4 : (m ^ 2) ^ 2 = m ^ 4 := by group
    simpa only [← pow_two, h4] using (hn.pow_right 2).mul_left hn
  obtain ⟨i, hi⟩ := normalize_reflection (n ^ 2) hs hfixed
  refine ⟨i, ?_⟩
  unfold SquareNormalized
  rw [← map_pow (MulAut.conj (m ^ i.val)) n 2]
  exact hi

end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification
