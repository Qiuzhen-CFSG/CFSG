module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification.Candidates
import Mathlib.Tactic.FinCases

/-!
# Encoding Janko's finite permutation check

A permutation satisfying `n * m * n⁻¹ = m²` is determined by its images of
1, 2, 12, 13 and its permutation of the two fixed points 0 and 11. On each
five-cycle, the other images follow by successive applications of `m²`.
`exists_candidateTable` proves this reconstruction for every such permutation.

For the computation we allow all 22 choices for each of the four images,
including choices which cannot define a permutation. The necessary square,
fourth-power and fixed-point tests discard these extra functions. The product
profiles imply the cheaper necessary test that point 1 returns after one of
5, 6, 7, 8, 11 steps. The certificate module exhausts this finite superset;
it never enumerates the symmetric group of order 22!.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 9, p.18, DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification.Enumeration
open JankoModel

public section
set_option maxRecDepth 100000

@[expose] def mSquare (x : Fin 22) : Fin 22 :=
  match x.val with
  | 0 => 0
  | 1 => 5
  | 2 => 10
  | 3 => 4
  | 4 => 9
  | 5 => 3
  | 6 => 8
  | 7 => 2
  | 8 => 7
  | 9 => 1
  | 10 => 6
  | 11 => 11
  | 12 => 16
  | 13 => 21
  | 14 => 15
  | 15 => 20
  | 16 => 14
  | 17 => 19
  | 18 => 13
  | 19 => 18
  | 20 => 12
  | _ => 17

theorem mSquare_apply : ∀ x, mSquare x = (m ^ 2) x := by decide +kernel

@[expose] def candidateTable (a b c d : Fin 22) (s : Fin 2) (x : Fin 22) : Fin 22 :=
  match x.val with
  | 0 => if s = 0 then 0 else 11
  | 1 => a
  | 2 => b
  | 3 => mSquare (mSquare (mSquare (mSquare a)))
  | 4 => mSquare a
  | 5 => mSquare (mSquare a)
  | 6 => mSquare (mSquare (mSquare (mSquare b)))
  | 7 => mSquare (mSquare (mSquare b))
  | 8 => mSquare b
  | 9 => mSquare (mSquare (mSquare a))
  | 10 => mSquare (mSquare b)
  | 11 => if s = 0 then 11 else 0
  | 12 => c
  | 13 => d
  | 14 => mSquare (mSquare (mSquare (mSquare c)))
  | 15 => mSquare c
  | 16 => mSquare (mSquare c)
  | 17 => mSquare (mSquare (mSquare (mSquare d)))
  | 18 => mSquare (mSquare (mSquare d))
  | 19 => mSquare d
  | 20 => mSquare (mSquare (mSquare c))
  | _ => mSquare (mSquare d)

@[expose] def fixedCount (f : Fin 22 → Fin 22) : ℕ := (Finset.univ.filter (fun x => f x = x)).card

@[expose] def HasShortOrbit (f : Fin 22 → Fin 22) : Prop :=
  f^[5] 1 = 1 ∨ f^[6] 1 = 1 ∨ f^[7] 1 = 1 ∨ f^[8] 1 = 1 ∨ f^[11] 1 = 1

instance (f : Fin 22 → Fin 22) : Decidable (HasShortOrbit f) := inferInstanceAs (Decidable (_ ∨ _))

@[expose] def ellStep (x : Fin 22) : Fin 22 :=
  if x = 0 then 12 else if x = 11 then 1 else if x = 21 then 0 else x + 1

@[expose] def PassesTests (f : Fin 22 → Fin 22) : Prop :=
  f (f 1) = 1 ∧ f (f 3) = 4 ∧ f (f 5) = 9 ∧
  f^[4] 2 = 2 ∧ f^[4] 12 = 12 ∧ f^[4] 13 = 13 ∧
  fixedCount f = 2 ∧ fixedCount (fun x => f (f x)) = 6 ∧
  ∀ i : Fin 11, HasShortOrbit (fun x => ellStep^[i.val] (f x))

instance (f : Fin 22 → Fin 22) : Decidable (PassesTests f) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def IsSurvivor (a b c d : Fin 22) (s : Fin 2) : Prop :=
  (a = 12 ∧ b = 6 ∧ c = 1 ∧ d = 17 ∧ s = 1) ∨
  (a = 1 ∧ b = 16 ∧ c = 7 ∧ d = 18 ∧ s = 1) ∨
  (a = 1 ∧ b = 21 ∧ c = 12 ∧ d = 10 ∧ s = 1) ∨
  (a = 21 ∧ b = 10 ∧ c = 14 ∧ d = 4 ∧ s = 1)
instance (a b c d : Fin 22) (s : Fin 2) : Decidable (IsSurvivor a b c d s) :=
  inferInstanceAs (Decidable (_ ∨ _))
private def base : Fin 6 → Fin 22 := ![1,2,12,13,0,11]
private def orbit : Fin 22 → Fin 6 := ![4,0,1,0,0,0,1,1,1,0,1,5,2,3,2,2,2,3,3,3,2,3]
private def phase : Fin 22 → ℕ := ![0,0,0,4,1,2,4,3,1,3,2,0,0,0,4,1,2,4,3,1,3,2]

private theorem cover : ∀ x, (m ^ phase x) (base (orbit x)) = x := by decide +kernel
private theorem table_formula (a b c d : Fin 22) (s : Fin 2) (x : Fin 22) :
    candidateTable a b c d s x = mSquare^[phase x]
      (![a,b,c,d,if s = 0 then 0 else 11,if s = 0 then 11 else 0] (orbit x)) := by
  fin_cases x <;> rfl

private theorem step_fixed : ∀ x, mSquare x = x ↔ x = 0 ∨ x = 11 := by decide +kernel
private theorem m_zero : m 0 = 0 := by decide +kernel
private theorem m_eleven : m 11 = 11 := by decide +kernel

attribute [local irreducible] m mSquare
theorem exists_candidateTable (n : Equiv.Perm (Fin 22)) (hn : n * m * n⁻¹ = m ^ 2) :
    ∃ a b c d : Fin 22, ∃ s : Fin 2, (n : Fin 22 → Fin 22) = candidateTable a b c d s := by
  have hnm : n * m = m ^ 2 * n := mul_inv_eq_iff_eq_mul.mp hn
  have h : Function.Semiconj n m mSquare := by
    intro x
    exact (congrArg (fun g : Equiv.Perm (Fin 22) => g x) hnm).trans
      (mSquare_apply (n x)).symm
  have h0 : n 0 = 0 ∨ n 0 = 11 := by
    apply (step_fixed _).mp
    exact (h 0).symm.trans (congrArg n m_zero)
  have h11 : n 11 = 0 ∨ n 11 = 11 := by
    apply (step_fixed _).mp
    exact (h 11).symm.trans (congrArg n m_eleven)
  have hz : n 0 ≠ n 11 := fun he => (by decide : (0 : Fin 22) ≠ 11) (n.injective he)
  have hs : ∃ s : Fin 2, n 0 = (if s = 0 then 0 else 11) ∧
      n 11 = (if s = 0 then 11 else 0) := by
    rcases h0 with h0 | h0 <;> rcases h11 with h11 | h11
    · exact False.elim (hz (h0.trans h11.symm))
    · exact ⟨0, h0, h11⟩
    · exact ⟨1, h0, h11⟩
    · exact False.elim (hz (h0.trans h11.symm))
  obtain ⟨s, hs0, hs11⟩ := hs
  refine ⟨n 1, n 2, n 12, n 13, s, ?_⟩
  have hbase : ∀ i : Fin 6, n (base i) =
      ![n 1,n 2,n 12,n 13,if s = 0 then 0 else 11,if s = 0 then 11 else 0] i := by
    intro i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hs0
    · exact hs11
  funext x
  calc
    n x = n ((m ^ phase x) (base (orbit x))) := congrArg n (cover x).symm
    _ = mSquare^[phase x] (n (base (orbit x))) := (h.iterate_right (phase x)) _
    _ = mSquare^[phase x]
        (![n 1,n 2,n 12,n 13,if s = 0 then 0 else 11,if s = 0 then 11 else 0] (orbit x)) :=
      congrArg (mSquare^[phase x]) (hbase _)
    _ = candidateTable (n 1) (n 2) (n 12) (n 13) s x := (table_formula _ _ _ _ _ _).symm

theorem ellStep_eq : ellStep = (ell : Fin 22 → Fin 22) := by decide +kernel

theorem hasShortOrbit_of_allowed (g : Equiv.Perm (Fin 22)) (hg : HasAllowedProfile g) : HasShortOrbit g := by
  have hd : orderOf g ∣ 5 ∨ orderOf g ∣ 6 ∨ orderOf g ∣ 7 ∨
      orderOf g ∣ 8 ∨ orderOf g ∣ 11 := by
    simp only [HasAllowedProfile, allowedOrderFixedPairs, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at hg
    rcases hg with ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ |
      ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩
    all_goals rw [ho]; decide
  have hp (d : ℕ) (hd : orderOf g ∣ d) : (g : Fin 22 → Fin 22)^[d] 1 = 1 :=
    congrArg (fun q : Equiv.Perm (Fin 22) => q 1) (orderOf_dvd_iff_pow_eq_one.mp hd)
  rcases hd with hd | hd | hd | hd | hd
  · exact Or.inl (hp 5 hd)
  · exact Or.inr (Or.inl (hp 6 hd))
  · exact Or.inr (Or.inr (Or.inl (hp 7 hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hp 8 hd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hp 11 hd))))

theorem passesTests_of_source (n : Equiv.Perm (Fin 22))
    (ho : orderOf n = 4) (hf : fixedCount n = 2)
    (hs : fixedCount ⇑(n ^ 2) = 6) (hn : SquareNormalized n)
    (hp : ∀ i : Fin 11, HasAllowedProfile (ell ^ i.val * n)) : PassesTests n := by
  have hfour (x : Fin 22) : (n : Fin 22 → Fin 22)^[4] x = x := by
    have he : n ^ 4 = 1 := ho ▸ pow_orderOf_eq_one n
    exact congrArg (fun g : Equiv.Perm (Fin 22) => g x) he
  refine ⟨hn.1, hn.2.1, hn.2.2.1, hfour 2, hfour 12, hfour 13, hf, hs, ?_⟩
  intro i
  have he : (fun x => ellStep^[i.val] (n x)) = ⇑(ell ^ i.val * n) := by
    rw [ellStep_eq]
    rfl
  rw [he]
  exact hasShortOrbit_of_allowed (ell ^ i.val * n) (hp i)

theorem candidateTable_n1 : candidateTable 12 6 1 17 1 = ⇑n1 := by decide +kernel
theorem candidateTable_n2 : candidateTable 1 16 7 18 1 = ⇑n2 := by decide +kernel
theorem candidateTable_n3 : candidateTable 1 21 12 10 1 = ⇑n3 := by decide +kernel
theorem candidateTable_n4 : candidateTable 21 10 14 4 1 = ⇑n4 := by decide +kernel

end
end Theory.GroupTheory.HeldM22A10.M22Identification.PermutationClassification.Enumeration
