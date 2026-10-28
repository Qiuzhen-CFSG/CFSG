module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.Frames
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.OrthogonalFrames
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.SolvableFrames
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement.SylowBound

/-!
# Geometric placement of the nonabelian lift of a projective order-nine pair

The full special-unitary preimage of UT is solvable, has only two and three
as prime divisors, and contains the nonabelian three-group above U. It also
contains a full ambient Sylow two-subgroup, whose order is greater than eight.
Thus the small-Sylow alternative in the solvable degree-three representation
argument is impossible. An invariant orthogonal frame then gives the required
actual matrix conjugation equivalence and monomial containment.

The conditional reduction separates frame existence and orthogonalization.
The final `monomial_placement` theorem discharges both steps using their proved
geometric interfaces, which apply to the full lifted product. No `PairInput`
hypotheses are needed here. Neither exponent three for the lifted subgroup
nor impossibility of all permuting pairs is asserted.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), and A.3.21(b)–(c), printed pp.55–56; GLS3, proof of
Theorem 6.5.3(a)–(d), especially (6.5.1), `refs/KGroup/GLS3/chapter6.tex`.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift

open ModTwoExtraspecial.Placement

variable {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : IsElementaryAbelian 3 U) (hc : Nat.card U = 9)
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective))
    (hperm : (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) =
      (T : Set _) * (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)))

include he hc hn hperm in
/-- The lifted product has no prime divisors other than two and three. -/
theorem preimage_product_prime_divisors
    (r : ℕ) (hr : r.Prime)
    (hd : r ∣ Nat.card ((U ⊔ (T : Subgroup _)).comap J.specialToProjective)) :
    r = 2 ∨ r = 3 := by
  rw [preimage_product_card J T U he hc hperm hn] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow (show r ∣ 3 ^ 3 from hd)))
  · let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    obtain ⟨n, hncard⟩ := T.isPGroup'.exists_card_eq
    rw [hncard] at hd
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hd))

/-- A full ambient Sylow two-subgroup lies in the preimage and has order
greater than eight, the bound for the primitive solvable alternative. -/
theorem preimage_product_contains_large_sylow
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hE : Nat.card E = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    ∃ S : Sylow 2 J.specialSubgroup,
      (S : Subgroup J.specialSubgroup) ≤
        (U ⊔ (T : Subgroup _)).comap J.specialToProjective ∧ 8 < Nat.card S := by
  obtain ⟨S, hS, _⟩ := exists_special_sylow J T
  refine ⟨S, ?_, eight_lt_special_sylow_card J p hp ho hE hconj S⟩
  apply map_le_iff_le_comap.mp
  rw [hS]
  exact le_sup_right

/-- Conditional placement from the two independent geometric steps. Every
other premise is discharged for the actual full preimage of the pair. -/
theorem monomial_placement_of_representation_steps
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hframes : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup, Group.IsSolvable H →
        (∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3) →
        (∃ R : Subgroup J.specialSubgroup, R ≤ H ∧ IsPGroup 3 R ∧ ¬ IsMulCommutative R) →
        HasFrame H ∨ ∀ S : Sylow 2 H, Nat.card S ≤ 8)
    (horthogonal : ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
      Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
      ∀ H : Subgroup J.specialSubgroup,
        (∃ R : Subgroup J.specialSubgroup, R ≤ H ∧ IsPGroup 3 R ∧ ¬ IsMulCommutative R) →
        HasFrame H → HasOrthogonalFrame H) : MonomialPlacement p := by
  intro E _ _ J _ hE hconj T U he hc hn hperm
  let H := (U ⊔ (T : Subgroup _)).comap J.specialToProjective
  have hR : ∃ R : Subgroup J.specialSubgroup,
      R ≤ H ∧ IsPGroup 3 R ∧ ¬ IsMulCommutative R :=
    ⟨U.comap J.specialToProjective, comap_mono le_sup_left,
      (preimage_three_group_card J U he hc hn).1, hn⟩
  have hframe : HasFrame H := by
    rcases hframes E J hE hconj H (preimage_product_solvable J T U he hc hperm hn)
      (preimage_product_prime_divisors J T U he hc hn hperm) hR with hframe | hsmall
    · exact hframe
    · obtain ⟨S, hSH, hSlarge⟩ := preimage_product_contains_large_sylow J T U p hp ho hE hconj
      have hsmallS := hsmall (S.subtype hSH)
      have hcard : Nat.card (S.subtype hSH) = Nat.card S :=
        Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv
      rw [hcard] at hsmallS
      exact (hSlarge.not_ge hsmallS).elim
  obtain ⟨C, hC, hpres⟩ := horthogonal E J hE hconj H hR hframe
  refine ⟨identityGram J, hconj, identityGram_form J, specialEquiv J C hC, ?_⟩
  exact special_map_le_monomial_of_frame H C hC hpres

/-- The full special-unitary preimage of a permuting projective order-nine
pair is monomial in an orthonormal basis over the original quadratic field. -/
theorem monomial_placement (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hlarge : 3 < p) (hmod : p % 3 = 2) : MonomialPlacement p := by
  apply monomial_placement_of_representation_steps p hp ho
  · intro E _ _ J hE hconj H hsolv hprimes hU
    exact frame_or_small_sylow hp ho hlarge hmod J hE hconj H hsolv hprimes hU
  · exact orthogonalFrame_of_frame p hp ho hlarge hmod

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.NonabelianLift
