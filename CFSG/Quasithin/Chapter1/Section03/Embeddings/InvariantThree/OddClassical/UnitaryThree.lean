module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial
public import Theory.SpecificGroups.SU3.OddThreeLocal.CyclicSylow
public import Theory.SpecificGroups.SU3.OddThreeLocal.SmallField

/-!
# Odd unitary degree-three Sylow pairs

For prime fixed-field order p ≡ 1 modulo three, every Sylow three-subgroup
of the actual PSU₃(p) matrix group is cyclic. The central-image reduction
therefore excludes nonreducible pairs in every quasisimple central cover,
without a Schur-multiplier assumption.

For p = 3, the action on the 28 isotropic points excludes permuting
products with central image of order nine or 27. This also handles every
central cover without a multiplier hypothesis. Thus a nonreducible pair
would require p > 3 and p ≡ 2 modulo three. In that case, the order-nine
branch handles both abelian and nonabelian special-unitary lifts, and the
extraspecial branch constructs the invariant local three-core of order nine.
These calculations control the full pair automizer, including outer actions.

`reducible_of_psu_three` assembles all odd prime parameters and both complement
orders. Its only earlier-result parameter is `UnitaryThree.ModTwoExtraspecial.PrimeCover`,
the universal cover implication from I.1.3 with actual SU₃ or PSU₃ equivalences.
Every local subgroup and action premise is discharged. Throughout, p is the
fixed-field order: the matrix field has order p² and conjugation x ↦ x^p.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The cyclic-Sylow branch includes all central covers of PSU₃(p). -/
theorem reducible_of_psu_three_mod_one {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  apply reducible_of_cyclic_three_sylow h
  intro P
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc := HermitianForm.OddThreeLocal.cyclic_three_sylow_of_prime_mod_one
    J p hp hmod hcard hconj P'
  change IsCyclic ((P : Subgroup _).map e.toMonoidHom) at hc
  let _ := hc
  let eP := (P : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_injective eP.toMonoidHom eP.injective

/-- The degree-28 subgroup exclusion applies to every central cover of PSU₃(3). -/
theorem reducible_of_psu_three_three {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 3) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (center Q)
  let f : Q →* ProjectiveSpecialUnitaryMatrixGroup J := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S' := S.mapSurjective (f := f) hf
  let U := R.map f
  have hc : Nat.card U = Nat.card (R.map q) := by
    dsimp only [U, f]
    rw [← Subgroup.map_map]
    exact card_map_of_injective e.injective
  have hU : Nat.card U = 9 ∨ Nat.card U = 27 := by
    rw [hc]
    exact central_image_card h hn
  apply HermitianForm.OddThreeLocal.not_permuting_three_three J hcard hconj S' U hU
  have hh := congrArg (Set.image f) h.permutes
  change (R.map f : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
      ((S : Subgroup Q).map f : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
    ((S : Subgroup Q).map f : Set (ProjectiveSpecialUnitaryMatrixGroup J)) *
      (R.map f : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  simpa only [Set.image_mul, Subgroup.coe_map, Sylow.coe_coe] using hh

/-- The only remaining unitary parameters for a nonreducible pair. -/
theorem nonreducible_psu_three_parameters {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p)
    (hn : ¬ PairReducible (S : Subgroup Q) R) : 3 < p ∧ p % 3 = 2 := by
  have h3 : p ≠ 3 := by
    intro he
    subst p
    exact hn (reducible_of_psu_three_three h hm)
  have h1 : p % 3 ≠ 1 := fun hmod => hn (reducible_of_psu_three_mod_one h p hp hmod hm)
  have h0 : p % 3 ≠ 0 := by
    intro hmod
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with he | he
    · norm_num at he
    · exact h3 he.symm
  have hp2 := hp.two_le
  obtain ⟨k, hk⟩ := ho
  omega

/-- The odd PSU₃ branch of the three-complement sieve, including every central
cover supplied by the universal earlier cover theorem. No local exclusion or
action calculation remains an assumption. -/
theorem reducible_of_psu_three
    (hcover : UnitaryThree.ModTwoExtraspecial.PrimeCover.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 p) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  obtain ⟨hlarge, hmod⟩ := nonreducible_psu_three_parameters h p hp ho hm hn
  rcases h.oddComplement with ⟨_, hcard⟩ | ⟨_, hcard, _⟩
  · exact hn (reducible_of_psu_three_mod_two_elementary h (by simpa using hcard)
      p hp ho hlarge hmod hm)
  · exact hn (UnitaryThree.ModTwoExtraspecial.reducible p hcover hp ho hlarge hmod
      h (by simpa using hcard) hm)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
