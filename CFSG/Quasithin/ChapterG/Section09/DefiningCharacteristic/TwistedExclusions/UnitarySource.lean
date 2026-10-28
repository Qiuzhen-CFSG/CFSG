module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
public import Theory.Representation.SU3.BinaryDegree
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Special
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# Excluding the actual special and projective unitary rows

For every nonbinary exponent, the actual SU3 cover gives degree at least
6n, while its special or projective automorphism rank is at most n+1.
The original G.9 degree bound contradicts these estimates. At the binary
endpoint the projective carrier is solvable; its special central extension
is solvable too. The argument retains arbitrary Hermitian forms and both
actual matrix models, with no separate central-quotient identification.

Source: Aschbacher–Smith G.9.3, printed p.356; A.3.6, printed p.43.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : GroupClass} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ} [Field F] [Finite F]

/-- The actual nonbinary special or projective unitary model is excluded. -/
theorem not_unitary_three_of_actual_model
    (h : ComponentHypothesis K ρ A L L m)
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (L ≃* J.specialSubgroup) ∨
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hm : m ≤ primeRank 2 (MulAut L) := h.toSetup.rank_le_automorphisms (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]; exact le_top)
  have hr : primeRank 2 (MulAut L) ≤ n+1 := by
    rcases model with hs | hp
    · obtain ⟨e⟩ := hs
      rw [primeRank_equiv 2 (MulAut.congr e)]
      exact HermitianForm.EvenTwoRank.special_automorphism_two_rank_le J hn hcard
        (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj)
    · obtain ⟨e⟩ := hp
      rw [primeRank_equiv 2 (MulAut.congr e)]
      exact HermitianForm.EvenTwoRank.automorphism_two_rank_le J hn hcard hconj
  obtain ⟨π,hπ,_⟩ := exists_unitary_cover J model
  have hdeg := degree_ge_of_cover h π hπ
    (fun σ hi ha => Representation.SU3.BinaryDegree.finrank_ge_of_irreducible
      J hn hcard hconj σ hi ha)
  have hu := h.degree_le
  omega

/-- Both literal binary endpoint carriers are solvable, so cannot be components. -/
theorem not_unitary_three_binary_endpoint
    (h : ComponentHypothesis K ρ A L L m)
    (J : HermitianForm 3 F)
    (hcard : Nat.card F = 2 ^ 2) (hconj : ∀ x, J.conj x = x ^ 2)
    (model : Nonempty (L ≃* J.specialSubgroup) ∨
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  rcases model with hs | hp
  · obtain ⟨e⟩ := hs
    let f := J.specialToProjective
    let : Group.IsSolvable (center J.specialSubgroup) := Group.isSolvable_of_comm fun x y =>
      Subtype.ext ((mem_center_iff.mp x.property y).symm)
    let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective J.specialToProjective_ker_le_center)
    let : Group.IsSolvable J.specialSubgroup :=
      Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])
    exact Group.IsPerfect.not_isSolvable L
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨e⟩ := hp
    exact Group.IsPerfect.not_isSolvable L
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- All positive binary exponents are excluded, retaining the actual cover. -/
theorem not_unitary_three_positive_exponent
    (h : ComponentHypothesis K ρ A L L m)
    (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (model : Nonempty (L ≃* J.specialSubgroup) ∨
      Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  by_cases hn1 : n = 1
  · subst n
    exact not_unitary_three_binary_endpoint h J (by simpa using hcard)
      (by simpa using hconj) model
  · exact not_unitary_three_of_actual_model h J (by omega) hcard hconj model
end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
