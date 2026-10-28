module

public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients.Primitivity
public import Theory.SpecificGroups.PSp4Three.Simplicity
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Simplicity and nontrivial quotients of PSp₄(F)

For a finite field with more than three elements, choose a nonzero scalar c
with c² ≠ 1. Conjugation by an element sending v to cv expresses every
symplectic transvection as a commutator. Transvection generation proves
perfectness. The faithful primitive projective action and its abelian
line-transvection groups then give simplicity by Iwasawa's criterion.

The carrier below is the standard matrix symplectic group modulo its full
center. It is definitionally the same carrier as `ClassicalGroup.PSp 2 F`;
no recognition hypothesis or change of alternating form is involved.

Adapted from Gerald Höhn, ATLAS, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
`Atlas/LinearGroups/Symplectic/{PerfectLarge,SimplicityHighRank}.lean`.
Covered by the ATLAS Research and Attribution License 1.0; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
Changes: specialize to rank two and field order greater than three, reuse
CFSG's generic `Matrix.PSp4Three` Iwasawa structure, and expose the actual
central quotient without importing classification modules into Theory.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.SimpleQuotients

open Matrix.PSp4Three
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F]

private theorem exists_scalar_square_ne_one (hq : 3 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c ^ 2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2⟩

private theorem perfect (hq : 3 < Nat.card F) : Group.IsPerfect (Sp 2 F) := by
  obtain ⟨c, hc, hc₂⟩ := exists_scalar_square_ne_one hq
  apply perfect_of_transvections
  intro v a
  by_cases hv : v = 0
  · subst v
    simp
  obtain ⟨g, _, hg⟩ := exists_generated_send hv (smul_ne_zero hc hv)
  let b := a / (c ^ 2 - 1)
  have hb : (c ^ 2 - 1) * b = a := mul_div_cancel₀ a (sub_ne_zero.mpr hc₂)
  have he : ⁅g, transvection v b⁆ = transvection v a := by
    rw [commutatorElement_def, transvection_conjugate, hg, transvection_scale,
      transvection_inverse, ← transvection_add]
    congr 1
    calc
      c ^ 2 * b + -b = (c ^ 2 - 1) * b := by ring
      _ = a := hb
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- PSp₄(F), defined as the actual central quotient, is simple for |F| > 3. -/
theorem isSimpleGroup (hq : 3 < Nat.card F) :
    IsSimpleGroup ((Matrix.symplecticGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) := by
  let := projective_preprimitive (F := F)
  let := projective_nontrivial (F := F) (n := 2) (by decide)
  let := perfect hq
  let : Group.IsPerfect (PSp 2 F) := inferInstance
  exact iwasawa.isSimpleGroup (Group.IsPerfect.commutator_eq_top (G := PSp 2 F))
    inferInstance

/-- In particular this covers the two-power fields occurring in the Ree
symplectic subgroups, whose exponents are 2m + 1 with m ≥ 1. -/
theorem isSimpleGroup_of_card_eq_two_pow {f : ℕ} (hf : 2 ≤ f)
    (hF : Nat.card F = 2 ^ f) :
    IsSimpleGroup ((Matrix.symplecticGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) := by
  apply isSimpleGroup
  rw [hF]
  have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2) h

/-- Every nontrivial quotient of the whole projective symplectic carrier is
isomorphic to that carrier. This includes all its simple quotients. -/
theorem nonempty_mulEquiv_of_surjective (hq : 3 < Nat.card F)
    {S : Type*} [Group S] [Nontrivial S]
    (f : ((Matrix.symplecticGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F)) →* S)
    (hf : Function.Surjective f) :
    Nonempty (S ≃* ((Matrix.symplecticGroup (Fin 2) F) ⧸
      Subgroup.center (Matrix.symplecticGroup (Fin 2) F))) := by
  let := isSimpleGroup hq
  exact ⟨(MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf, hf⟩).symm⟩

end Theory.SpecificGroups.SymplecticFour.SimpleQuotients
