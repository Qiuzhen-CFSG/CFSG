module
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.PSL3Three.SylowFixers
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Prime-field and ternary linear actions in 1.1.5

The actual field witness and inherited perfectness exclude the degenerate
PSL₂ parameters. Prime-field projective semilinear coverage identifies a
pointwise Sylow fixer as inner. For PSL₃(3), the proved bound of two on the
full Sylow fixer, together with a nonidentity inner automorphism supplied by
the Sylow center, gives the same conclusion. The common central-quotient
transport then retains innerness of the original automorphism and identifies
its center with its two-core.

The final applications produce row (e) after the independent arithmetic and
cover exclusions. These premises remain explicit: the full odd-family
classification is not asserted here.
Source: Aschbacher--Smith, 1.1.5(3)(e), printed pp.502--503.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

omit [Finite L] in
/-- Nonsolvability of the genuine central quotient excludes fields of order
at most three, including the exponent-zero and prime-three endpoints. -/
theorem linear_two_field_large {q : ℕ} (hq : Odd q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : 3 < q := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial PSL(2,F) := e.symm.toEquiv.nontrivial
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rw [← hcard]
  exact Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    (hcard ▸ hq) (Group.IsPerfect.not_isSolvable _)

omit [Finite L] in
/-- The source exponent bound leaves a genuine prime or a square; the prime
branch has order greater than three. -/
theorem linear_two_exponent {p e : ℕ} (ho : Odd p) (he : e ≤ 2)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ e)) :
    (e = 1 ∧ 3 < p) ∨ e = 2 := by
  have hl := linear_two_field_large ho.pow h
  have he0 : e ≠ 0 := by intro h0; simp [h0] at hl
  have hsplit : e = 1 ∨ e = 2 := by omega
  exact hsplit.imp (fun he1 => ⟨he1, by simpa [he1] using hl⟩) id

/-- Every allowed prime-field quotient forces innerness upstairs for the
original marked automorphism, with center equal to the two-core. -/
theorem MarkedInvolution.linear_two_prime_inner_and_center
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 p) :
    α ∈ (MulAut.conj (G := L)).range ∧ center L = pCore 2 L := by
  have hl := linear_two_field_large ho h
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let f := e.trans (Atlas.fieldEquivPSL 2 k)
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs f
  obtain ⟨g, _, hg⟩ := Theory.PSL2.primeField_sylow_fixed_inner ho hl Q
    (MulAut.centralQuotientAction f α) hQ
  exact d.inner_and_center_of_quotient_inner f ⟨g, hg.symm⟩

private theorem inner_of_fixer_card_two {G : Type*} [Group G] [Finite G]
    (hz : center G = ⊥) (hcard : 2 ∣ Nat.card G) (P : Sylow 2 G)
    (hbound : ∀ A : Subgroup (MulAut G),
      (∀ a ∈ A, ∀ x ∈ P, a x = x) → Nat.card A ≤ 2)
    (a : MulAut G) (ha : ∀ x ∈ P, a x = x) :
    a ∈ (MulAut.conj (G := G)).range := by
  classical
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).mpr (P.ne_bot_of_dvd_card hcard)
  let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : center P)
  have hzn : (z.val.val : G) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  let A := fixingSubgroup (MulAut G) (P : Set G)
  let B := A ⊓ (MulAut.conj (G := G)).range
  have hmem : MulAut.conj (z.val.val : G) ∈ B := by
    refine ⟨?_, ⟨z.val.val, rfl⟩⟩
    change MulAut.conj (z.val.val : G) ∈ fixingSubgroup (MulAut G) (P : Set G)
    rw [mem_fixingSubgroup_iff]
    intro x hx
    change z.val.val * x * z.val.val⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (congrArg Subtype.val (mem_center_iff.mp z.property ⟨x, hx⟩)).symm
  have hbn : (⟨MulAut.conj z.val.val, hmem⟩ : B) ≠ 1 := by
    intro h
    exact hzn ((MulAut.conj_injective_of_center_eq_bot hz)
      ((congrArg Subtype.val h).trans (map_one MulAut.conj).symm))
  let : Nontrivial B := ⟨⟨_, _, hbn⟩⟩
  have hb : 2 ≤ Nat.card B := Finite.one_lt_card
  have hA : Nat.card A ≤ 2 := hbound A (fun _ hm => (mem_fixingSubgroup_iff _).mp hm)
  have hBA : B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (hA.trans hb)
  have hm : a ∈ A := (mem_fixingSubgroup_iff _).mpr ha
  rw [← hBA] at hm
  exact hm.2

/-- The surviving PSL₃(3) quotient forces the original marked automorphism
to be inner. This does not assume a trivial Schur multiplier. -/
theorem MarkedInvolution.linear_three_three_inner_and_center
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 3) :
    α ∈ (MulAut.conj (G := L)).range ∧ center L = pCore 2 L := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let f := e.trans (Atlas.fieldEquivPSL 3 k)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Matrix.PSL3Three.PSL := f.symm.isSimpleGroup
  let : Group.IsPerfect Matrix.PSL3Three.PSL := Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨_, _, Q, hQ⟩ := d.centralQuotient_model_inputs f
  apply d.inner_and_center_of_quotient_inner f
  exact inner_of_fixer_card_two Subgroup.center_eq_bot_of_simple_perfect
    (by rw [Matrix.PSL3Three.card_PSL]; decide) Q
    (Matrix.PSL3Three.SylowFixers.sylow_fixer_card_le_two Q)
    (MulAut.centralQuotientAction f α) hQ

open Chapter15.Section03.Candidates.ComponentStructure

/-- Row (e) for the prime-field branch, once its arithmetic and cover
exclusions have been discharged. No action premise remains. -/
theorem MarkedInvolution.linear_two_prime_of_center_eq_bot
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (ho : Odd p)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 p) (hz : center L = ⊥) :
    ModelAction115 L α := by
  have hi := (d.linear_two_prime_inner_and_center hp.1 ho h).1
  let f : L ≃* L ⧸ center L := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact .odd (Or.inr ⟨p, hp, h.of_mulEquiv f⟩) hi

/-- Row (e) for PSL₃(3), retaining only the independent cover exclusion. -/
theorem MarkedInvolution.linear_three_three_of_center_eq_bot
    {α : MulAut L} {P : Sylow 2 L} (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 3) (hz : center L = ⊥) :
    ModelAction115 L α := by
  have hi := (d.linear_three_three_inner_and_center h).1
  let f : L ≃* L ⧸ center L := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact .odd (Or.inl (h.of_mulEquiv f)) hi

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
