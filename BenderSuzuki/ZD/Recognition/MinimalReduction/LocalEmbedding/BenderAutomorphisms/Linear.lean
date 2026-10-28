module

public import BenderSuzuki.SE.Models
public import Theory.GroupAction.AutomorphismFixedTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.OuterFixed

/-!
# Binary PSL₂ fixed-group obstructions: assembly

For any automorphism squaring to one, parity and the Weyl involution give an
involution in the actual fixed subgroup. Inner automorphisms have fixed
subgroups containing a four-group when the binary field degree is at least two.
An outer fixed subgroup isomorphic to PSL₂ over the square-root field has a
four-group unless that field is GF(2), and never has a normal Sylow 2-subgroup,
including in this small exception.

Arbitrary-automorphism semilinear coverage and outer involution descent identify
the entire outer fixed subgroup with its square-root-field model. This
discharges the classification premise in the two conditional assembly helpers
and proves both obstructions without additional automorphism hypotheses.
The source inputs are GLS, Volume 4, Chapter 4, Lemma 3.4(b,c).

The application in Chapter 2, Proposition 4.4 uses C_K(u). We derive its rank
consequence from actual fixed-group isomorphisms, without relying on the
transcribed C_H(u) in Chapter 4, Lemma 3.4(e). Normality here is inside the fixed
group; no quotient or residual is substituted for that group.
-/

namespace BenderSuzuki.ZD.Linear
open _root_.BenderSuzuki.MatrixGroups PFAppendixIII PFchapter1section1

/-- The Weyl involution witnesses even order without a group-order formula. -/
public theorem psl2_even_card (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Even (Nat.card (PSL2MatrixGroup K)) := by
  have hw := Converse.PWeyl_isInvolution (F := K)
  have ho : orderOf (Converse.PWeyl K) = 2 := orderOf_eq_prime_iff.mpr ⟨hw.2, hw.1⟩
  apply even_iff_two_dvd.mpr
  simpa only [ho] using orderOf_dvd_natCard (Converse.PWeyl K)

/-- Every automorphism squaring to one fixes an involution, including the identity. -/
public theorem fixed_contains_involution {n : ℕ} (a : MulAut (PSL2BinaryMatrixGroup n))
    (ha : a ^ 2 = 1) :
    ∃ x : PSL2BinaryMatrixGroup n, x ∈ a.fixedSubgroup ∧ IsInvolution x := by
  obtain ⟨x, hx, ho⟩ := MulAut.exists_fixed_orderOf_eq_two a ha
    (psl2_even_card (BinaryGaloisField n))
  obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp ho
  exact ⟨x, (MulAut.mem_fixedSubgroup a x).mpr hx, hne, hsq⟩

/-- An actual square-root-field fixed model yields precisely the exceptional degree. -/
public theorem exponent_eq_two_of_fixed_model {n m : ℕ} (hm : 0 < m) (hnm : n = 2 * m)
    (a : MulAut (PSL2BinaryMatrixGroup n))
    (e : a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m)
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) : n = 2 := by
  have hm2 : ¬ 2 ≤ m := by
    intro h
    exact hrank ((binary_twoRank h).map_of_injective e.symm.toMonoidHom e.symm.injective)
  have hm1 : m = 1 := by omega
  omega

/-- Fixed groups isomorphic to binary PSL₂, including PSL₂(2), are not 2-closed. -/
public theorem fixed_no_normal_sylow_of_model {n m : ℕ}
    (a : MulAut (PSL2BinaryMatrixGroup n))
    (e : a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) :
    ¬ ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal := by
  intro h
  exact psl2_no_normal_sylow ((e.exists_normal_sylow_iff 2).mp h)

/-- Conditional assembly: the outer fixed-group classification remains an explicit premise. -/
public theorem rank_one_obstruction_of_outer_fixed_models {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (houter : (¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) →
      ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m))
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    n = 2 ∧ (¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) ∧
      ∃ x : PSL2BinaryMatrixGroup n, x ∈ a.fixedSubgroup ∧ IsInvolution x := by
  have hi := fixed_no_four_implies_outer hn a ha hrank
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := houter hi
  exact ⟨exponent_eq_two_of_fixed_model hm hnm a e hrank, hi,
    fixed_contains_involution a ha⟩

/-- Conditional assembly of the 2-closed obstruction from actual outer fixed models. -/
public theorem inner_of_normal_sylow_of_outer_fixed_models {n : ℕ}
    (a : MulAut (PSL2BinaryMatrixGroup n))
    (houter : (¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) →
      ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m))
    (hP : ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) :
    ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b := by
  by_contra hi
  obtain ⟨m, _, _, ⟨e⟩⟩ := houter hi
  exact fixed_no_normal_sylow_of_model a e hP

/-- Every outer involution of binary PSL₂ has the actual square-root-field fixed group. -/
public theorem outer_fixed_model {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) := by
  obtain ⟨g, σ, heq⟩ := binary_semilinear_coverage hn a
  exact outer_fixed_model_of_semilinear hn a ha g σ heq houter

/-- An arbitrary outer involution of PSL₂(4) fixes a copy of PSL₂(2). -/
public theorem outer_fixed_model_two
    (a : MulAut (PSL2BinaryMatrixGroup 2)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b : PSL2BinaryMatrixGroup 2, a = MulAut.conj b) :
    Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup 1) := by
  obtain ⟨m, _, hnm, e⟩ := outer_fixed_model (by decide) a ha houter
  have hm : m = 1 := by omega
  subst m
  exact e

/-- If the fixed subgroup has no four-group, the degree is two, the automorphism
is outer, and the fixed subgroup contains an involution. -/
public theorem rank_one_obstruction {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    n = 2 ∧ (¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b) ∧
      ∃ x : PSL2BinaryMatrixGroup n, x ∈ a.fixedSubgroup ∧ IsInvolution x :=
  rank_one_obstruction_of_outer_fixed_models hn a ha (outer_fixed_model hn a ha) hrank

/-- An involutory automorphism with a normal Sylow 2-subgroup in its fixed group
is inner. Normality is relative to the entire fixed group. -/
public theorem inner_of_normal_sylow {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (hP : ∃ P : Sylow 2 a.fixedSubgroup, (P : Subgroup a.fixedSubgroup).Normal) :
    ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b :=
  inner_of_normal_sylow_of_outer_fixed_models a (outer_fixed_model hn a ha) hP

end BenderSuzuki.ZD.Linear
