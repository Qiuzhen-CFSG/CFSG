module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Source
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.Source
public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.CubicClifford.Dimension
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
import Mathlib.Tactic

/-!
# The solvable cubic branch in binary degree four

A nontrivial five-core has odd centralizer on the actual four-space, so it
cannot be centralized by the positive-rank elementary actor. A normal
seven-core is excluded by the binary degree divisibility. The Fitting
subgroup is therefore the three-core. If the latter had order three,
solvable Fitting self-centralization would make its quotient a two-group,
and cubic Clifford theory would force binary degree two.

Consequently the three-core has order nine. The existing nine-normalizer
recognition supplies the literal orthogonal action, retaining the source
rank-one and rank-two alternatives. This specializes G.9.4(3--4) to the
solvable actor used in 14.3.15, without a semilinear overgroup premise.
Source: Aschbacher--Smith G.9.4, pp.354--355, and 14.3.15, pp.994--995.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

private theorem normalCore_invariants_eq_bot (h : FittingHypothesis K ρ A m)
    (p : ℕ) (hne : pCore p G ≠ ⊥) :
    Representation.invariants (ρ.comp (pCore p G).subtype) = ⊥ := by
  let : Representation.IsIrreducible ρ := h.irreducible
  by_contra hfix
  have hle := Representation.le_ker_of_normal_invariants_ne_bot ρ (pCore p G) hfix
  rw [ρ.ker_eq_bot h.faithful] at hle
  exact hne (bot_unique hle)

/-- In the cubic branch a nontrivial five-core would have odd centralizer,
contradicting the positive-rank elementary actor which centralizes it. -/
theorem Four.fiveCore_eq_bot_of_cubic_degree_four
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 4) : pCore 5 G = ⊥ := by
  classical
  by_contra hne
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ h.faithful
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  have hdiv := card_centralizer_five_dvd_fifteen (V := Multiplicative V) (pCore 5 G)
    (FiveCore.fiveCore_card h.faithful hd hne) hV
  have hA : A ≤ centralizer (pCore 5 G : Set G) :=
    Four.centralizes_primeCore_of_cubic_commutator hc 5 (by decide)
  have htwo : 2 ∣ Nat.card A := by rw [h.card_actor]; exact dvd_pow_self 2 (by omega)
  have hh := htwo.trans ((card_dvd_of_le hA).trans hdiv)
  norm_num at hh

/-- An irreducible binary four-space has no nontrivial normal seven-core. -/
theorem Four.sevenCore_eq_bot_of_degree_four
    (h : FittingHypothesis K ρ A m) (hd : Module.finrank (ZMod 2) V = 4) :
    pCore 7 G = ⊥ := by
  by_contra hne
  have hh := Representation.BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
    (ρ.comp (pCore 7 G).subtype) (by decide : Nat.Prime 7) (by decide)
    (show IsPGroup 7 (pCore 7 G) from pCore_isPGroup) (normalCore_invariants_eq_bot h 7 hne)
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_seven, hd] at hh
  norm_num at hh

/-- Only the actual three-core remains in the Fitting subgroup. -/
theorem Four.fitting_eq_threeCore_of_cubic_degree_four
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 4) : fittingSubgroup G = pCore 3 G := by
  let : Representation.IsIrreducible ρ := h.irreducible
  have hG : Nat.card G ∣ 20160 := by
    have hh := Representation.card_dvd_card_GL_of_injective ρ h.faithful
    rw [hd, Matrix.card_GL_field] at hh
    norm_num [Fin.prod_univ_succ] at hh
    exact hh
  apply le_antisymm _ (pCore_le_fitting G 3)
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  have hp := Nat.prime_of_mem_primeFactors p.val.property
  have hpd := (Nat.dvd_of_mem_primeFactors p.val.property).trans hG
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, hpd, (by decide : 20160 ≠ 0)⟩
  rw [show Nat.primeFactors 20160 = {2,3,5,7} by decide +kernel] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h2 | h3 | h5 | h7
  · rw [h2, h.toSetup.twoCore_eq_bot]; exact bot_le
  · rw [h3]
  · rw [h5, Four.fiveCore_eq_bot_of_cubic_degree_four h hm hc hd]; exact bot_le
  · rw [h7, Four.sevenCore_eq_bot_of_degree_four h hd]; exact bot_le

/-- For the solvable source actor, an order-three core would give an
irreducible binary plane, contradicting degree four. -/
theorem Four.threeCore_card_nine_of_solvable
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 4) (hs : Group.IsSolvable G) :
    Nat.card (pCore 3 G) = 9 := by
  let : Representation.IsIrreducible ρ := h.irreducible
  rcases Four.threeCore_card_cases h.toSetup hm (threeCoreData_from_source h hm hc) hd with h3 | h9
  · let B := pCore 3 G
    let : IsCyclic B := isCyclic_of_prime_card h3
    have hfit := Four.fitting_eq_threeCore_of_cubic_degree_four h hm hc hd
    have hcentral : centralizer (B : Set G) = B := by
      apply le_antisymm _ B.le_centralizer
      change centralizer (pCore 3 G : Set G) ≤ pCore 3 G
      rw [← hfit]
      exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
    let f : G →* MulAut B := MulAut.conjNormal
    have hk : f.ker = B := (MulAut.conjNormal_ker_eq_centralizer B).trans hcentral
    have haut : IsPGroup 2 (MulAut B) := IsPGroup.of_card (n := 1) (by
      rw [IsCyclic.card_mulAut, h3]; decide)
    have hQ : IsPGroup 2 (G ⧸ B) := by
      exact ((haut.to_subgroup f.range).of_equiv
        (QuotientGroup.quotientKerEquivRange f).symm).of_equiv
          (QuotientGroup.quotientMulEquivOfEq hk)
    have hne : ¬ B ≤ ρ.ker := by
      rw [ρ.ker_eq_bot h.faithful]
      intro hh
      have hz := card_eq_one.mpr (bot_unique hh)
      rw [h3] at hz
      omega
    have hdim := Representation.CubicClifford.finrank_eq_two ρ ⊥ B h3 bot_le
      (hQ.of_equiv (QuotientGroup.quotientMulEquivOfEq (bot_sup_eq B)).symm) hne
    omega
  · exact h9

/-- The actual solvable cubic degree-four branch has its marked orthogonal
action; the semilinear overgroup classification is unnecessary. -/
theorem source_solvable_cubic_degree_four
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V = 4) (hs : Group.IsSolvable G) :
    (m = 1 ∧ CaseThree ρ m) ∨ (m = 2 ∧ CaseFour ρ m) := by
  have data := threeCoreData_from_source h hm hc
  obtain ⟨d⟩ := Four.NineNormalizer.orthogonalNormalizerModel ρ h.faithful hd (pCore 3 G)
    (Four.threeCore_card_nine_of_solvable h hm hc hd hs)
  have hm12 : m = 1 ∨ m = 2 := by have := data.actor_rank_le; omega
  rcases hm12 with rfl | rfl
  · exact Or.inl ⟨rfl, Four.caseThree_of_orthogonalNormalizer h.toSetup hd d⟩
  · exact Or.inr ⟨rfl, Four.caseFour_of_orthogonalNormalizer h.toSetup data hd d⟩

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
