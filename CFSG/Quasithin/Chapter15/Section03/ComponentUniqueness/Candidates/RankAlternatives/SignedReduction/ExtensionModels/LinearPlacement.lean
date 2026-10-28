module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Linear.Borel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicBorelFixer
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Local placement in the split linear extension

The invariant Borel over S ∩ L lies in the actual intersection M ∩ I by
15.3.33(1). Every cubic element of its PSL₃ image lifts through O₂(L) to a
cubic element of this Borel, hence to Y₊ by 15.3.11(6). An element of S
centralizing Y₊ therefore fixes all cubic elements of the projective Borel.
The intrinsic cubic-Borel rigidity calculation makes its quotient action
trivial. Perfection of L and centrality of O₂(L) then make its action on L
trivial as well; the central two-cover kernel is retained throughout.

In the rank-one branch the first plane V₁ lies in C_S(Y₊), whereas
N_G(V₁) ≤ M by 15.3.11(3). Thus L centralizes V₁ and lies in M, contrary
to the chosen outside component. This excludes the even-degree linear
quotient itself and, in particular, proves the requested placement implication
with the exact PGL extension and signed component witnesses still explicit.
No diagonal actor, minimal outside overgroup, or later 15.3.38/40/43
conclusion is an input.

`LocalSetup` retains the earlier Sylow, component, theta and invariant
characteristic-two containment facts. Only the first-plane containment,
centralization and normalizer fields of `PlaneData` are used: these come
from the natural plane setup and the second choice in 15.3.10, selected
by 15.3.11(5ii). They are genuine earlier source inputs, not the desired
placement. The other numerical and split-model premises in the final
theorem are unnecessary for the stronger centralizer contradiction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2),
printed pp.51--52; 15.3.2--12, pp.1121--1125; 15.3.25 and 15.3.33,
p.1134; and the reductions on pp.1135 and 1139.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.LinearPlacement
open RankOne.DiagonalExclusion Candidates.LinearCore Candidates.LinearCore.MatrixImage

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G}

/-- Cubic Borel rigidity detects centralization of the actual component,
including through its entire central two-core. -/
theorem centralizer_le_of_linear_quotient (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (heven : Even n) (hcard : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    S ⊓ centralizer (Yplus : Set G) ≤ centralizer (L : Set G) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  have hcore : pCore 2 L ≤ center L :=
    (local_center_eq_twoCore h.component_le h.component h.odd_core).ge
  have hSN : S ≤ normalizer (L : Set G) :=
    le_sup_right.trans (h.join_normalizes horbit)
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨P, hP⟩ := quotient_sylow h.component_le h.component.1 Q hQ e
  obtain ⟨_, _, hBM⟩ := h.linear_borel horbit hn heven hcard e
  intro v hv
  have hfix : quotientAction hSN e ⟨v, hv.1⟩ = 1 := by
    apply Matrix.PSL3.LinearThree.CubicBorel.eq_one_of_fixes_sylowNormalizer_cubics
      hn heven hcard P
    intro z hz hz3
    obtain ⟨l, hl, hl3⟩ := order_three_lift e z hz3
    have hlB : (l : G) ∈ L ⊓ normalizer (S ⊓ L : Subgroup G) := by
      rw [← h.linear_borel_preimage e P hP]
      exact mem_map_of_mem L.subtype (show quotientMap e l ∈ normalizer
        (P : Set PSL(3,F)) from hl ▸ hz)
    have hlY : (l : G) ∈ Yplus := h.theta_eq ▸ subset_closure
      ⟨hBM hlB, (Subgroup.orderOf_coe l).trans hl3⟩
    have hvl : L.normalizerMonoidHom ⟨v, hSN hv.1⟩ l = l := by
      apply Subtype.ext
      change v * (l : G) * v⁻¹ = l
      rw [← mem_centralizer_iff.mp hv.2 l hlY, mul_inv_cancel_right]
    rw [← hl]
    change quotientAction hSN e ⟨v, hv.1⟩ (e (QuotientGroup.mk' (pCore 2 L) l)) = _
    rw [quotientAction_apply, hvl]
    rfl
  have hm : (⟨v, hv.1⟩ : S) ∈ (quotientAction hSN e).ker := hfix
  rw [quotientAction_ker hSN e hcore] at hm
  exact hm

/-- The first-plane facts of 15.3.11 exclude an even-degree PSL₃ quotient
for the outside component in the rank-one local setup. -/
theorem false_of_linear_quotient (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) {V₁ : Subgroup G}
    (hVS : V₁ ≤ S) (hVY : ⁅V₁, Yplus⁆ = ⊥)
    (hNV : normalizer (V₁ : Set G) ≤ M)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (heven : Even n) (hcard : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) : False := by
  have hVC : V₁ ≤ centralizer (L : Set G) :=
    (le_inf hVS (commutator_eq_bot_iff_le_centralizer.mp hVY)).trans
      (centralizer_le_of_linear_quotient h horbit hn heven hcard e)
  exact h.component_outside ((le_centralizer_iff.mp hVC).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNV))

/-- The requested placement implication with the literal split extension,
actual component quotient and permitted signed component restriction.
The proof establishes the stronger local contradiction above, so it does
not need to extract or assume an extension actor. -/
theorem yplus_not_le_of_pgl (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (p : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S)
    (_hrankL : primeRank 3 L = 2) (_hrankY : primeRank 3 d.Yplus = 1)
    {F : Type*} [Field F] [Finite F] {q n : ℕ}
    (hq : q = 2 ^ n) (hn : 0 < n) (hmod : q % 3 = 1)
    (hcard : Nat.card F = q)
    (_extension : Residual I ≃* PGL(Fin 3,F))
    (model : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (_signed : ClassicalGroup.IsPSL L 3 q ∨ q = 4)
    (_htheta : ¬ theta I ≤ L) : ¬ d.Yplus ≤ L := by
  have heven : Even n := by
    rw [Nat.even_iff]
    have hp := Nat.BinaryTorusParity.two_pow_mod_three n
    rw [hq] at hmod
    split_ifs at hp <;> omega
  exact (false_of_linear_quotient h horbit p.first_le p.first_centralizes
    p.first_normalizer hn heven (hcard.trans hq) model).elim

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.LinearPlacement
