module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoCore
public import Theory.SpecificGroups.SU3.BinaryCubicRankParity
public import Theory.SpecificGroups.SL2.BinaryOddRank

/-!
# Excluding binary rank-one models in the original rank-two branch

Binary PSL₂ has cyclic cubic Sylows. For PSU₃ the original inverted-order
bound forces field degree two or four, while cubic rank two forces odd
degree. The preceding Suzuki exclusion completes all Bender-model rows.
These are actual model isomorphisms of the selected component, and all
point, action and earlier-geometry hypotheses are preserved.

The rank-one source branch is not excluded by this argument. Source:
Aschbacher–Smith, proof of 12.6.26, printed p.832, Theorem C inspection.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- In rank two, the binary unitary row contradicts the forced even field degree. -/
theorem SourceHypothesis.original_rank_two_not_binaryUnitary
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) {n : ℕ} (hn2 : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSU (Nonabelian.Setup.star H c.K) 3 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hcenter : center B = ⊥ := center_eq_bot_of_simple_perfect
  let e₀ : (B ⧸ center B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have heven : Even n := by
    rcases S.original_selectedComponent_binaryUnitary_quotient_degree D hZ z hz hTV hTz
      hbound hns hH hn c a hn2 ⟨F,hFfield,hFfinite,J,hF,hconj,⟨e₀.trans e⟩⟩ with he|he
    · rw [he]; decide
    · rw [he]; decide
  have hlow := BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity.rank_le_one_of_even
    J (by omega : 0 < n) hF hconj heven
  have hrB : primeRank 3 B = 2 := c.three_rank_eq_star.symm.trans hr
  rw [primeRank_equiv 3 e] at hrB
  omega

include c in
/-- Binary linear-two components have cyclic cubic Sylows and cannot have rank two. -/
theorem SourceHypothesis.original_rank_two_not_binaryLinearTwo
    (hr : primeRank 3 c.K = 2) {n : ℕ} (_hn2 : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 (2^n) := by
  classical
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F) := default
  have hcyc : IsCyclic P := Matrix.SL2.odd_pGroup_isCyclic_of_injective
    P.isPGroup' (by decide : 3 ≠ 2) (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype
    Subtype.val_injective
  have hlow := P.primeRank_quotient_le_one hcyc
    (center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hrB : primeRank 3 (Nonabelian.Setup.star H c.K) = 2 :=
    c.three_rank_eq_star.symm.trans hr
  rw [primeRank_equiv 3 e] at hrB
  change primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≤ 1 at hlow
  omega

include hz hTV hTz hbound hH hn a in
/-- Every Bender-model row in Theorem C is excluded on the original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_bender
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ ClassificationModels.IsBenderModel (Nonabelian.Setup.star H c.K) := by
  intro hm
  cases hm with
  | linear n hn2 he => exact S.original_rank_two_not_binaryLinearTwo D hZ z c hr hn2 he
  | unitary n hn2 he =>
      exact S.original_rank_two_not_binaryUnitary D hZ z hz hTV hTz hbound
        hH hn c a hTI hns hr hn2 he
  | suzuki m hm he =>
      exact S.original_selectedComponent_star_not_suzuki D hZ z hz hTV hTz
        hbound hns hH hn c m (by omega) he
end CFSG.Quasithin.Chapter12.Section06
