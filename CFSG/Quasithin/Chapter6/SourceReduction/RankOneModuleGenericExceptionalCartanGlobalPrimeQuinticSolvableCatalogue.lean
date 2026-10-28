module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.TwistedRows
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ExceptionalRows
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Applications
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableLocal

/-!
# Full reduced-catalogue filtering for the original quintic pair

All seven regular families, eight exceptional rows, three binary quotient
conventions and both orientations are handled. Solvability and index five
at the first endpoint exclude the ordinary rows except binary Ree, where
the opposite endpoint is solvable. The exceptional rows use only their
weaker parabolic equivalences; the binary clauses use their literal quotient
maps. The original-to-reduced transports restore the full original Borel.

Applied to the selected Chapter 6 pair, opposite solvability contradicts
its proved nonsolvable right endpoint, yielding p ≠ 5 and hence p = 3.
Both D₁₀ and Sz(2) remain in the input; no ambient Sylow assumption is added.
The adapter lives here because the existing full ReducedAlternatives
predicate is defined at the Chapter 6 catalogue boundary. The model filters
are separate Chapter F extensions.

This is the complete conditional implication from that catalogue. Genuine
source selection remains with qt-dgs85-source-assembly, and its discharge
in the original quintic theorem remains required.
Source: Aschbacher–Smith F.1.12 and 5.2.2, pp.262–264 and 647–648;
DGS Theorem A and (15.1)–(15.3), pp.99–100 and 226–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalExtension
open ChapterF.Source ChapterF.Source.QuinticSolvableParabolics
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.DGS85.Assembly.BinaryQuotients
variable {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}

/-- The entire reduced catalogue implies opposite solvability at the original
quintic pair, retaining both small left quotients and the full overlap. -/
theorem quintic_opposite_solvable_of_reduced_alternatives
    (h : HypothesisF11 ![K,R] S) (hqt : IsQuasithin (ChapterF.Source.generated ![K,R] S))
    (hSK : S ≤ K) (hi : S.relIndex K = 5) (ha : ReducedAlternatives K R S) :
    Group.IsSolvable (parabolic ![K,R] S 1) := by
  cases ha with
  | linear F m hm hF b e => exact (not_linear h hSK hi F b e.some).elim
  | symplectic F m hm hF b e => exact (not_symplectic h hSK hi F b e.some).elim
  | g2 F b e => exact (not_g2 h hSK hi F b e.some).elim
  | triality m hm b e => exact (not_triality h hSK hi m hm b e.some).elim
  | ree m b e =>
    have hm := ree_parameter_zero h hSK hi m b e.some
    subst m
    let := ReeComparison.binary_parabolic_solvable (ReeNative.side (!b))
    have hs : Group.IsSolvable
        (parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 1) :=
      Group.isSolvable_of_isSolvable_injective (f := e.some.right.toMonoidHom) e.some.right.injective
    exact (original_opposite_solvable_of_reduced h 0 hs).1
  | unitaryFour m hm b e => exact (not_unitaryFour h hSK hi m hm b e.some).elim
  | unitaryFive q hq heven M b e => exact (not_unitaryFive h hqt hSK hi hq heven M b e.some).elim
  | exceptional c he =>
    rcases he with he | he
    · exact (original_opposite_solvable_of_reduced h 0
        (ExceptionalComparison.right_solvable c _ he)).1
    · exact (not_reversed_exceptional h hSK hi c he).elim
  | binaryLocal i he =>
    exact (quintic_parabolics_solvable_of_binary_rows h hSK hi (Or.inl ⟨i,he⟩)).2.1
  | binaryJoin i he =>
    exact (quintic_parabolics_solvable_of_binary_rows h hSK hi (Or.inr (Or.inl ⟨i,he⟩))).2.1
  | binaryParabolic i he =>
    exact (quintic_parabolics_solvable_of_binary_rows h hSK hi (Or.inr (Or.inr ⟨i,he⟩))).2.1
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalExtension

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- At the literal selected Cartan pair, the full reduced catalogue rules out
p = 5 by contradicting its proved nonsolvable right endpoint. -/
theorem LocalData.prime_ne_five_of_reduced_alternatives
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (ha : Global.OriginalExtension.ReducedAlternatives
      (D ⊔ Global.sourceS L H) R (Global.sourceS L H)) : p ≠ 5 := by
  intro hp
  subst p
  have hf := d.hypothesisF11 h hH c hd hz
  exact d.right_parabolic_not_solvable hz
    (Global.OriginalExtension.quintic_opposite_solvable_of_reduced_alternatives
      hf (h.qtke.quasithin.subgroup _) le_sup_right (Input.prime_left_index h hH c hd) ha)

/-- The same actor is cubic after the quintic catalogue exclusion. -/
theorem LocalData.prime_eq_three_of_reduced_alternatives
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (ha : Global.OriginalExtension.ReducedAlternatives
      (D ⊔ Global.sourceS L H) R (Global.sourceS L H)) : p = 3 :=
  hd.prime.resolve_right (d.prime_ne_five_of_reduced_alternatives h hH c hd hz ha)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
