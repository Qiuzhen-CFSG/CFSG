module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.OddLinear
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Mathieu
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.JankoFourRudvalis
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction

/-!
# Odd-characteristic and sporadic rows for two-centrality symmetry

This module assembles residual separation for the complete (E2)(ii)–(iii)
alternative: PSL₃(3), every Fermat–Mersenne PSL₂ parameter, and all nine
sporadic names. Inner and outer noncentral actors are both retained.
The two source quotient conventions are connected by the canonical
L/Z(L) ≃ L/O₂(L), using quasisimplicity and the trivial odd core.

The earlier inputs are the concrete universal fixed-group tables and the
complete covering alternative of 16.1.2(2). They contain extensions,
isomorphisms and Sylow markings, never residual separation. The existing
proved M₁₁ and M₂₃ tables require no extra input. The large-center
exceptions are eliminated only for J₂ and HS, where the order comparison
needs the bound; the possible order-four center over M₂₂ is retained.

The family proofs derive incompatible residual orders, prime divisors or
involution structure. The odd-linear proofs exclude the exceptional O³
modification by actual model orders; the sporadic proofs accommodate it
directly. In particular no quotient fixed group is identified with the
image of the full fixed group upstairs.

`separation` and `twoCentral_iff_of_residualEquiv` are conditional
comparisons. The source 16.5.6 assembly must supply `EarlierTables` and
the earlier covering alternative; this module does not assert those
intrinsic catalogues or the final four-clause source theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2 and 16.1.5 on printed pp.1170–1172, I.2.2 on pp.409–412,
and Notation 16.5.5 and Lemma 16.5.6(4) on p.1197. Source exclusions
must remain at their proper levels: Bender and PSL₃(4) at L/Z(L),
and A₆ at the full component L. The A₆ exclusion is unnecessary for this
branch and is not used.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows

open Subgroup Theory.GroupTheory ClassificationModels
open OtherPreliminaries
open SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open OuterReduction.CoverFusion

/-- The concrete earlier tables consumed by the odd-linear and nine-sporadic
comparison. The J₄ and Ru fields retain their actual Sylow markings; the
other markings and every residual invariant are proved in the family modules.
The PSL₂ input includes parameters five and seven. -/
structure EarlierTables where
  pslTwo : OddTwoTables
  pslThree : ∀ a : MulAut Matrix.PSL3Three.PSL, orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) → Nonempty (a.fixedSubgroup ≃* Equiv.Perm (Fin 4))
  m12 : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
    OtherPreliminaries.Mathieu.M12InvolutionAlternative a
  m22 : ∀ a : MulAut Sporadic.Mathieu.M22, orderOf a = 2 →
    OtherPreliminaries.Mathieu.M22InvolutionAlternative a
  m24 : ∀ a : MulAut Sporadic.Mathieu.M24, orderOf a = 2 →
    OtherPreliminaries.Mathieu.M24InvolutionAlternative a
  j2 : ∀ a : MulAut Sporadic.LeechRelated.J2.Carrier, orderOf a = 2 →
    OtherPreliminaries.JankoTwoHigmanSims.J2InvolutionAlternative a
  hs : ∀ a : MulAut Sporadic.LeechRelated.HS.Carrier, orderOf a = 2 →
    OtherPreliminaries.JankoTwoHigmanSims.HSInvolutionAlternative a
  j4 : JankoFourRudvalis.JankoTable
  ru : JankoFourRudvalis.RudvalisTable

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} [IsQuasisimple L]

omit [Finite G] [IsQuasisimple L] in
private theorem small_center_of_source
    (hcent : SourceCenterAlternative L)
    (hB : ¬ IsBenderModel (L ⧸ center L))
    (h34 : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hcard : Nat.card (L ⧸ center L) ≠ 443520) : Nat.card (center L) ≤ 2 := by
  rcases hcent with hb | ⟨hs | hl, _⟩ | ⟨⟨e⟩, _⟩
  · exact hb
  · exact (hB (.suzuki 1 (by decide) hs)).elim
  · exact (h34 hl).elim
  · exact (hcard ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order)).elim

/-- The full nine-name sporadic comparison. Source 16.1.2(2) is used only
to bound the centers over J₂ and HS; no center is discarded in the other
seven branches. The two exclusions are on the central quotient, exactly as
in the source. Both noncentral inner and noncentral outer rows are covered. -/
theorem sporadic_separation (tables : EarlierTables)
    (hodd : pPrimeCore 2 L = ⊥) (hcent : SourceCenterAlternative L)
    (hB : ¬ IsBenderModel (L ⧸ center L))
    (h34 : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hfamily : IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L))
    (u v : normalizer (L : Set G)) (hu2 : orderOf u.val = 2) (hv2 : orderOf v.val = 2)
    (huπ : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hvπ : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := hfamily
  let eZ := (LiePreliminaries.centerQuotientEquivTwoCore hodd).trans e
  cases name with
  | m11 => exact Mathieu.m11_no_equiv eZ u v hvπ hv
  | m12 => exact Mathieu.m12_no_equiv hodd eZ tables.m12 u v huπ hvπ hu hv
  | m22 => exact Mathieu.m22_no_equiv hodd eZ tables.m22 u v huπ hvπ hu hv
  | m23 => exact Mathieu.m23_no_equiv eZ u v hvπ hv
  | m24 => exact Mathieu.m24_no_equiv hodd eZ tables.m24 u v huπ hvπ hu hv
  | j2 =>
    have hZ := small_center_of_source hcent hB h34 (by
      rw [Nat.card_congr eZ.toEquiv]
      change Nat.card Sporadic.LeechRelated.J2.Carrier ≠ 443520
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      decide)
    exact JankoTwoHigmanSims.j2_no_equiv tables.j2 hodd eZ hZ u v hu hvπ hv
  | j3 => exact (hj3 rfl).elim
  | j4 => exact JankoFourRudvalis.janko_no_equiv tables.j4 hodd eZ u v hu2 hv2 huπ hvπ hu hv
  | hs =>
    have hZ := small_center_of_source hcent hB h34 (by
      rw [Nat.card_congr eZ.toEquiv]
      change Nat.card Sporadic.LeechRelated.HS.Carrier ≠ 443520
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      decide)
    exact JankoTwoHigmanSims.hs_no_equiv tables.hs hodd eZ hZ u v hu hvπ hv
  | he => exact (hhe rfl).elim
  | ru => exact JankoFourRudvalis.rudvalis_no_equiv tables.ru hodd eZ u v hu2 hv2 huπ hvπ hu hv

/-- Separation of the full modified residuals for exactly (E2)(ii)–(iii),
conditional only on the displayed earlier fixed-group and covering tables.
The odd-characteristic alternatives concern L itself, while the sporadic
alternative concerns L/O₂(L). No additional ambient geometry is required. -/
theorem separation (tables : EarlierTables)
    (hodd : pPrimeCore 2 L = ⊥) (hcent : SourceCenterAlternative L)
    (hB : ¬ IsBenderModel (L ⧸ center L))
    (h34 : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hfamily : IsOtherEvenTypeComponent L)
    (u v : normalizer (L : Set G)) (hu2 : orderOf u.val = 2) (hv2 : orderOf v.val = 2)
    (huπ : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hvπ : orderOf (actionMap (L := L) le_rfl v) = 2)
    (hu : IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u))
    (hv : ¬ IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v)) :
    ¬ Nonempty (modifiedCentralizerResidual L u.val ≃*
      modifiedCentralizerResidual L v.val) := by
  rcases hfamily with hthree | htwo | hsporadic
  · exact OddLinear.separation tables.pslTwo tables.pslThree (Or.inl hthree) u v hvπ hu hv
  · exact OddLinear.separation tables.pslTwo tables.pslThree (Or.inr htwo) u v hvπ hu hv
  · exact sporadic_separation tables hodd hcent hB h34 hsporadic u v hu2 hv2 huπ hvπ hu hv

/-- The forward comparison used after transporting a common residual into
one component. Symmetry gives the reverse implication with no new table input. -/
theorem twoCentral_iff_of_residualEquiv (tables : EarlierTables)
    (hodd : pPrimeCore 2 L = ⊥) (hcent : SourceCenterAlternative L)
    (hB : ¬ IsBenderModel (L ⧸ center L))
    (h34 : ¬ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (hfamily : IsOtherEvenTypeComponent L)
    (u v : normalizer (L : Set G)) (hu2 : orderOf u.val = 2) (hv2 : orderOf v.val = 2)
    (huπ : orderOf (actionMap (L := L) le_rfl u) = 2)
    (hvπ : orderOf (actionMap (L := L) le_rfl v) = 2)
    (e : modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl v) := by
  constructor
  · intro hu
    by_contra hv
    exact separation tables hodd hcent hB h34 hfamily u v hu2 hv2 huπ hvπ hu hv ⟨e⟩
  · intro hv
    by_contra hu
    exact separation tables hodd hcent hB h34 hfamily v u hv2 hu2 hvπ huπ hv hu ⟨e.symm⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows
