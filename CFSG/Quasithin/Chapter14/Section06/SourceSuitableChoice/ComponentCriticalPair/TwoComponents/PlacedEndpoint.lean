module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.CriticalActions
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Hyperplanes
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Selection

/-!
# Interface between the two terminal component arguments

The first part of original 14.6.24(3) selects a critical endpoint, makes its
actor normalize the two components, and places its central point in one
component support. The actor then has rank at most two. The second part
uses this same endpoint for component alignment and the Sylow-index
contradiction. This record is the output contract for the first part;
it asserts neither existence nor exclusion of a component pair.

The denominator is the literal intersection with the opposite two-core.
`source_critical_denominators` identifies it with the commutator preimage,
so there is no independent choice of a denominator or a quotient action.
Source: Aschbacher--Smith 14.6.24(3), printed pp.1039--1041.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
variable {G : Type*} [Group G] [Finite G]

/-- Uniform point placement for rank-compared critical endpoints. The
endgame needs this for the reversed endpoint in the equal-rank branch,
as well as for the initial choice. This is an output contract, not an
assertion that an arbitrary F.9 setup has only two component supports. -/
def PairPointPlacement {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) (K Kplus : Subgroup G) : Prop :=
  ∀ i : h.CriticalEndpoint,
    0 < Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) →
    Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) ≤
      rank (((i.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) →
    i.conjugate D.V₁ ≤ ⁅D.UH,K⁆ ∨ i.conjugate D.V₁ ≤ ⁅D.UH,Kplus⁆

/-- The placed critical endpoint needed by the component-containment and
Sylow-index argument. Its construction, including every rank inequality,
remains the responsibility of the quadratic-placement theorem. -/
structure PlacedEndpoint {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) (K Kplus : Subgroup G) where
  endpoint : h.CriticalEndpoint
  normalizes_left : endpoint.conjugate D.UH ≤ normalizer (K : Set G)
  normalizes_right : endpoint.conjugate D.UH ≤ normalizer (Kplus : Set G)
  point_support : endpoint.conjugate D.V₁ ≤ ⁅D.UH,K⁆
  positive : 0 < Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH)
  comparison : Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH) ≤
    rank (((endpoint.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)))
  rank_le_two :
    rank (((endpoint.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) ≤ 2

namespace PlacedEndpoint
variable {D : ChapterF.Section09.Setup G} {h : D.Hypothesis} {K Kplus : Subgroup G}

/-- Once endpoint symmetry has excluded equality of the two ranks, the
literal denominator has index two. The power-of-two assertion comes from
the actual elementary module, not from an extra numerical premise. -/
theorem index_eq_two_of_strict_comparison [IsElementaryAbelian 2 D.UH]
    (p : PlacedEndpoint h K Kplus)
    (hs : Nat.log 2 ((D.UH ⊓ p.endpoint.conjugate D.QH).relIndex D.UH) <
      rank (((p.endpoint.conjugate D.UH).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H)))) :
    (D.UH ⊓ p.endpoint.conjugate D.QH).relIndex D.UH = 2 := by
  have hp := p.positive
  have hr := p.rank_le_two
  have hd : Nat.log 2 ((D.UH ⊓ p.endpoint.conjugate D.QH).relIndex D.UH) = 1 := by
    omega
  rw [log_relIndex_eq_quotient_finrank] at hd
  rw [relIndex_eq_two_pow_quotient_finrank,hd]
  rfl
/-- The same strict comparison forces rank two of the literal star image. -/
theorem actor_rank_eq_two_of_strict_comparison
    (p : PlacedEndpoint h K Kplus)
    (hs : Nat.log 2 ((D.UH ⊓ p.endpoint.conjugate D.QH).relIndex D.UH) <
      rank (((p.endpoint.conjugate D.UH).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H)))) :
    rank (((p.endpoint.conjugate D.UH).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) = 2 := by
  have hp := p.positive
  have hr := p.rank_le_two
  omega
end PlacedEndpoint

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Representation
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The final natural/dual placement on p.1041 uses the same placed
endpoint and the literal opposite-core intersection. The source symmetry
argument must still establish strict comparison, and the component action
must identify the rank-two image on the marked natural space. -/
theorem source_point_in_natural_or_dual_of_strict_comparison
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    (A W Wdual : Subgroup G)
    (π : A →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (c : BinaryConjugationSection A W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π))
    (cdual : BinaryConjugationSection A Wdual (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π)))
    (hactor : p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ A)
    (hW : W ≤ conjugateSpanBy (localModule T M) Mc)
    (hWdual : Wdual ≤ conjugateSpanBy (localModule T M) Mc)
    (hs : Nat.log 2 ((conjugateSpanBy (localModule T M) Mc ⊓
        p.endpoint.conjugate (Mc.pCoreIn 2)).relIndex
        (conjugateSpanBy (localModule T M) Mc)) <
      rank (((p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf Mc).map
        (QuotientGroup.mk' (pCore 2 Mc))))
    (hrank : 2 ≤ rank
      (((p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf A).map π)) :
    p.endpoint.conjugate (centralInvolutions T) ≤ W ∨
      p.endpoint.conjugate (centralInvolutions T) ≤ Wdual := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hi := p.index_eq_two_of_strict_comparison hs
  have hd := (source_critical_denominators hG T hempty hM hunique hmany hcard e hab p.endpoint).1
  apply source_point_in_natural_or_dual_of_index_two hG T hempty hM hunique hmany hcard e hab
    p.endpoint A W Wdual π c cdual hactor hW hWdual _ hrank
  rw [hd]
  exact hi

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
