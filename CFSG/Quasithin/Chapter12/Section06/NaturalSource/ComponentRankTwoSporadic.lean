module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoMathieu
public import Theory.SpecificGroups.SporadicSylowFixerCentralizers

/-!
# The surviving sporadic row of the original rank-two component

The native J₂, HS, Held and Rudvalis centralizer bounds contradict the
faithful original Sylow E₉ in the same marked involution centralizer.
Simplicity for the Rudvalis realization is inherited from the original
selected component. Together with the Mathieu and J₁ exclusions, the
full sporadic alternative reduces to the actual J₄ carrier.

This leaves J₄ and the nonsporadic simple models to be excluded. The
rank-one branch, abelian point span and universal natural reduction
remain unproved. All original earlier-geometry hypotheses are retained.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, last paragraph.
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
/-- Exclude the actual Sporadic.LeechRelated.J2.Carrier model on the original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_jankoTwo
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Sporadic.LeechRelated.J2.Carrier) := by
  rintro ⟨e⟩
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact Sporadic.LeechRelated.J2.not_nine_dvd_sylow_fixer_centralizer P α hα hP h9

include hz hTV hTz hbound hH hn a in
/-- Exclude the actual Sporadic.LeechRelated.HS.Carrier model on the original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_higmanSims
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact Sporadic.LeechRelated.HS.not_nine_dvd_sylow_fixer_centralizer P α hα hP h9

include hz hTV hTz hbound hH hn a in
/-- Exclude the actual Held.He model on the original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_held
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Held.He) := by
  rintro ⟨e⟩
  obtain ⟨α,hα,⟨P,hP⟩,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact Held.not_nine_dvd_sylow_fixer_centralizer P α hα hP h9

include hz hTV hTz hbound hH hn a in
/-- Exclude the actual Rudvalis.Model model on the original rank-two component. -/
theorem SourceHypothesis.original_rank_two_not_rudvalis
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
    S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  obtain ⟨α,hα,_,h9⟩ := S.original_rank_two_model_centralizer D hZ z hz hTV hTz hbound hH hn c a hTI hns hr e
  exact Rudvalis.not_nine_dvd_involution_aut_centralizer α hα h9

include hz hTV hTz hbound hH hn a in
/-- The full sporadic branch now reduces to the literal J4 model. -/
theorem SourceHypothesis.original_rank_two_sporadic_jankoFour
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (Nonabelian.Setup.star H c.K)) :
    Nonempty (Nonabelian.Setup.star H c.K ≃* Janko4.Model) := by
  obtain ⟨name,hname,he⟩ := S.original_rank_two_sporadic_restricted D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr hm
  rcases hname with rfl|rfl|rfl|rfl|rfl
  · exact (S.original_rank_two_not_jankoTwo D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim
  · exact he
  · exact (S.original_rank_two_not_higmanSims D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim
  · exact (S.original_rank_two_not_held D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim
  · exact (S.original_rank_two_not_rudvalis D hZ z hz hTV hTz hbound hH hn c a hTI hns hr he).elim

include hz hTV hTz hbound hH hn a in
/-- Retain the exact original centralizer-core obstruction and the remaining
actual models after excluding every sporadic row except J4. -/
theorem SourceHypothesis.original_rank_two_remaining_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ((ClassicalGroup.IsPSU B 3 3 ∨ ClassicalGroup.IsPSU B 3 5) ∨
        (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel B f ∧
          ¬ ClassicalGroup.IsPSL B 3 (2^f)) ∨
        ClassicalGroup.IsPSL B 5 2 ∨ Nonempty (B ≃* Janko4.Model)) := by
  obtain ⟨hcore,hmodels⟩ := S.original_rank_two_restricted_models D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hr
  refine ⟨hcore,?_⟩
  rcases hmodels with h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (S.original_rank_two_sporadic_jankoFour D hZ z hz hTV hTz
      hbound hH hn c a hTI hns hr h)))
end CFSG.Quasithin.Chapter12.Section06
