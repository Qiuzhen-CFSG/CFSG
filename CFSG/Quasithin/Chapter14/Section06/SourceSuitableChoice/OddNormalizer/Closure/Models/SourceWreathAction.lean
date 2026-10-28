module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.StrictSource

/-!
# The source exchanged closure acts faithfully on its marked square

Apply the actual 14.6.14 component and layer comparison to the original
outside H. For each surviving exchanged component, the same Mc/O₂(Mc)
acts faithfully in its automorphism wreath, with the inner coordinates and
inverse-conjugating exchanger retained. The component's two-group outer
automorphisms prove Mc = Kz T.

The last theorem keeps exactly the unfinished step visible: the full outer
image must still be identified, giving S₅ wr C₂, Aut(PSL₂(16)) wr C₂, or
PSL₃(2) wr C₂. No closure classification, p=3 result, normalizer equality or
suitability is assumed. These source conclusions and the parabolic normalizers
remain with qt-e-suitable-odd-normalizer. The earlier primitive and exchanged
inputs retain qt-e-quintic-recognition and qt-e-14612-singleton; final suitable
choice belongs to qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.14--16, printed pp.1033--1035.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.XiEmbedding
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The actual exchanged source branch supplies the faithful marked wreath
action and the Sylow supplement, with no additional model or action premise. -/
theorem source_exchanged_closure_actions
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc)) :
    Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
      ExchangedWreathRows (T : Subgroup G) Mc (residualClosure H Mc) L p := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  apply exchanged_closure_wreath_rows hTMc hL hcomp hq
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    hm.1 hlayer
  exact source_strict_exchanged_component_models
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax L hcomp hm

/-- The original closure alternatives reduce to determining the full image of
these faithful marked wreath actions. Both residual identities and the full
layer are retained, and Mc = Kz T is now proved in every exchanged row. -/
theorem source_closure_alternatives_or_marked_wreath_actions
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
        ExchangedWreathRows (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
  rcases source_closure_alternatives_or_exchanged_models
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hc | ⟨L,hL,hcomp,hq,hm,_hmodels,hr,hr3,hlayer⟩
  · exact Or.inl hc
  · obtain ⟨hgen,ha⟩ := source_exchanged_closure_actions
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax
      L hL hcomp hq hm hlayer
    exact Or.inr ⟨L,hL,hcomp,hq,hm,hgen,ha,hr,hr3,hlayer⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
