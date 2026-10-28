module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.Quotient
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.PointSylow.MarkedOrbit
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow

/-!
# The marked PSL₅(2) pushing-up configuration

Failure of uniqueness for the actual odd-actor residual gives the genuine
C.2.8 configuration. The intersection residual covers L modulo O₂(L), hence
has the same marked PSL₅(2) quotient, outside every exceptional row of 4.4.3.
The full source module contains the section-centralizer conjugate of the
original exterior module and therefore has order at least 1024.

All C.2.8, radical, section-kernel and quotient premises are constructed here
from the ordinary uniqueness of LT. The Hall consumer discharges that earlier
premise using exterior_component_sylow_unique.
The remaining C.4.8/4.2.13 classification must exclude this configuration;
neither its exclusion nor residual uniqueness is asserted in this module.
Source: Aschbacher--Smith, 4.2.12--13 and 4.4.5--6, pp.610--612,620.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The contrary branch constructs the actual source configuration, its
characteristic-two section, the marked quotient and the large full module. -/
theorem exterior_oddActorResidual_pushingUp_configuration
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) s.marking.M)
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M) :
    ∃ J H W : Subgroup G,
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ s.marking.M < H ∧ V ≤ J.pCoreIn 2 ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let MH := H ⊓ s.marking.M
      let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H MH LH (J.pCoreIn 2) W ∧
      (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
      (LH.subgroupOf MH).Normal ∧
      Nonempty ((LH ⧸ pCore 2 LH) ≃* Representation.SL5TenDimensional.Group) ∧
      ¬ OddNormalizerExceptionalQuotient (LH ⧸ pCore 2 LH) ∧
      pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
      ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
      generalizedFitting X = pCore 2 X ∧
      (∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
      1024 ≤ Nat.card W ∧
      ∃ c : sectionCentralizerIn s.marking.M L,
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  have hcomm := s.marking.centralizing_actor_commutator hAM hAV
  obtain ⟨J,H,S,hpush,hH,hJH,hstrict,hC,c,_,hVW⟩ :=
    Chapter4.Section02.Unitary.chosen_oddActorResidual_C28
      h.toHypothesis1221 D A hAM hcomm hodd hAV hM hnot
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFJ : oddActorResidual L A ≤ J :=
    (inf_eq_left.mpr hFL).symm.le.trans (hpush.2.trans inf_le_left)
  obtain ⟨hc,_,hVF,_⟩ := s.marking.centralizing_actor_cover h A hAM hodd hAV
  have hcJ : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) :=
    hc.subset.trans (Set.mul_subset_mul_right hFJ)
  have hVJ : V ≤ J.pCoreIn 2 := hVF.trans hpush.1
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h.toHypothesis1221 hcJ hJH
  have hd := chosen_oddActorResidual_counterexample_residual
    h.toHypothesis1221 D hcJ hJH hVJ
  rw [hr] at hd
  obtain ⟨he, hno⟩ := s.marking.cover_quotient
    ((map_subtype_le _).trans inf_le_left) hd.1.subset
  obtain ⟨e, _⟩ := he
  have hsize : 1024 ≤ Nat.card (Chapter4.Section02.Unitary.fullModule L
      ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) := by
    have hb := card_le_of_le hVW
    rwa [card_map_of_injective (MulAut.conj (c : G)).injective, s.marking.card_module] at hb
  exact ⟨J,H,_,hpush,hH,hJH,hstrict,hVJ,hC,hd.1,hd.2.2.1,⟨e⟩,hno,
    hC.oddCore_eq_bot,hC.isRadical,hC.sylow_in_normalClosure,
    hC.section_fitting_eq_core,hC.section_sylow_in_H,hsize,c,hVW⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
