module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Reduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Models
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow

/-!
# The nonbinary pushing-up configuration with literal quotient comparison

Failure of uniqueness for the actual fixed residual constructs the C.2.8
configuration. Its intersection residual is normal in H intersect N(L),
covers L modulo O2(L), and has the same full quotient on representatives.
Every exceptional quotient in 4.4.3 is excluded. The characteristic-two
section kernel and radical conditions are proved, and the full module
contains a section-centralizer conjugate of the original V and has order
at least 64. Exclusion of this configuration by the specialized C.4.8
analysis remains an obligation of the odd-normalizer task.

Source: Aschbacher--Smith, 4.2.12--13 and 4.4.5--6, printed pp.610--612,620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

@[expose] def PushingUpCase (L V A : Subgroup G) : Prop :=
    ∃ J H W : Subgroup G,
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧ V ≤ J.pCoreIn 2 ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let MH := H ⊓ normalizer (L : Set G)
      let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H MH LH (J.pCoreIn 2) W ∧
      (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
      (LH.subgroupOf MH).Normal ∧
      (∃ e : (LH ⧸ pCore 2 LH) ≃* (L ⧸ pCore 2 L),
        ∀ i : LH, e (QuotientGroup.mk' (pCore 2 LH) i) =
          QuotientGroup.mk' (pCore 2 L)
            (inclusion ((map_subtype_le _).trans inf_le_left) i)) ∧
      ¬ ExceptionalQuotient (LH ⧸ pCore 2 LH) ∧
      pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
      ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
      generalizedFitting X = pCore 2 X ∧
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
      64 ≤ Nat.card W ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W

theorem pushingUp_configuration {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    PushingUpCase L V A := by
  have hcomm := actor_commutator D S hA
  obtain ⟨J,H,P,hpush,hH,hJH,hstrict,hC,c,_,hVW⟩ :=
    Chapter4.Section02.Unitary.chosen_oddActorResidual_C28
      S.source.toHypothesis1221 D A (hA.trans inf_le_left) hcomm ho
      (hA.trans inf_le_right) (component_sylow_unique D S) hnot
  have hFL : oddActorResidual L A ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFJ : oddActorResidual L A ≤ J :=
    (inf_eq_left.mpr hFL).symm.le.trans (hpush.2.trans inf_le_left)
  obtain ⟨hc,_,hVF,_⟩ := actor_cover D S hA ho
  have hcJ : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) :=
    hc.subset.trans (Set.mul_subset_mul_right hFJ)
  have hVJ : V ≤ J.pCoreIn 2 := hVF.trans hpush.1
  have hr := chosen_intersection_twoResidual_eq_solvableResidual S.source.toHypothesis1221 hcJ hJH
  have hd := chosen_oddActorResidual_counterexample_residual
    S.source.toHypothesis1221 D hcJ hJH hVJ
  rw [hr] at hd
  obtain ⟨e,he⟩ := cover_quotient ((map_subtype_le _).trans inf_le_left) hd.1.subset
  have hno := not_exceptional_of_equiv D S e
  have hsize : 64 ≤ Nat.card (Chapter4.Section02.Unitary.fullModule L
      ((P : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) := by
    have hb := card_le_of_le hVW
    rw [card_map_of_injective (MulAut.conj (c : G)).injective] at hb
    exact (module_card_ge D S).trans hb
  exact ⟨J,H,_,hpush,hH,hJH,hstrict,hVJ,hC,hd.1,hd.2.2.1,⟨e,he⟩,hno,
    hC.oddCore_eq_bot,hC.isRadical,hC.sylow_in_normalClosure,
    hC.section_fitting_eq_core,hC.section_sylow_in_H,hsize,c,hVW⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
