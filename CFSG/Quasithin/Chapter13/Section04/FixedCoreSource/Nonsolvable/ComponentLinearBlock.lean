module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearMS
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMS
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ChiefBound

/-!
# The original covered row's Baumann module models and cubic bound

Apply the natural-point MS theorem to the actual pair constructed in
ComponentLinearMS. Transport its quotient marking and conjugation action
through both subgroup inclusions, obtaining the natural or doubled natural
model on Q=[O₂(K Baum(R)),K] in the original ambient group. The normal
natural eight in Q bounds cubic movement on the entire two-core by two;
this bound is transported by the same inclusions.

This supplies the upper bound for the covered-original linear-three row.
The original covered-module lower bound, its comparison with this two-core,
and the remaining 13.4.10–17 arguments stay with qt-d-1341-nonsolvable-source.
No chief-factor contradiction or complete C.1.37 block recognition is
claimed here. LargeDistanceInput and the earlier structural/module source
premises retain their existing producers and final discharge at
qt-d-1341-fixed-core-source. Both escaping weights remain required in
that final assembly.

Source: Aschbacher–Smith 13.4.10(2), printed p.908; C.1.34 and C.1.37,
printed pp.136–137 and 141–143.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter12.Section08 Chapter14.Section03.FaithfulSource
open ChapterC.NaturalPointControl
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
open Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource
universe u

private theorem map_linear_models {X G : Type*} [Group X] [Group G]
    (K D : Subgroup X) (f : X →* G) (hf : Function.Injective f)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hm : HasSectionModel K D ⊥ (linearThreeActor e) BinaryLinearThree.W ∨
      HasSectionModel K D ⊥ (linearThreeActor e) (BinaryLinearThree.W.prod BinaryLinearThree.W)) :
    ∃ e' : (K.map f ⧸ pCore 2 (K.map f)) ≃* BinaryLinearThree.Group,
      HasSectionModel (K.map f) (D.map f) ⊥ (linearThreeActor e') BinaryLinearThree.W ∨
      HasSectionModel (K.map f) (D.map f) ⊥ (linearThreeActor e')
        (BinaryLinearThree.W.prod BinaryLinearThree.W) := by
  let i := K.equivMapOfInjective f hf
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let e' := c.trans e
  have ha (x : K) : linearThreeActor e' (i x) = linearThreeActor e x := by
    change e (c (QuotientGroup.mk' _ (i x))) = e (QuotientGroup.mk' _ x)
    change e (QuotientGroup.mk' _ (i.symm (i x))) = e (QuotientGroup.mk' _ x)
    rw [i.symm_apply_apply]
  refine ⟨e',?_⟩
  rcases hm with hm | hm
  · exact Or.inl (by simpa only [Subgroup.map_bot] using hm.map f hf (linearThreeActor e') ha)
  · exact Or.inr (by simpa only [Subgroup.map_bot] using hm.map f hf (linearThreeActor e') ha)

private theorem ambient_natural_point_block
    {G : Type u} [Group G] [Finite G] (K R X : Subgroup G)
    (hKX : K ≤ X) (hRX : R ≤ X)
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (a : NaturalAction U) (hR : a.R = R.subgroupOf X)
    (hres : pResidual 2 X = K.subgroupOf X)
    (hi : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ) :
    let Q := ⁅(K ⊔ ChapterB.baumann R).pCoreIn 2,K⁆
    ∃ e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      (HasSectionModel K Q ⊥ (linearThreeActor e) BinaryLinearThree.W ∨
        HasSectionModel K Q ⊥ (linearThreeActor e) (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∧
      ∀ A : Subgroup G, IsPGroup 3 A → A ≤ K →
        conjugationCubicLength A ((K ⊔ ChapterB.baumann R).pCoreIn 2) ≤ 2 := by
  let f : a.J →* G := X.subtype.comp a.J.subtype
  have hf : Function.Injective f := X.subtype_injective.comp a.J.subtype_injective
  have hL : a.LJ.map f = K := by
    rw [←map_map]
    change ((pResidual 2 X).subgroupOf a.J |>.map a.J.subtype).map X.subtype = K
    rw [map_subgroupOf_eq_of_le (show pResidual 2 X ≤ a.J from le_sup_left),
      hres,map_subgroupOf_eq_of_le hKX]
  have hBm : a.B.map X.subtype = ChapterB.baumann R := by
    change (ChapterB.baumann a.R).map X.subtype = _
    dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha]
    rw [baumann_map_injective X.subtype X.subtype_injective,hR,
      map_subgroupOf_eq_of_le hRX]
  have hB : a.BJ.map f = ChapterB.baumann R := by
    rw [←map_map]
    change (a.B.subgroupOf a.J |>.map a.J.subtype).map X.subtype = _
    rw [map_subgroupOf_eq_of_le (show a.B ≤ a.J from le_sup_right),hBm]
  have hJ : a.J.map X.subtype = K ⊔ ChapterB.baumann R := by
    change (pResidual 2 X ⊔ a.B).map X.subtype = _
    rw [Subgroup.map_sup,hres,map_subgroupOf_eq_of_le hKX,hBm]
  have hcore : (pCore 2 a.J).map f = (K ⊔ ChapterB.baumann R).pCoreIn 2 := by
    rw [←map_map]
    change (a.J.pCoreIn 2).map X.subtype = _
    rw [map_pCoreIn_of_injective 2 _ _ X.subtype_injective,hJ]
  have hQ : (msQ a.LJ a.BJ).map f = ⁅(K ⊔ ChapterB.baumann R).pCoreIn 2,K⁆ := by
    rw [←msQ_map _ _ _ hf,hL,hB]
    rfl
  obtain ⟨e,hm⟩ := natural_or_double_of_msInput a hi
  have hc := NaturalAction.core_card_le_of_models hi e hm
  have hmodels := map_linear_models a.LJ (msQ a.LJ a.BJ) f hf e hm
  rw [hL,hQ] at hmodels
  obtain ⟨e',hm'⟩ := hmodels
  refine ⟨e',hm',?_⟩
  intro A hA hAK
  let Aj := A.comap f
  have hAj : IsPGroup 3 Aj := hA.comap_of_injective f hf
  have hAjK : Aj ≤ a.LJ := by
    intro x hx
    have hm : f x ∈ a.LJ.map f := hL.symm ▸ hAK hx
    obtain ⟨y,hy,hyx⟩ := hm
    exact hf hyx ▸ hy
  have hAm : Aj.map f = A := map_comap_eq_self (hAK.trans (hL ▸ map_le_range _ _))
  let : IsElementaryAbelian 2 (U.subgroupOf a.J) := IsElementaryAbelian.subgroupOf a.module_le_J
  have hb := a.inMSGroup.core_length_le_two hi hc Aj hAj hAjK
  rw [←length_map_injective f hf Aj (pCore 2 a.J),hAm,hcore] at hb
  exact hb

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Apply the natural-point MS alternatives on the original covered row.
The literal Baumann commutator core is natural or doubled natural, and
every cubic of K moves at most two binary layers on its two-core. -/
theorem covered_linear_component_block
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
    let Q := ⁅(K ⊔ ChapterB.baumann R).pCoreIn 2,K⁆
    ∃ e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
      (HasSectionModel K Q ⊥ (linearThreeActor e) BinaryLinearThree.W ∨
        HasSectionModel K Q ⊥ (linearThreeActor e) (BinaryLinearThree.W.prod BinaryLinearThree.W)) ∧
      ∀ A : Subgroup G, IsPGroup 3 A → A ≤ K →
        conjugationCubicLength A ((K ⊔ ChapterB.baumann R).pCoreIn 2) ≤ 2 := by
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨hn,hel,a,hR,hres,⟨hi⟩⟩ := covered_linear_component_ms hl h₀ h structural modules
    D m h1332 fixed hindex hc z hzT hzL hKz hHN hKM hfK eK
  let := hn
  let := hel
  exact ambient_natural_point_block K R X le_sup_left le_sup_right (U.subgroupOf X)
    a hR hres hi

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
