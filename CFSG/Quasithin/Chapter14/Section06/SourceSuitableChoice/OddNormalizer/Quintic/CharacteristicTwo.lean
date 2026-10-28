module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.FittingEscape
public import Theory.GroupTheory.PCoreCentralizerOvergroup

/-!
# Characteristic two in the actual second normalizer

The original central point lies in O₂(K₂), hence in the two-core of
N_G(K₂). Its centralizer is Mc, so the core centralizer inside N_G(K₂)
lies in the intersection with Mc. That intersection has the same
self-centralizing two-core as Mc. The characteristic-two overgroup
criterion therefore applies to N_G(K₂).

This derives the characteristic-two step of 14.6.15 from the intermediate
module geometry, without a new normalizer or component hypothesis.
Source: Aschbacher--Smith 14.6.15, printed p.1034.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open Chapter1.RadicalExclusions ChapterA.Section04
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

private theorem characteristicTwo_of_core_intersection (Mc N Z : Subgroup G)
    (hMc : Mc ∈ Chapter1.He G)
    (hcore : (Mc ⊓ N).pCoreIn 2 = Mc.pCoreIn 2)
    (hZ : Z ≤ N.pCoreIn 2) (hcentral : centralizer (Z : Set G) = Mc) :
    generalizedFitting N = pCore 2 N := by
  let B := Mc ⊓ N
  have hB : B ∈ Chapter1.He G := by
    change B ⊓ centralizer (B.pCoreIn 2 : Set G) ≤ B.pCoreIn 2
    change Mc ⊓ centralizer (Mc.pCoreIn 2 : Set G) ≤ Mc.pCoreIn 2 at hMc
    change (Mc ⊓ N) ⊓ centralizer ((Mc ⊓ N).pCoreIn 2 : Set G) ≤ (Mc ⊓ N).pCoreIn 2
    rw [hcore]
    exact (inf_le_inf_right _ inf_le_left).trans hMc
  have hcB : centralizer (pCore 2 (B.subgroupOf N) : Set (B.subgroupOf N)) ≤
      pCore 2 (B.subgroupOf N) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe
      (show B ≤ N from inf_le_right))).mpr (Chapter1.mem_He_iff.mp hB)
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_le_of_overgroup 2 (B.subgroupOf N) hcB
  intro x hx
  refine ⟨?_,x.property⟩
  rw [←hcentral]
  intro z hz
  obtain ⟨q,hq,hqz⟩ := hZ hz
  have he := congrArg Subtype.val (hx q hq)
  change (q : G) * (x : G) = (x : G) * (q : G) at he
  change (q : G) = z at hqz
  rwa [hqz] at he

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (H1 H2 : Subgroup G)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (c : CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH)
      a Mc H1)
    (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) c.endpoint.representative)

/-- The second normalizer has characteristic two, with every subgroup
and centralizer computed on the original ambient carriers. -/
theorem source_secondNormalizer_characteristicTwo :
    generalizedFitting (normalizer (d.K2 : Set G)) = pCore 2 (normalizer (d.K2 : Set G)) := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hHe : Mc ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (hG.evenCharacteristic T Mc hmax hTMc)
  apply characteristicTwo_of_core_intersection Mc _ (centralInvolutions T) hHe d.intersection_core
  · exact d.point_core.trans (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.K2)
      ((pCoreIn_le 2 d.K2).trans d.K2.le_normalizer)
      (normalizer_le_normalizer_characteristic_image d.K2 (pCore 2 d.K2)))
  · exact hMc.symm
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
