module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRestrictionsComponents
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Complete
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PrimeChoice
public import Theory.GroupTheory.ReducedNormal.SylowCenter

/-!
# Quasisimplicity of the original H-star overcomponent

For a nonquasisimple faithful maximal local component Y, choose a nontrivial
canonical odd radical. The proved 3.2.14 centralization theorem makes it
centralize the original Sylow omega-center, which lies in R₂(YT). No escape
puts the radical and T in N_G(L). Its starred uniqueness theorem identifies
that normalizer with the radical normalizer, so YT lies in N_G(L).

The generating component of an escaping nonsolvable H cannot lie in such Y.
Thus its actual faithful maximal overcomponent satisfies Hypothesis 12.2.3,
with the same ambient exclusions. The multiple-overgroup standing hypothesis
is retained explicitly. The residual model and module alternatives remain
with the assembly owner qt-d-12213-hstar-natural.

Source: Aschbacher–Smith, 12.2.7, final paragraph, printed pp.797–798;
1.3.7–8 and 3.2.14. The prime-choice lemma imported from Chapter 13 uses
only A.3.6 and the canonical radical construction, not its later conclusions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H X Y : Subgroup G}

private theorem omega_le_join_reduced (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hY : Y ∈ Chapter1.L G (T : Subgroup G)) :
    omegaCenterIn (T : Subgroup G) ≤
      (reducedTwoSubgroup (Y ⊔ (T : Subgroup G) : Subgroup G)).map
        (Y ⊔ (T : Subgroup G)).subtype := by
  let J := Y ⊔ (T : Subgroup G)
  let S : Sylow 2 J := T.subtype le_sup_right
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨hY.2.2, show (T : Subgroup G) ≤ J from le_sup_right⟩)
  have hh := map_mono (f := J.subtype) (sylow_omegaCenter_le_reduced S hc)
  change (Stellmacher.omegaOneCenterAmbient (S : Subgroup J)).map J.subtype ≤ _ at hh
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective] at hh
  change Stellmacher.omegaOneCenterAmbient (((T : Subgroup G).subgroupOf J).map J.subtype) ≤ _ at hh
  rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hh

/-- The nonquasisimple branch forces the whole original local join into M. -/
theorem nonquasisimple_overgroup_le_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hY : FaithfulMaximalLocal T Y)
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  obtain ⟨p,hp,ho,_,hd,_,_⟩ := Chapter13.Section01.exists_odd_radical_source h.simpleQTKE h36
    (show Y ∈ Chapter13.Section01.nonquasisimpleFaithful T from
      ⟨(mem_faithfulLocalComponents_iff T Y).mpr ⟨hY.1.1,hY.2⟩,hn⟩)
  let : Fact p.Prime := ⟨hp⟩
  have hstar := Chapter3.RadicalCentralization.ChosenStars.XiP_mem_XiStar
    h.simpleQTKE T hY.1 hn ho hd
  have hrad := Chapter3.RadicalCentralization.ChosenStars.maximal_solvableRadical_centralizes_sylowJoin
    h.simpleQTKE T hmany hY.1 hn
  have hXiZ : XiP p Y ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G) :=
    ((Chapter3.RadicalCentralization.XiP_le_solvableRadical Y p).trans hrad).trans
      (centralizer_le (omega_le_join_reduced h.simpleQTKE hY.1.1))
  have hXiM : XiP p Y ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le (hXiZ.trans (chosen_omega_centralizer_le_of_noEscape_at h D structural hnone))
      (structural L h).1
  have hmax : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
      (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
      h.simpleQTKE T h.maximal_faithful.1
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have he : normalizer (L : Set G) = normalizer (XiP p Y : Set G) := by
    have hh : normalizer (L : Set G) ∈
        {M : Subgroup G | IsMaximalTwoLocal M ∧ XiP p Y ⊔ (T : Subgroup G) ≤ M} :=
      ⟨hmax,hXiM⟩
    rw [(Chapter1.XiEmbedding.normalizer_unique_of_XiStar_knownSimple h.simpleQTKE T hstar).2] at hh
    exact Set.mem_singleton_iff.mp hh
  rw [he]
  exact sup_le (Y.le_normalizer.trans (normalizer_le_normalizer_XiP p Y)) hstar.1.invariant

/-- An overcomponent containing the escaping original component is quasisimple
modulo its own two-core. -/
theorem HStarGeneratingComponent.overcomponent_quasisimple_of_many_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hXY : X ≤ Y) (hY : FaithfulMaximalLocal T Y) :
    IsQuasisimple (Y ⧸ pCore 2 Y) := by
  by_contra hn
  exact C.escapes (hXY.trans (le_sup_left.trans
    (nonquasisimple_overgroup_le_normalizer_at h D structural hmany hnone hY hn)))

/-- The original nonsolvable H-star supplies a faithful maximal overcomponent
to which the same ambient-local 12.2.2 producers apply. -/
theorem chosen_hstar_exists_quasisimple_overcomponent_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y := by
  obtain ⟨X,Y,C,hXY,hY,hf⟩ := chosen_hstar_exists_faithful_overcomponent_at
    h D structural hnone hTI hH hs
  exact ⟨X,Y,C,hXY,{
    simpleQTKE := h.simpleQTKE
    maximal_faithful := ⟨hY,hf⟩
    quasisimple := C.overcomponent_quasisimple_of_many_at h D structural hmany hnone hXY ⟨hY,hf⟩
    no_rankTwo := h.no_rankTwo
    no_M22 := h.no_M22
    no_M23 := h.no_M23
    no_J4 := h.no_J4 }⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
