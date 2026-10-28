module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterModels
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRestrictionsNormalization
public import Theory.GroupTheory.PerfectSylowPreservingAction
import all CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceOvercomponent

/-!
# The original escaping residual without a global TI hypothesis

Nonsolvability and H-star minimality make H minimal parabolic. E.2.2
then constructs its generating component. The explicit omega-center
centralizer guard forces movement. Odd-radical uniqueness excludes a
nonquasisimple maximal overcomponent, and the seven-module classification
identifies the original component with the literal O²(H).

The internal import reuses the Sylow-center inclusion from the earlier
12.2.7 proof, without changing that module's public interface.
Source: Aschbacher–Smith, 12.2.7 and 12.3.2, printed pp.797–798,807.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 Section02.RecognitionSource
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L H X Y : Subgroup G}

omit [Finite G] in
/-- The literal omega module agrees with the earlier 12.2.7 presentation. -/
theorem localModule_eq_hstarOmegaModule : localModule T H = hstarOmegaModule T H := by
  unfold localModule hstarOmegaModule
  rw [sylowCenterSeed_eq]

/-- Nonsolvable H-star members are minimal parabolic without any global TI assumption. -/
theorem local_hstar_minimalParabolic
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤ := by
  have hn : ¬ ((T : Subgroup G).subgroupOf H).Normal := by
    intro hn
    have hHN := (normal_subgroupOf_iff_le_normalizer hH.1.1.2).mp hn
    let := T.normalizer_isSolvable_two
    exact hs (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hHN) (inclusion_injective hHN))
  obtain ⟨hTB,hBH,_⟩ := Chapter3.HStar.unique_maximal T hTM hH
  exact (ChapterB.intrinsic_minimalParabolic T H (H ⊓ normalizer (L : Set G))
    (Chapter3.HStar.minimalParabolic T hTM hH (Or.inr hn)) hTB hBH).1

/-- An already chosen escaping H-star supplies the standing multiple-local
guard, so the classification itself does not need that extra premise. -/
theorem local_hstar_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  obtain ⟨⟨V,⟨D⟩⟩⟩ := (structural L h).2.1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
    h.simpleQTKE T h.maximal_faithful.1
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hcore : pCore 2 H ≠ ⊥ := by
    intro he
    apply hH.1.1.1
    change (pCore 2 H).map H.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
  apply Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
  refine ⟨⟨normalizer (L : Set G),⟨hM,(structural L h).1⟩,
    N,⟨hN,hH.1.1.2.trans hHN⟩,?_⟩,Set.toFinite _⟩
  intro he
  exact hH.1.2 (he.symm ▸ hHN)

/-- E.2.2 gives an actual moving component under the printed centralizer guard. -/
theorem local_exists_generating_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X : Subgroup G, HStarGeneratingComponent T L H X := by
  let S := T.subtype hH.1.1.2
  obtain ⟨X,hX,hq,hgen,_⟩ := ChapterE.Structure.source_original_component
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) S
    (local_hstar_minimalParabolic (structural L h).1 hH hs) hs
  let X' := X.map H.subtype
  have hX'H : X' ≤ H := map_subtype_le _
  have hXsub : X'.subgroupOf H = X := comap_map_eq_self_of_injective H.subtype_injective _
  have hgen' : X' ⊔ (T : Subgroup G) = H := by
    have he := congrArg (map H.subtype) hgen
    have ht : ((S : Subgroup H)).map H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hH.1.1.2
    simpa only [Subgroup.map_sup, ht, ← MonoidHom.range_eq_map, range_subtype] using he
  let e : X ≃* X' := X.equivMapOfInjective H.subtype H.subtype_injective
  let eq : (X ⧸ pCore 2 X) ≃* (X' ⧸ pCore 2 X') :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let := hq
  have hq' : IsQuasisimple (X' ⧸ pCore 2 X') := IsQuasisimple.of_mulEquiv eq
  let := hX.perfect
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hXK : X ≤ pResidual 2 H := le_of_isPerfect_of_solvable_quotient X (pResidual 2 H)
  have hres : (pResidual 2 H).map H.subtype = componentOrbit X' (T : Subgroup G) := by
    rw [embedded_pResidual_eq_conjugateSpanBy X' (T : Subgroup G) H
      (map_mono hXK) T.isPGroup' hgen', conjugateSpanBy_eq_iSup_conj]
    rfl
  have hout : ¬ X' ≤ normalizer (L : Set G) := by
    intro hx
    apply hH.1.2
    rw [← hgen']
    exact sup_le hx (structural L h).1
  refine ⟨X', ⟨⟨hX'H,hXsub.symm ▸ hX⟩,hq',hgen',hres,hout,?_⟩⟩
  intro he
  apply hout
  exact ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (centralizer_le (le_conjugateSpanBy _ _))).trans
      (by simpa only [sylowCenterSeed_eq] using hZ)

/-- Odd-radical uniqueness excludes every nonquasisimple escaping overcomponent. -/
theorem local_nonquasisimple_overgroup_le_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G)) (hY : FaithfulMaximalLocal T Y)
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
    sup_le (hXiZ.trans (by simpa only [sylowCenterSeed_eq] using hZ))
      (structural L h).1
  obtain ⟨⟨V,⟨D⟩⟩⟩ := (structural L h).2.1
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

/-- The original residual and a faithful maximal overcomponent under the actual
same-G,T inputs. No global TI or no-escape hypothesis is needed. -/
theorem local_residual_overcomponent
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    HStarGeneratingComponent T L H (localResidual H) ∧
      ∃ Y : Subgroup G, localResidual H ≤ Y ∧ Hypothesis1223 KnownSimple.IsKnownSimple T Y := by
  obtain ⟨X,C⟩ := local_exists_generating_component h structural hZ hH hs
  obtain ⟨Y,hXY,hY,hf⟩ := C.exists_faithful_maximal_overcomponent h hH
  have hq : IsQuasisimple (Y ⧸ pCore 2 Y) := by
    by_contra hn
    exact C.escapes (hXY.trans (le_sup_left.trans
      (local_nonquasisimple_overgroup_le_normalizer h structural (local_hstar_many h structural hH) hZ ⟨hY,hf⟩ hn)))
  have hy : Hypothesis1223 KnownSimple.IsKnownSimple T Y :=
    { h with maximal_faithful := ⟨hY,hf⟩, quasisimple := hq }
  have he := C.eq_residual_of_normalized
    (C.normalized_of_overcomponent_at structural modules hH hXY hy)
  change X = localResidual H at he
  exact ⟨he ▸ C,Y,he ▸ hXY,hy⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
