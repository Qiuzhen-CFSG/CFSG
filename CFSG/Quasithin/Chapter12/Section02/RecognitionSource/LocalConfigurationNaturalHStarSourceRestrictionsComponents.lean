module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRestrictionsCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.PResidual.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful

/-!
# The original generating component and faithful overcomponent in 12.2.7

E.2.2 produces an actual C-component X of the nonsolvable H, with
quasisimple X/O₂(X) and H=XT. Its T-orbit is precisely K=O²(H).
Since X escapes N_G(L), it moves V_H. The latter lies in Ω₁(Z(O₂(H)));
A.4.8 therefore detects a nontrivial intrinsic module for X. Faithfulness
ascends to an actual maximal local overcomponent Y by the proved 1.2.9
chain theorem. All component and core normality remains relative to H.

The final rank application uses a T-invariant original component with an
actual A₅ quotient identification. It transports the intrinsic quotient
through X=K and discharges the existing residual-identification consumer.
The T-invariance and A₅ model exclusions, including the nonquasisimple
Y branch, remain source obligations of qt-d-12213-hstar-natural. This
module proves the opening of 12.2.7, not its full alternatives (2–3).

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798; E.2.2, pp.215–216;
A.4.8–10, pp.59–60; and 1.2.9, p.507.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

/-- An actual source component in H, retaining its original Sylow generation,
quasisimple quotient, residual orbit and movement on V_H. -/
structure HStarGeneratingComponent (T : Sylow 2 G) (L H X : Subgroup G) : Prop where
  component : X ∈ Chapter1.cComponentsIn H
  quasisimple : IsQuasisimple (X ⧸ pCore 2 X)
  generates : X ⊔ (T : Subgroup G) = H
  residual : (pResidual 2 H).map H.subtype = componentOrbit X (T : Subgroup G)
  escapes : ¬ X ≤ normalizer (L : Set G)
  moves : ⁅hstarOmegaModule T H, X⁆ ≠ ⊥

/-- E.2.2 supplies a genuine original component; the omega-centralizer guard
forces it to move the source module. No model identification is assumed. -/
theorem chosen_hstar_exists_generating_component_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X : Subgroup G, HStarGeneratingComponent T L H X := by
  let S := T.subtype hH.1.1.2
  obtain ⟨X,hX,hq,hgen,_⟩ := ChapterE.Structure.source_original_component
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) S
    (chosen_hstar_minimalParabolic_at h D structural hTI hH) hs
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
      (chosen_omega_centralizer_le_of_noEscape_at h D structural hnone)

/-- The generating component belongs to the exact local family and embeds
in an actual maximal local component. Faithfulness is not assumed here. -/
theorem HStarGeneratingComponent.exists_maximal_overcomponent
    {X : Subgroup G} (C : HStarGeneratingComponent T L H X)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    X ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ Y ∈ Chapter1.LStar G (T : Subgroup G), X ≤ Y := by
  have hx := (Chapter1.lemma_1_2_6 T hH.1.1).1 C.component
  exact ⟨hx.2, Chapter1.exists_mem_LStar_ge hx.2⟩

omit [Finite G] in
/-- Once the source chain proves T-invariance, the original component is
literally O²(H), rather than merely an isomorphic section. -/
theorem HStarGeneratingComponent.eq_residual_of_normalized
    {X : Subgroup G} (C : HStarGeneratingComponent T L H X)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    X = (pResidual 2 H).map H.subtype := by
  rw [C.residual]
  exact le_antisymm (le_componentOrbit X (T : Subgroup G))
    (iSup_conjugates_le_of_le_normalizer X (T : Subgroup G) X le_rfl hn)

/-- Actual rank consumer after the T-normalization and A₅ model branches
of 12.2.7 have been proved. The quotient retains the intrinsic O₂ of X. -/
theorem chosen_hstar_quotient_rank_of_generating_five_component_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {X : Subgroup G} (C : HStarGeneratingComponent T L H X)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hf : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  apply chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH
  intro _
  let e : pResidual 2 H ≃* X :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (C.eq_residual_of_normalized hn).symm)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans hf.some⟩

/-- Movement of V_H detects faithfulness of the actual original component.
The comparison uses the two-core of H as a signalizer, retaining the
subnormal inclusion X≤H and the intrinsic core of X. -/
theorem HStarGeneratingComponent.faithful_at
    {X : Subgroup G} (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    X ∈ MainForward.faithfulLocalComponents T := by
  have hx := (C.exists_maximal_overcomponent hH).1
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (h.simpleQTKE.evenCharacteristic T)).mpr
  refine ⟨hx, ?_⟩
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hx
  have hn : X ≤ normalizer (H.pCoreIn 2 : Set G) := C.component.1.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hsig : ChapterA.Section04.IsTwoSignalizer X H (H.pCoreIn 2) :=
    (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr
      ⟨pCoreIn_le _ _, isPGroup_pCoreIn _ _, hn⟩
  have hcomm := ChapterA.Section04.signalizer_commutator_le_pCore X H (H.pCoreIn 2)
    C.component.1 C.component.2.subnormal hp hsig
  have hle := ChapterA.Section04.signalizerModule_le_intrinsicModule X (H.pCoreIn 2) hp hn
    (pCoreAmbient_mono_of_isSubnormalIn X H 2 C.component.1 C.component.2.subnormal) hcomm
  have hw : hstarOmegaModule T H ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2) := by
    let := chosen_hstar_omega_elementary h hH
    intro w hw
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨chosen_hstar_omega_le_core h hH hw,
      elemPow_eq_one_of_isElementaryAbelian w hw,
      (le_centralizer_iff.mp (chosen_hstar_core_centralizes_omega h hH)) hw⟩
  intro he
  apply C.moves
  apply eq_bot_iff.mpr
  have hc := (commutator_mono (show X ≤ X from le_rfl) hw).trans
    ((ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter X (H.pCoreIn 2)).symm.le.trans hle)
  rw [commutator_comm] at hc
  exact hc.trans_eq he

/-- The source proof now has an actual faithful maximal local overcomponent.
Its quasisimple/model case analysis remains separate. -/
theorem HStarGeneratingComponent.exists_faithful_maximal_overcomponent
    {X : Subgroup G} (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ Y : Subgroup G, X ≤ Y ∧ Y ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ChapterA.Section04.IsFaithfulSignalizerType Y := by
  obtain ⟨Y,hY,hXY⟩ := (C.exists_maximal_overcomponent hH).2
  have hf := Chapter1.Section02.Adequate.faithful_local_overgroup T
    (h.simpleQTKE.evenCharacteristic T) (C.faithful_at h hH) hY.1 hXY
  exact ⟨Y,hXY,hY,((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T Y).mp hf).2⟩

/-- Original 12.2.7 nonsolvable opening, including the faithful overcomponent
which the subsequent seven-row and embedding analysis must classify. -/
theorem chosen_hstar_exists_faithful_overcomponent_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧ X ≤ Y ∧
      Y ∈ Chapter1.LStar G (T : Subgroup G) ∧ ChapterA.Section04.IsFaithfulSignalizerType Y := by
  obtain ⟨X,C⟩ := chosen_hstar_exists_generating_component_at h D structural hnone hTI hH hs
  obtain ⟨Y,hXY,hY,hf⟩ := C.exists_faithful_maximal_overcomponent h hH
  exact ⟨X,Y,C,hXY,hY,hf⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
