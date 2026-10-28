module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SevenNatural
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.IntrinsicSource
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Point-core movement forced by a large component

If the original point core centralizes the flag plane, the point span lies
in its omega-center. The faithful local section shows that every C-component
moves this span. The intrinsic signalizer-module theorem therefore makes
each component faithful, and earlier 14.3.4 gives the actual A₅ or L₃(2)
core quotient. Thus a component with core quotient of order greater than
168 forces movement of the original plane.

The quotient version lifts a C-component through the literal O₂(H), using
its actual intrinsic quotient. Applied to the alternating subgroup of an
S₇ star quotient, it supplies the movement needed by the seven-letter
natural-section exclusion. The guarded consumer uses only earlier results
at the same G,T. General movement in the remaining small-component cases
and the final residual alternatives are not asserted here.

Source: Aschbacher–Smith, 13.3.14(a),(e), 14.3.4(1), 14.7.4(1), and
14.7.37(3), printed pp.891–892,990,1043,1059–1060, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Contrary plane centralization makes every actual point component one
of the two earlier faithful quotient models. -/
theorem component_small_of_plane_centralized_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hc : ⁅F.Vi 2,F.H.pCoreIn 2⁆ = ⊥)
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) := by
  let := h.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  let := IsElementaryAbelian.of_surjective (p := 2)
    (F.tildeMap V hVH) (F.tildeMap_surjective V hVH)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    have hh := F.card 1 (by decide)
    simp [he] at hh
  have htwo : IsTwoLocal F.H := ⟨F.Vi 1,hp,
    T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow),rfl⟩
  have hHe : F.H ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T) htwo (F.invariant 1)
  have hgen : V = conjugateSpanBy (F.Vi 2) (F.Li L 1) :=
    (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).symm
  have hω : F.U ≤ omegaOneCenterAmbient (F.H.pCoreIn 2) :=
    (Chapter13.Section03.Noncentrality.reduction_a (F.Vi 2) V (F.Li L 1) F.H
      ((F.le_seed 2).trans hVH) ((F.Li_le L 1).trans inf_le_right) hgen hHe hc).2
  have hωmap : (omegaOneCenterAmbient (pCore 2 F.H)).map F.H.subtype =
      omegaOneCenterAmbient (F.H.pCoreIn 2) :=
    (omegaOneCenterAmbient_map_injective F.H.subtype F.H.subtype_injective _).symm
  have hUi : F.U.subgroupOf F.H ≤ omegaOneCenterAmbient (pCore 2 F.H) := by
    intro a ha
    have hh := hω ha
    rw [←hωmap] at hh
    obtain ⟨b,hb,he⟩ := hh
    exact (F.H.subtype_injective he) ▸ hb
  have hH := h.point_mem_Hz_at F previous
  have hk := F.localKernel_eq_pCore h.source.simpleQTKE L (normalizer (L : Set G)) F.H
    (by decide) h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl (h.maximal_unique_at structural).2
    ((Subgroup.centralizer_le_normalizer _).trans (h.seed_normalizer_le_at structural)) h.centralizer_L hH
  have hm : ⁅F.U.subgroupOf F.H,C⁆ ≠ ⊥ := by
    intro hz
    have hCU : C ≤ centralizer (F.U.subgroupOf F.H : Set F.H) := by
      rw [commutator_comm] at hz
      exact commutator_eq_bot_iff_le_centralizer.mp hz
    have hCQ : C ≤ pCore 2 F.H := by
      rw [←hk]
      intro c hc
      apply (F.mem_localTildeAction_ker_iff F.H le_rfl c).mpr
      intro a ha
      have he := mem_centralizer_iff.mp (hCU hc) (⟨a,F.U_le_H ha⟩ : F.H) ha
      have heG : a * (c : G) = (c : G) * a := congrArg Subtype.val he
      simp [commutatorElement_def,←heG,mul_assoc]
    let : Group.IsNilpotent C := (pCore_isPGroup.to_le hCQ).isNilpotent
    exact hC.not_isSolvable inferInstance
  obtain ⟨hCL,hCf⟩ := Chapter13.Section03.Noncentrality.source_component_faithful_local
    T F.H (F.invariant 1) (Chapter1.mem_H_of_isTwoLocal htwo) hHe C _ hC hUi hm
  let e := C.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rcases (faithful _ hCL hCf).1 with ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨q.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr ⟨q.trans a⟩


/-- A component larger than both earlier faithful models forces the original
point core to move the original flag plane. -/
theorem plane_moved_of_large_component_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (hc : 168 < Nat.card (C ⧸ pCore 2 C)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  intro hz
  rcases component_small_of_plane_centralized_at h structural previous faithful hz C hC with
    he | he
  · obtain ⟨e⟩ := he
    have he := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup,Nat.card_fin] at he
    norm_num at he
    omega
  · obtain ⟨e⟩ := he
    have he := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
    omega

/-- The quotient version lifts an actual component through O₂(H), retaining
the equality between its intrinsic core quotient and its prescribed image. -/
theorem plane_moved_of_large_star_component_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (B : Subgroup (HStar F.H)) (hB : B.IsCComponent)
    (hc : 168 < Nat.card B) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  let : Group.IsNilpotent (pCore 2 F.H) := pCore_isPGroup.isNilpotent
  obtain ⟨C,hC,himage⟩ := hB.exists_map_quotient_eq (pCore 2 F.H)
  apply plane_moved_of_large_component_at h structural previous faithful C hC
  rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hC).toEquiv,himage]
  exact hc

/-- A symmetric seven quotient supplies its actual alternating component,
so the general movement premise is discharged in this model. -/
theorem plane_moved_of_symmetric_seven_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 7)) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  let A := alternatingGroup (Fin 7)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hA : A.IsCComponent := isCComponent_of_isSimpleGroup_of_isPerfect
    (inferInstance : A.Normal).isSubnormal
  apply plane_moved_of_large_star_component_at h structural previous faithful
    (A.map e.symm.toMonoidHom) (hA.map_equiv e.symm)
  rw [←Nat.card_congr (A.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv]
  change 168 < Nat.card (alternatingGroup (Fin 7))
  rw [nat_card_alternatingGroup,Nat.card_fin]
  norm_num

/-- The actual seven-letter natural section at the original point normalizer
is impossible, without a point-normality or movement hypothesis. -/
theorem original_seven_natural_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 7))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (BinaryPermutation.SevenParabolic.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  local_seven_natural_impossible_at h structural
    (plane_moved_of_symmetric_seven_at h structural previous faithful e) F.H
    (h.point_mem_Hz_at F previous) e c

/-- The same source exclusion at the literal many-overgroup consumer. -/
theorem original_seven_natural_impossible_of_many_source_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : HStar F.H ≃* Equiv.Perm (Fin 7))
    (c : BinaryConjugationSection F.H F.U (F.Vi 1)
      (BinaryPermutation.SevenParabolic.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F.H))))) : False :=
  original_seven_natural_impossible_at h (structural hmany) (previous hmany) faithful e c

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
