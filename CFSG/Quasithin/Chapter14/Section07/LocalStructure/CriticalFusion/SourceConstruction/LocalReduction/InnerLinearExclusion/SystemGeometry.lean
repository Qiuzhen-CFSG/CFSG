module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.MiddleSource
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Parabolics.Quotient

/-!
# The actual A₃ and C₃ systems of 14.7.11

The natural action identifies LT/O₂(LT) with L₃(2) and its two literal
flag parabolics. Restrict I, H₂P and LT to E = ⟨LT,I⟩, carrying each
intrinsic quotient and parabolic through the canonical subgroupOf maps.
Their chamber is the original T. Uniqueness of the maximal two-local
overgroup of LT and escape of I force O₂(E)=1, hence the chamber is
core-free. The original fixed point supplies the C₃ nondegeneracy clause.

The final theorem constructs all D1–D5 from the small-quotient geometry;
no system, generation or parabolic hypothesis is supplied. The earlier
point-core movement and universal earlier cubic-actor inputs remain
explicit. The C₃ contradiction and guarded transport remain subsequent.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.11 and I.5,
printed pp.1045–1046 and 418–419.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def coreRestriction {A B : Subgroup G} (hAB : A ≤ B) :
    HStar (A.subgroupOf B) ≃* HStar A :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hAB) (pCore_map_iso 2 (subgroupOfEquivOfLe hAB))

/-- The full natural action identifies the literal third vertex quotient. -/
def seedQuotientEquiv_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    HStar (L ⊔ (T : Subgroup G)) ≃* Matrix.PSL3Two.PSL := by
  let := h.chosen.elementary
  let a : MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun f => { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
      invFun := fun f => MulEquiv.toAdditive.symm f.toAddEquiv
      left_inv := by intro f; ext; rfl
      right_inv := by intro f; ext; rfl
      map_mul' := by intro f g; ext; rfl }
  let e := (a.trans (BinaryLinear.SmallParabolicLevi.linearGroupCongr h.naturalMarking.coordinates)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
  let f := e.toMonoidHom.comp (F.binarySeedAction L h.chosen.normalizes)
  have hf : Function.Surjective f := e.surjective.comp (h.full_LT_action_at structural)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact F.binarySeedAction_ker_isPGroup L h.chosen.normalizes (h.centralizer_LT_at structural)
  exact (f.pCoreQuotientEquiv hf hk).trans
    ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.pCore_two_PSL_eq_bot).trans QuotientGroup.quotientBot)

set_option backward.isDefEq.respectTransparency false in
/-- The point stabilizer in LT is the original residual/Sylow product. -/
theorem seed_point_intersection_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (L ⊔ (T : Subgroup G)) ⊓ F.H = F.Li L 1 ⊔ (T : Subgroup G) := by
  let A := (L ⊔ (T : Subgroup G)) ⊓ F.H
  have hTA : (T : Subgroup G) ≤ A := le_inf le_sup_right (F.invariant 1)
  have hLT : (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = L :=
    embedded_pResidual_join_pGroup L _ ((pResidual_eq_top_iff 2 L).mp h.residual)
      T.isPGroup' (h.sylow_normalizes_at structural)
  have hN : L ⊓ F.H ≤ A := inf_le_inf_right _ le_sup_left
  have hR : (pResidual 2 A).map A.subtype ≤ L ⊓ F.H :=
    le_inf ((embedded_pResidual_mono 2 (show A ≤ L ⊔ (T : Subgroup G) from inf_le_left)).trans_eq hLT)
      ((map_subtype_le _).trans inf_le_right)
  have he := embedded_pResidual_eq_of_le_of_residual_le 2 hN hR
  have he' : (pResidual 2 A).map A.subtype = F.Li L 1 := by
    simpa [InvariantFlag.Li, InvariantFlag.H] using he.symm
  have hh := congrArg (map A.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTA))
  rw [Subgroup.map_sup,he',Sylow.coe_subtype,map_subgroupOf_eq_of_le hTA,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh.symm

private theorem not_two_of_symmetricThree {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 X := by
  intro hp
  have hs := (hp.to_quotient (pCore 2 X)).of_equiv e
  obtain ⟨n,hn⟩ := hs.exists_card_eq
  have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at hd
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

set_option backward.isDefEq.respectTransparency false in
/-- Both actual natural flag parabolics have the complete rank-two lattice. -/
theorem seed_parabolics_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    RankTwoParabolics (L ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
      ((F.P L).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let A := L ⊔ (T : Subgroup G)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hBA : B ≤ A := sup_le ((F.Li_le L 1).trans (inf_le_left.trans le_sup_left)) le_sup_right
  have hPA : F.P L ≤ A := inf_le_left
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hi : B ⊓ F.P L = (T : Subgroup G) := by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans hBH)).trans_eq (plane_parabolic_inf_point_at h structural)
    · exact le_inf le_sup_right (F.binary_sylow_le_P L)
  let eB := (coreRestriction hBA).trans (pointQuotientEquiv_at h structural)
  let := h.chosen.elementary
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf := F.binaryPermutationAction_surjective (by decide) L h.chosen.normalizes (h.full_LT_action_at structural)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action_at structural) (h.centralizer_LT_at structural))
  let eP := (coreRestriction hPA).trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf))
  have hnotB := not_two_of_symmetricThree eB
  have hnotP := not_two_of_symmetricThree eP
  have hiA : B.subgroupOf A ⊓ (F.P L).subgroupOf A = (T : Subgroup G).subgroupOf A := by
    simpa only [subgroupOf,←comap_inf] using congrArg (fun Z : Subgroup G => Z.subgroupOf A) hi
  have hproper (X Z : Subgroup A) (hnZ : ¬ IsPGroup 2 Z)
      (hi : X ⊓ Z = (T : Subgroup G).subgroupOf A) : X ≠ ⊤ := by
    intro hx
    rw [hx,top_inf_eq] at hi
    exact hnZ (hi.symm ▸ T.isPGroup'.comap_subtype)
  exact RankTwoParabolics.of_psl_two_quotient (pCore 2 A) pCore_isPGroup
    (seedQuotientEquiv_at (F := F) h structural) (T.subtype le_sup_right)
    _ _ (hproper _ _ hnotP hiA)
    (hproper _ _ hnotB ((inf_comm _ _).trans hiA)) hnotB hnotP hiA

/-- The literal three source vertices, restricted only to their generated group. -/
private def systemFamily (I H₂ : Subgroup G) : Fin 3 → Subgroup ((L ⊔ (T : Subgroup G)) ⊔ I : Subgroup G) :=
  fun i => (![I,H₂ ⊔ F.P L,L ⊔ (T : Subgroup G)] i).subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ I)

private theorem point_center_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) (I : Subgroup G) (hTI : (T : Subgroup G) ≤ I) (hIH : I ≤ F.H) :
    center I ≠ ⊥ := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hz1,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hz : z ∈ F.Vi 1 := hpoint.symm ▸ mem_zpowers z
  have hzI : z ∈ I := hTI (h.chosen.le_sylow (F.le_seed 1 hz))
  have hn : I ≤ centralizer (F.Vi 1 : Set G) :=
    hIH.trans (normalizer_le_centralizer_of_card_two _ hc)
  have hzC : (⟨z,hzI⟩ : I) ∈ center I := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hn x.property) z hz).symm
  intro he
  rw [he,mem_bot] at hzC
  exact hz1 (congrArg Subtype.val hzC)

/-- D1--D5 for the actual generated group; all parabolic data are constructed
by the original small-quotient geometry. -/
private theorem system_of_middle_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I H₂ : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (h₂I : H₂ ≤ I) (hT₂ : (T : Subgroup G) ≤ H₂)
    (hpoint : RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I) (H₂.subgroupOf I))
    (hJI : (H₂ ⊔ F.P L) ⊓ I = H₂)
    (hJA : (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L)
    (hch : (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G))
    (he : Nonempty (HStar (H₂ ⊔ F.P L) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hline : RankTwoParabolics (H₂ ⊔ F.P L : Subgroup G)
      ((T : Subgroup G).subgroupOf (H₂ ⊔ F.P L))
      (H₂.subgroupOf (H₂ ⊔ F.P L)) ((F.P L).subgroupOf (H₂ ⊔ F.P L)))
    (D : Diagram)
    (h3 : D = .A3 → Nonempty (HStar I ≃* Matrix.PSL3Two.PSL))
    (h6 : D = .C3 → Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ S : DSystem D ((L ⊔ (T : Subgroup G)) ⊔ I : Subgroup G),
      S.family = systemFamily (L := L) (F := F) I H₂ := by
  let A := L ⊔ (T : Subgroup G)
  let J := H₂ ⊔ F.P L
  let E := A ⊔ I
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hIE : I ≤ E := le_sup_right
  have hAE : A ≤ E := le_sup_left
  have hJE : J ≤ E := sup_le (h₂I.trans hIE) (inf_le_left.trans hAE)
  have hTI := F.sylow_le_of_mem_Hz hI
  have hTJ : (T : Subgroup G) ≤ J := hT₂.trans le_sup_left
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) hTI
  have hIA : I ⊓ A = B := by
    apply le_antisymm
    · exact (le_inf inf_le_right (inf_le_left.trans hI.2.1)).trans_eq (seed_point_intersection_at h structural)
    · exact le_inf hBI (sup_le ((F.Li_le L 1).trans (inf_le_left.trans le_sup_left)) le_sup_right)
  have hpar0 : RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
      (J.subgroupOf I) (A.subgroupOf I) := by
    have hj : J.subgroupOf I = H₂.subgroupOf I := by
      rw [←inf_subgroupOf_right J I,hJI]
    have ha : A.subgroupOf I = B.subgroupOf I := by
      rw [←inf_subgroupOf_left A I,hIA]
    rw [hj,ha]
    exact hpoint.symm
  have hpar1 : RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
      (I.subgroupOf J) (A.subgroupOf J) := by
    have hi : I.subgroupOf J = H₂.subgroupOf J := by
      rw [←inf_subgroupOf_left I J,hJI]
    have ha : A.subgroupOf J = (F.P L).subgroupOf J := by
      rw [←inf_subgroupOf_left A J,hJA]
    rw [hi,ha]
    exact hline
  have hpar2 : RankTwoParabolics A ((T : Subgroup G).subgroupOf A)
      (I.subgroupOf A) (J.subgroupOf A) := by
    have hi : I.subgroupOf A = B.subgroupOf A := by
      rw [←inf_subgroupOf_right I A,hIA]
    have hj : J.subgroupOf A = (F.P L).subgroupOf A := by
      rw [←inf_subgroupOf_right J A,hJA]
    rw [hi,hj]
    exact seed_parabolics_at h structural
  let family := systemFamily (L := L) (F := F) I H₂
  have hchE : chamberSubgroup family = (T : Subgroup G).subgroupOf E := by
    ext x
    simp only [chamberSubgroup,mem_iInf,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    change ((x : G) ∈ I ∧ (x : G) ∈ J ∧ (x : G) ∈ A) ↔ (x : G) ∈ (T : Subgroup G)
    exact ⟨fun hx => hch.le ⟨⟨hx.2.1,hx.1⟩,hx.2.2⟩,fun hx =>
      let hh := hch.ge hx
      ⟨hh.1.2,hh.1.1,hh.2⟩⟩
  have hs (X : Subgroup G) (hXE : X ≤ E) (hTX : (T : Subgroup G) ≤ X) :
      ∃ P : Sylow 2 (X.subgroupOf E),
        (P : Subgroup (X.subgroupOf E)) = ((T : Subgroup G).subgroupOf E).subgroupOf (X.subgroupOf E) := by
    let e := subgroupOfEquivOfLe hXE
    refine ⟨(T.subtype hTX).comapOfInjective e.toMonoidHom e.injective ?_,rfl⟩
    intro x _
    obtain ⟨y,hy⟩ := e.surjective x
    exact ⟨y,hy⟩
  have hcore : pCore 2 E = ⊥ := by
    apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup A I (normalizer (L : Set G))
    · intro M hM hAM
      have hh : M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ A ≤ N} := ⟨hM,hAM⟩
      rw [(h.maximal_unique_at structural).2] at hh
      exact Set.mem_singleton_iff.mp hh
    · exact hI.2.2
  have hcenter : center (I.subgroupOf E) ≠ ⊥ := by
    have hc : center I ≠ ⊥ := point_center_ne_bot h I hTI hI.2.1
    intro hb
    have hh := Nat.card_congr (centerCongr (subgroupOfEquivOfLe hIE)).toEquiv
    rw [hb,card_bot] at hh
    exact hc (card_eq_one.mp hh.symm)
  refine ⟨{
    family := family
    finite_vertex := fun _ => inferInstance
    point_A3 := fun hd => ⟨(coreRestriction hIE).trans (h3 hd).some⟩
    point_C3 := fun hd => (h6 hd).imp
      (fun he => ⟨(coreRestriction hIE).trans he.some⟩)
      (fun he => ⟨(coreRestriction hIE).trans he.some⟩)
    line_quotient := ⟨(coreRestriction hJE).trans he.some⟩
    plane_quotient := ⟨(coreRestriction hAE).trans (seedQuotientEquiv_at (F := F) h structural)⟩
    sylow := ?_
    point_parabolics := ?_
    line_parabolics := ?_
    plane_parabolics := ?_
    generate := ?_
    core_free := ?_
    nondegenerate := fun _ => Or.inl hcenter },rfl⟩
  · intro i
    rw [hchE]
    fin_cases i
    · exact hs I hIE hTI
    · exact hs J hJE hTJ
    · exact hs A hAE le_sup_right
  · rw [hchE]
    exact CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics.rankTwo_subgroupOf I J A T E hIE hpar0
  · rw [hchE]
    exact CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics.rankTwo_subgroupOf J I A T E hJE hpar1
  · rw [hchE]
    exact CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics.rankTwo_subgroupOf A I J T E hAE hpar2
  · apply top_unique
    have hg : A.subgroupOf E ⊔ I.subgroupOf E = ⊤ := by
      rw [←subgroupOf_sup hAE hIE,subgroupOf_self]
    rw [←hg]
    exact sup_le (le_iSup family 2) (le_iSup family 0)
  · rw [hchE]
    apply le_bot_iff.mp
    rw [←hcore]
    exact le_sSup ⟨inferInstance,T.isPGroup'.comap_subtype.to_le (normalCore_le _)⟩

/-- Construct the actual A₃ or C₃ system, including the source chamber and
its core-freeness, on the subgroup generated by I and LT. -/
theorem small_local_source_system
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (D : Diagram)
    (h3 : D = .A3 → Nonempty (HStar I ≃* Matrix.PSL3Two.PSL))
    (h6 : D = .C3 → Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ H₂ : Subgroup G, H₂ = I ⊓ F.Gi 2 ∧
      ∃ S : DSystem D ((L ⊔ (T : Subgroup G)) ⊔ I : Subgroup G),
        S.family = fun i => (![I,H₂ ⊔ F.P L,L ⊔ (T : Subgroup G)] i).subgroupOf
          ((L ⊔ (T : Subgroup G)) ⊔ I) := by
  have hm : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6)) := by
    cases D
    · exact Or.inl (h3 rfl)
    · exact Or.inr (h6 rfl)
  obtain ⟨H₂,Y,h₂eq,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,hJI,hJA,hch,hquot,hline⟩ :=
    small_local_middle_quotient h hab structural previous faithful hmovement I hI hm
  have h₂I : H₂ ≤ I := h₂eq.le.trans inf_le_left
  have hT₂ : (T : Subgroup G) ≤ H₂ := hYT ▸ le_sup_right
  obtain ⟨S,hS⟩ := system_of_middle_geometry h (structural G T) I H₂ hI h₂I hT₂
    hR hJI hJA hch hquot hline D h3 h6
  exact ⟨H₂,h₂eq,S,hS⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
