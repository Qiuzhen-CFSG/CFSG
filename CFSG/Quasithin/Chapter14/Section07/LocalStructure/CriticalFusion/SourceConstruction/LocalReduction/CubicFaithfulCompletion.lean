module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicNaturalModule
/-!
# The full cubic quotient and its literal overlap

In the nonsolvable cubic branch, the component image in D/O₂(D) is again
PSL₃(2). The Goldschmidt reduction and the nonnormalizing cubic residuals
force it to be the entire quotient. Comparing this with D/C_D(W) proves
C_D(W) = O₂(D), preserving the original quotient kernel.

The natural point span W and the original seed V both have order eight.
They contain V₂ and are distinct, since equality would make Y normalize V.
Thus V ∩ W = V₂. Their common normalizers give LT ∩ D = P, with exactly
the original plane parabolic, as required by the subsequent coset geometry.

Source: Aschbacher–Smith, proof of 14.5.8, printed pp.1014–1015,
refs/quasithin.pdf. The ambient exclusion is assembled in the next module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The literal two-core quotient is the linear-three group. -/
theorem cubic_generated_component_core_quotient_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  let q := QuotientGroup.mk' Q
  let qC := QuotientGroup.mk' C
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le.trans inf_le_right
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hcomp : r.comp q = qC := by
    ext x
    rfl
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hJ.subnormal).symm
  let eJ : (J ⧸ pCore 2 J) ≃* J.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))
  obtain ⟨e₀⟩ := cubic_generated_component_linear_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let e := eJ.symm.trans e₀
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := e.isSimpleGroup
  let := hJ.perfect
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hz : center (J.map q) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J.map q)) inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative (J.map q) (center_eq_top_iff.mp hh))
  let : IsQuasisimple (J.map q) := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hj : IsComponent (D ⧸ Q) (J.map q) :=
    ⟨hJ.subnormal.map (QuotientGroup.mk'_surjective Q),inferInstance⟩
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hJn,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective Q)
    ht.quotient_twoCore ht.quotient_twoCore_eq_bot hj
  let : (J.map q).Normal := hJn
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have hnot : ¬ (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype ≤
      normalizer ((pResidual 2 (((F.P L).subgroupOf D).map q)).map
        (((F.P L).subgroupOf D).map q).subtype : Set (D ⧸ Q)) := by
    rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2]
    intro hh
    have hm := (map_mono (f := r) hh).trans (le_normalizer_map r)
    rw [map_map,map_map,hcomp] at hm
    exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout hm
  have htop := goldschmidt_linear_completion ht.quotient_twoCore
    ht.quotient_twoCore_eq_bot (J.map q) e hcases hnot
  exact ⟨topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e)⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_core_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_core_quotient_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The point-span action has exactly the full two-core as kernel. -/
theorem cubic_generated_component_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    centralizer (W.subgroupOf D : Set D) = pCore 2 D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le.trans inf_le_right
  obtain ⟨eQ⟩ := cubic_generated_component_core_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨eC⟩ := cubic_generated_component_action_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨QuotientGroup.mk' Q g,rfl⟩
  have hc : Nat.card (D ⧸ C) = Nat.card (D ⧸ Q) := Nat.card_congr (eC.trans eQ.symm).toEquiv
  have hi := (hr.bijective_of_nat_card_le hc.ge).injective
  apply le_antisymm _ hQC
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change QuotientGroup.mk' C x = r 1
  rw [r.map_one]
  exact (QuotientGroup.eq_one_iff x).mpr hx

/-- The original full point-normality interface. -/
theorem cubic_generated_component_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    centralizer (W.subgroupOf D : Set D) = pCore 2 D := by
  apply cubic_generated_component_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The two rank-three seeds meet in the original plane. -/
theorem cubic_generated_component_seed_intersection_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    V ⊓ W = F.Vi 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  obtain ⟨hW8,hWY,_,_⟩ := cubic_generated_component_span_geometry_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  change Nat.card W = 8 at hW8
  change W = conjugateSpanBy (F.Vi 2) Y at hWY
  have hPW : F.Vi 2 ≤ W := by
    rw [hWY]
    exact le_conjugateSpanBy _ _
  have hle : F.Vi 2 ≤ V ⊓ W := le_inf (F.le_seed 2) hPW
  have h4 : 4 ≤ Nat.card (V ⊓ W : Subgroup G) := by
    simpa only [F.card 2 (by decide), show (2 : ℕ)^2 = 4 from rfl] using card_le_of_le hle
  have hd : Nat.card (V ⊓ W : Subgroup G) ∣ 8 := hW8 ▸ card_dvd_of_le inf_le_right
  have h8 : Nat.card (V ⊓ W : Subgroup G) ≠ 8 := by
    intro hh
    have hIW : V ⊓ W = W := eq_of_le_of_card_ge inf_le_right (by rw [hh,hW8])
    have hWV : W ≤ V := hIW.symm.le.trans inf_le_left
    have hWV' : W = V := eq_of_le_of_card_ge hWV (by rw [hW8,h.seed_card]; rfl)
    have hNV : Y ≤ normalizer (V : Set G) := by
      rw [←hWV']
      exact (le_sup_left.trans le_sup_right : Y ≤ D).trans (le_normalizer_conjugateSpanBy _ _)
    have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S M hM
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
    exact hout (hNV.trans (h.seed_normalizer_le structural hu))
  have hm : Nat.card (V ⊓ W : Subgroup G) ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have heq : Nat.divisors 8 = {1,2,4,8} := by decide
  rw [heq] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hc : Nat.card (V ⊓ W : Subgroup G) = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hc,F.card 2 (by decide)]; rfl)).symm

/-- The original full point-normality interface. -/
theorem cubic_generated_component_seed_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    V ⊓ W = F.Vi 2 := by
  apply cubic_generated_component_seed_intersection_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The common vertex subgroup is precisely the marked plane parabolic. -/
theorem cubic_generated_component_vertex_intersection_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    (L ⊔ (T : Subgroup G)) ⊓ (F.P L ⊔ (Y ⊔ (T : Subgroup G))) = F.P L := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  have hinter := cubic_generated_component_seed_intersection_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hnorm : (L ⊔ (T : Subgroup G)) ⊓ D ≤ normalizer (F.Vi 2 : Set G) := by
    rw [←hinter]
    exact le_normalizer_inf
      (inf_le_left.trans (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural)))
      (inf_le_right.trans (le_normalizer_conjugateSpanBy _ _))
  apply le_antisymm
  · intro x hx
    simp only [InvariantFlag.P,mem_inf,mem_iInf]
    refine ⟨hx.1,?_⟩
    intro i hi
    have hi2 : i = 2 := by omega
    subst i
    exact hnorm hx
  · exact le_inf inf_le_left le_sup_left

/-- The original full point-normality interface. -/
theorem cubic_generated_component_vertex_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    (L ⊔ (T : Subgroup G)) ⊓ (F.P L ⊔ (Y ⊔ (T : Subgroup G))) = F.P L := by
  apply cubic_generated_component_vertex_intersection_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
