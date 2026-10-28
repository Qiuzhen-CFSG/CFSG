module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicMovingEndgame
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic
public import Theory.GroupTheory.PGroup.ElementaryNineCubicLifts
public import Theory.GroupTheory.PResidual.AbelianQuotient

/-!
# Solvable containment for the actual two-node product quotient

The literal S₃ × S₃ quotient has elementary two-residual of order nine.
Its two-perfect lift normalizes the point residual. The two invariant cubic
lifts either lie in N_G(L), or fix the original plane by 14.5.3. In the latter
case their normalization of L₁ makes them preserve V = ⟨V₂ᴸ¹⟩, giving the
same containment. They generate the residual, which supplements T.
This proves precisely the solvable row of 14.7.29 consumed by the inner
linear argument, using only the same G,T earlier inputs.
Source: Aschbacher–Smith 14.5.3,20 and 14.7.29,51, pp.1013,1019,1055,1065.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem point_plane_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hn : A ≤ normalizer (F.Li L 1 : Set G))
    (hc : A ≤ normalizer (F.Vi 2 : Set G)) :
    A ≤ normalizer (L : Set G) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  apply le_trans _ (h.seed_normalizer_le_at structural)
  rw [←F.seed_eq_plane_span L (by decide) h.chosen.normalizes
    (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
  exact normalizes_conjugateSpanBy _ _ A hc hn

private theorem local_point_sylow_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G))
    (hYT : Y ≤ normalizer (T : Set G)) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let J := B ⊔ Y
  have hBJ : B ≤ J := le_sup_left
  have hJH : J ≤ F.H := sup_le
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)) hYH
  have hc : Nat.card (F.Vi 1) = 2 := F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hc))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBJ))) hJH
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := le_bot_iff.mp (he ▸ hpoint)
    rw [hz,card_bot] at hc
    omega
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBJ (mem_sup_left ha))
      (fun ha => hBJ (mem_sup_right ha))⟩,hJH,fun hh => hout (le_sup_right.trans hh)⟩
  have hYB : Y ≤ normalizer (B : Set G) :=
    (le_inf hYL hYT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    (sup_le B.le_normalizer hYB).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  exact WholeResidualAssembly.point_core_not_le_local_core_at h hab structural J hJ
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B)
      ((pCoreIn_le 2 B).trans hBJ) hJR)

/-- The original cubic containment when the actor normalizes the original L₁.
Plane fixation is supplied by the proved moving-plane contradiction. -/
theorem point_normalized_cubic_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  have he : Nonempty (HStar (Y ⊔ (T : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    apply cubic_sylow_join_symmetricThree T Y hYT hc
    intro hm
    have hcore : Y.pCoreIn 2 ≤ (T : Subgroup G) :=
      (isPGroup_pCoreIn 2 Y).le_sylow_of_normalized T
        (hYT.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
    exact hout (local_point_sylow_normalizer_le h hab structural Y hYH hYL
      (le_normalizer_iff_commutator_le_right.mpr (hm.trans hcore)))
  have hf := (original_cubic_actor_contained_or_plane_fixed h hab structural previous
    faithful Y hYH hYp hYT he).resolve_left hout
  exact hout (point_plane_normalizer_le h structural Y hYL
    ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hf)).trans
      (Subgroup.centralizer_le_normalizer _)))

private theorem pair_residual_elementary {X : Type*} [Group X] [Finite X]
    (e : X ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    IsElementaryAbelian 3 (pResidual 2 X) ∧ Nat.card (pResidual 2 X) = 9 := by
  let a := (pResidual 2 X).equivMapOfInjective e.toMonoidHom e.injective
  let b := MulEquiv.subgroupCongr ((map_pResidual 2 e).trans SymmetricThreeProductResidual.residual_eq)
  let c := (a.trans b).trans (Subgroup.prodEquiv _ _)
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  let : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hc
  have hp (x : alternatingGroup (Fin 3)) : x ^ 3 = 1 := by
    simpa only [hc] using (pow_card_eq_one' (x := x))
  let : IsElementaryAbelian 3
      (alternatingGroup (Fin 3) × alternatingGroup (Fin 3)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Prod.ext (hp x.1) (hp x.2)) }
  refine ⟨IsElementaryAbelian.of_injective c.toMonoidHom c.injective,?_⟩
  rw [Nat.card_congr c.toEquiv,Nat.card_prod,hc]

/-- The literal S₃ × S₃ local quotient is excluded, without a general
solvable-local callback. This is the exact solvable row of the inner proof. -/
theorem local_pair_quotient_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (e : HStar J ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) : False := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let R := pResidual 2 J
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let A := (F.Li L 1).subgroupOf J
  have hBI : B ≤ J := sup_le (F.Li_one_le_of_mem_Hz hJ) (F.sylow_le_of_mem_Hz hJ)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hAr : (pResidual 2 (B.subgroupOf J)).map (B.subgroupOf J).subtype = A := by
    apply map_injective J.subtype_injective
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBI,residual_group_at h structural,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ)]
  let : A.Normal := hAr ▸ residual_normal_of_symmetricThreePair
    (e.toMonoidHom.comp q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (by rw [MonoidHom.ker_comp_of_injective _ _ e.injective]; exact hk) S
    (B.subgroupOf J) (fun _ hx => mem_sup_right hx)
  have hAp : IsPPerfect 2 A := by
    rw [←hAr]
    exact isPPerfect_embedded_pResidual 2 _
  have hAR : A ≤ R := le_pResidual_of_isPPerfect A hAp
  let c := (coreQuotientEquivImage 2 A).symm
  let a := subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)
  have hC : Nat.card (A.map q) = 3 := by
    rw [Nat.card_congr c.toEquiv,
      Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hm : R.map q = pResidual 2 (HStar J) := map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)
  obtain ⟨hE,hcard⟩ := pair_residual_elementary e
  let : IsElementaryAbelian 3 (R.map q) := hm ▸ hE
  have hRcard : Nat.card (R.map q) = 9 := hm ▸ hcard
  obtain ⟨X,Y,hXY,⟨hXp,hXT,_,_,hXc⟩,⟨hYp,hYT,_,hYc⟩⟩ :=
    exists_cubic_lifts_of_normal_elementary_nine q (QuotientGroup.mk'_surjective _) hk
      R (isPPerfect_pResidual 2) hRcard S S.isPGroup' (A.map q) (map_mono hAR) hC
      le_normalizer_of_normal
  have hJN : J ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (F.Li_one_le_of_mem_Hz hJ)).mp inferInstance
  have hcontain (X : Subgroup J) (hp : IsPPerfect 2 X)
      (hXT : (S : Subgroup J) ≤ normalizer (X : Set J))
      (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
      X.map J.subtype ≤ normalizer (L : Set G) := by
    let eX := X.equivMapOfInjective J.subtype J.subtype_injective
    have hn : (T : Subgroup G) ≤ normalizer (X.map J.subtype : Set G) := by
      have hh := (map_mono hXT).trans (le_normalizer_map J.subtype)
      rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)] at hh
    have hcx : Nat.card ((X.map J.subtype) ⧸ pCore 2 (X.map J.subtype)) = 3 := by
      rw [←Nat.card_congr (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)).toEquiv]
      exact hc
    exact point_normalized_cubic_containment h hab structural previous faithful
      (X.map J.subtype) ((map_subtype_le X).trans hJ.2.1)
      ((map_subtype_le X).trans hJN) (hp.of_surjective eX.toMonoidHom eX.surjective) hn hcx
  have hRM : R.map J.subtype ≤ normalizer (L : Set G) := by
    rw [←hXY,Subgroup.map_sup]
    exact sup_le (hcontain X hXp hXT hXc) (hcontain Y hYp hYT hYc)
  have hgen := congrArg (map J.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  exact hJ.2.2 (hgen ▸ sup_le hRM (h.sylow_normalizes_at structural))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
