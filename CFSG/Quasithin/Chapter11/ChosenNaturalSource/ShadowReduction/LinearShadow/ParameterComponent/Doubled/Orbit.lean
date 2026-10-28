module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Generation
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Sylow

/-!
# The doubled actor in the original omega-orbit quotient

E.3.6 is applied to V_M, not the old seed V. The resulting actor in the
literal H/C_H(V_H) has order at least 2^(2n). E.3.40 excludes its outer
placement, and the actual rank-one Sylow order identifies it with a Sylow
of the residual image. Matrix coordinates retain the original residual
projection and use a field of order 2^(2n). No parameter equality k=n or
later natural-quotient marking is used.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
The doubled weak-closure escape and s-value are separate geometric inputs.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- An active conjugate of the full doubled module is selected on the same VH. -/
theorem exists_active_conjugate (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2) :
    ∃ g : G, (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T ∧
      ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
        centralizer (omegaClosure T H : Set G) := by
  by_contra hn
  push Not at hn
  apply hw
  rw [← weakClosureZero_eq_indexed]
  apply sSup_le
  rintro A ⟨g,rfl,hg⟩
  apply (le_inf hg ?_).trans (sylow_inf_orbit_centralizer_le_core h
    (weakClosure_not_le_core_of_counterexample h p hc))
  simpa only [omegaClosure_eq_parameterOrbit] using hn g hg

/-- Both matrix identifications commute with the literal projection from K.
This discharges the field and group-marking part of the natural coordinates. -/
theorem compatible_matrix_equivs
    (s : Hypothesis1131At D S U₁ H)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree))) :
    ∃ (e : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F)
      (eStar : residualStar T H ≃* Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ k : outsideResidual H,
        eStar ⟨starProjection T H (inclusion (outsideResidual_le H) k),
          mem_map_of_mem (starProjection T H) k.property⟩ =
        e (QuotientGroup.mk' _ k) := by
  obtain ⟨E,hE,hfin,hcard,⟨j⟩⟩ := hmodel
  let := hE
  let := hfin
  have hfour : 4 ≤ Nat.card E := by
    rw [hcard]
    calc
      4 = 2 ^ 2 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by have := S.nonbinary; omega)
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (outsideResidual H ⧸ pCore 2 (outsideResidual H)) := j.isSimpleGroup
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  let f : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hF.symm)
  let e : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃* SL(2,F) :=
    (j.trans (Atlas.fieldEquivPSL 2 f)).trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let d := residualStarEquiv T H s.outside.1.1.2 s.moves_omega_center
  refine ⟨e,d.symm.trans e,?_⟩
  intro k
  change e (d.symm (d (QuotientGroup.mk' _ k))) = e (QuotientGroup.mk' _ k)
  rw [d.symm_apply_apply]

/-- E.3.6 on the selected doubled conjugate, at parameter 2n. -/
theorem selected_family (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞)) :
    letI := ParameterComponent.omegaOrbit_elementary s
    (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ∈
      ChapterE.fixedSpaceFamily (sourceStarRepresentation s) (2 * S.field.degree) := by
  let := fullModule_elementary d
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := ParameterComponent.conjugate_fixedSpaceFamily s (fullModule L V) g hg
    (by simpa only [omegaClosure_eq_parameterOrbit] using ha)
  rw [hs, ENat.toNat_mul, ENat.toNat_ofNat, ENat.toNat_natCast] at hf
  let e := starOrbitEquiv s.outside.1.1.2
  have hh := ChapterE.fixedSpaceFamily_map_of_equivariant
    (ParameterComponent.orbitRepresentation s) (sourceStarRepresentation s)
    e.symm.toMonoidHom e.symm.injective (LinearEquiv.refl (ZMod 2) _)
    (by intro x v; change _ = ParameterComponent.orbitRepresentation s (e (e.symm x)) v
        rw [e.apply_symm_apply]; rfl) hf
  have hm : (ParameterComponent.actorImage T H ((fullModule L V).map (MulAut.conj g).toMonoidHom)).map
      e.symm.toMonoidHom =
        (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
    rw [← starOrbitEquiv_actor s.outside.1.1.2, map_map]
    simp [e]
  rwa [hm] at hh


/-- Faithfulness and the fixed-space family give |B*| ≥ 2^(2n). -/
theorem selected_card_lower (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Finite F] (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞)) :
    Nat.card F ≤ Nat.card
      ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) := by
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := selected_family s g d hg ha hs
  have hr := ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily
    (sourceStarRepresentation s) (sourceStarRepresentation_injective s) hf
  rw [hF]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hr).trans
    (Nat.pow_log_le_self 2 (Nat.card_pos.ne'))

/-- E.3.40 excludes nontrivial action on every normalized odd subgroup. -/
theorem selected_centralizes_odd (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞))
    (R : Subgroup (Star T H)) (hR : Odd (Nat.card R))
    (hn : (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      normalizer (R : Set (Star T H))) :
    (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      centralizer (R : Set (Star T H)) := by
  let := ParameterComponent.omegaOrbit_elementary s
  exact ChapterE.centralizes_odd_of_mem_fixedSpaceFamily (sourceStarRepresentation s)
    (sourceStarRepresentation_injective s)
    (ChapterE.fixedSpaceFamily_mono _ (by decide : 0 < 2) (by have := S.nonbinary; omega)
      (selected_family s g d hg ha hs)) R hR hn
/-- The original selected B* lies in K*, at the doubled field degree. -/
theorem selected_le_residual
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree))) :
    (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      residualStar T H := by
  by_contra hnot
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := selected_family s g d hg ha hs
  obtain ⟨_,e,_⟩ := compatible_matrix_equivs s hF hmodel
  let : IsElementaryAbelian 2
      ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) := hf.2.1.2
  obtain ⟨R,_,hR,hn,hc⟩ := SylowPlacement.rankOne_odd_witness
    (by have := S.nonbinary; omega) hF (residualStar T H) e
    (source_star_core s) (source_star_residual_quotient_two s.outside.1.1.2)
    _ (selected_card_lower s g d hF hg ha hs) hnot
  exact hc (selected_centralizes_odd s g d hg ha hs R hR hn)

/-- Once placed in K*, the same image fills a Sylow subgroup by its order bound. -/
theorem selected_sylow_of_containment
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree)))
    (hAK : (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      residualStar T H) :
    ∃ R : Sylow 2 (residualStar T H),
      (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
  let := ParameterComponent.omegaOrbit_elementary s
  let A := (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)
  let : IsElementaryAbelian 2 A := (selected_family s g d hg ha hs).2.1.2
  obtain ⟨R,hR⟩ := ((IsElementaryAbelian.isPGroup 2 A).comap_subtype
    (K := residualStar T H)).exists_le_sylow
  have hle : A ≤ (R : Subgroup (residualStar T H)).map (residualStar T H).subtype := by
    intro a ha
    exact ⟨⟨a,hAK ha⟩,hR ha,rfl⟩
  obtain ⟨_,e,_⟩ := compatible_matrix_equivs s hF hmodel
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card ((R : Subgroup (residualStar T H)).map (residualStar T H).subtype) =
      Nat.card F := calc
    _ = Nat.card R := card_map_of_injective (residualStar T H).subtype_injective
    _ = Nat.card P := Nat.card_congr
      ((R : Subgroup (residualStar T H)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card F := (Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
  refine ⟨R,(eq_of_le_of_card_ge hle ?_).symm⟩
  rw [hcard]
  exact selected_card_lower s g d hF hg ha hs

/-- The selected image is Sylow in the actual residual image, using the
doubled s-value and the residual recognition at degree 2n. -/
theorem selected_sylow
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) = ((2 * S.field.degree) : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree))) :
    ∃ R : Sylow 2 (residualStar T H),
      (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) :=
  selected_sylow_of_containment s g d hF hg ha hs hmodel
    (selected_le_residual s g d hF hg ha hs hmodel)


/-- The literal selected image has rank exactly 2n. -/
theorem selected_rank (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
      (2 * S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree))) :
    rank ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
      (starProjection T H)) = 2 * S.field.degree := by
  obtain ⟨R,hR⟩ := selected_sylow s g d hF hg ha hs hmodel
  obtain ⟨_,e,_⟩ := compatible_matrix_equivs s hF hmodel
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card ((R : Subgroup (residualStar T H)).map (residualStar T H).subtype) =
      2 ^ (2 * S.field.degree) := calc
    _ = Nat.card R := card_map_of_injective (residualStar T H).subtype_injective
    _ = Nat.card P := Nat.card_congr
      ((R : Subgroup (residualStar T H)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card F := (Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv).symm
    _ = 2 ^ (2 * S.field.degree) := hF
  rw [← hR,rank,hc,Nat.log_pow (by decide : 1 < 2)]

private theorem proper_corank_lt_rank {X : Type*} [Group X] [Finite X]
    {A B : Subgroup X} [IsElementaryAbelian 2 A] (hBA : B ≤ A) (hB : B ≠ ⊥) :
    Nat.log 2 (B.relIndex A) < rank A := by
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB
  have hcardB : 1 < Nat.card (B.subgroupOf A) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv]
    exact Finite.one_lt_card
  have hpos : 0 < B.relIndex A := Nat.pos_of_ne_zero
    (B.subgroupOf A).index_ne_zero_of_finite
  have hc := (B.subgroupOf A).index_mul_card
  change B.relIndex A * Nat.card (B.subgroupOf A) = Nat.card A at hc
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hp : Nat.card A = 2 ^ rank A := by
    rw [rank,hr,Nat.log_pow (by decide : 1 < 2)]
  apply (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hpos)).mpr
  rw [← hp,← hc]
  nlinarith

/-- Uniformity is derived from E.3.6 and the actual Sylow rank, for every
nonidentity element of the selected image in H/C_H(V_H). -/
theorem selected_uniform (s : Hypothesis1131At D S U₁ H) (g : G)
    (d : Coordinates D S)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * S.field.degree))
    (hg : (fullModule L V).map (MulAut.conj g).toMonoidHom ≤ T)
    (ha : ¬ (fullModule L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
      (2 * S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ (2 * S.field.degree)))
    (a : Star T H)
    (haA : a ∈ (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
      (starProjection T H)) (ha1 : a ≠ 1) :
    letI := omegaOrbit_elementary s
    fixedSpace (sourceStarRepresentation s) (zpowers a) =
      fixedSpace (sourceStarRepresentation s)
        ((((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
          (starProjection T H)) := by
  let := omegaOrbit_elementary s
  have hf := selected_family s g d hg ha hs
  let A := (((fullModule L V).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
    (starProjection T H)
  let : IsElementaryAbelian 2 A := hf.2.1.2
  have hz : zpowers a ≤ A := zpowers_le.mpr haA
  have hn : zpowers a ≠ ⊥ := fun he => ha1 (mem_bot.mp (he ▸ mem_zpowers a))
  apply (hf.2.2 (zpowers a) hz ?_).symm
  rw [← selected_rank s g d hF hg ha hs hmodel]
  exact proper_corank_lt_rank hz hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
