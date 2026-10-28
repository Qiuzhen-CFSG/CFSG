module
public import Theory.SpecificGroups.SL2.InvertedCubicBorel
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneContradiction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement

/-!
# The contained binary rank-one row at the original group

The actual component normality theorem and marked Borel calculation use
only the earlier structural theorems at the original G,T. The original
point residual gives an inverted cubic in the Borel torus, while its
centralizer gives the fixed supplement. The resulting field has order
four, so the literal quotient is the permitted alternating-five carrier.
No outside-component containment or later component-list statement is
assumed. Source: Aschbacher--Smith 14.7.41(2), printed p.1061,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- An actual binary L₂ component containing the original point has field four. -/
theorem local_linearTwo_contained_field_four_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) : n = 2 := by
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hCN := local_cComponent_normal_at d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let : C.Normal := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hCN
  let : Group.IsPerfect C := hC.perfect
  let j : C →* G := I.subtype.comp C.subtype
  have hj : Function.Injective j := I.subtype_injective.comp C.subtype_injective
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let N : Subgroup C := normalizer (P : Set C)
  let B₀ : Subgroup G := N.map j
  let A : Subgroup C := (F.Li L 1).comap j
  have hArange : F.Li L 1 ≤ j.range := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hin
  have hAm : A.map j = F.Li L 1 := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hArange
  let ea : A ≃* F.Li L 1 :=
    (equivMapOfInjective A j hj).trans (MulEquiv.subgroupCongr hAm)
  let : Group.IsSolvable (F.Li L 1) := by
    let : Group.IsNilpotent (pCore 2 (F.Li L 1)) := pCore_isPGroup.isNilpotent
    have hp : IsPGroup 3 (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
      IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card_at h structural)
    let := hp.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (F.Li L 1))).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective (f := ea.toMonoidHom) ea.injective
  have hPA : (P : Subgroup C) ≤ normalizer (A : Set C) := by
    intro x hx
    rw [hP] at hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp
      (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) hx) (j a)
  let es : (C ⧸ pCore 2 C) ≃* SL(2,E) :=
    e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
  let q : C →* SL(2,E) := es.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := es.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker ≤ (P : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ es.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hAN : A ≤ N :=
    Matrix.SpecialLinearGroup.solvable_sylow_normalized_le_normalizer q hq P hqk A hPA
  have hAB : F.Li L 1 ≤ B₀ := hAm ▸ map_mono (f := j) hAN
  have hPpres (t : I) (ht : (t : G) ∈ T) :
      (P : Subgroup C).map (MulAut.conjNormal t).toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP] at hx ⊢
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx)
        ((T : Subgroup G).inv_mem ht)
    · rw [card_map_of_injective (f := (MulAut.conjNormal t : MulAut C).toMonoidHom)
        (K := (P : Subgroup C)) (MulAut.conjNormal t : MulAut C).injective]
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := by
    intro t ht
    let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI ht⟩
    let α : MulAut C := MulAut.conjNormal t'
    have hN : N.map α.toMonoidHom = N := by
      change (normalizer (P : Set C)).map α.toMonoidHom = normalizer (P : Set C)
      have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom)
        (P : Subgroup C) α.bijective
      rw [show (P : Subgroup C).map α.toMonoidHom = P from hPpres t' ht] at hh
      simpa only [Sylow.coe_coe] using hh
    have he : (MulAut.conj t).toMonoidHom.comp j = j.comp α.toMonoidHom := rfl
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (N.map j).map (MulAut.conj t).toMonoidHom = N.map j
    rw [Subgroup.map_map,he,←Subgroup.map_map,hN]
  have hnB : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) :=
    sup_le (hAB.trans B₀.le_normalizer) hTB
  have hBH : B₀ ≤ F.H :=
    (map_mono (show N ≤ ⊤ from le_top)).trans (by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
      exact (map_subtype_le _).trans hI.2.1)
  let : Group.IsSolvable N := P.normalizer_isSolvable_two
  have hsol : Group.IsSolvable B₀ :=
    Group.isSolvable_of_surjective (j.subgroupMap_surjective N)
  have hBM := WholeResidualAssembly.GuardedSource.point_normalized_solvable_le_normalizer d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hBA := WholeResidualAssembly.GuardedSource.point_normalized_solvable_normalizes_point d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hAres : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype := by
    have hh := embedded_pResidual_mono 2 hAB
    have hpA : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
    rw [(pResidual_eq_top_iff 2 _).mpr hpA,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  obtain ⟨t,hti⟩ := AlternatingSevenSource.exists_point_core_inverter_at (F := F) h structural
  let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let α : MulAut C := MulAut.conjNormal t'
  let β : MulAut SL(2,E) := MulAut.congr es ((pCore 2 C).quotientAut α)
  have hact (x : C) : q (α x) = β (q x) := by
    change es (QuotientGroup.mk' _ (α x)) =
      es ((pCore 2 C).quotientAut α (es.symm (es (QuotientGroup.mk' _ x))))
    rw [es.symm_apply_apply,quotientAut_apply_mk]
  obtain ⟨f₀,σ,hf₀,hk₀,he₀⟩ :=
    Matrix.SpecialLinearGroup.exists_sylowNormalizer_torus_action q hq P hqk α β
      hact (hPpres t' t.property.1)
  let eb : N ≃* B₀ := equivMapOfInjective N j hj
  let f : B₀ →* Eˣ := f₀.comp eb.symm.toMonoidHom
  have hf : Function.Surjective f := hf₀.comp eb.symm.surjective
  have hk : IsPGroup 2 f.ker := by
    have hker : f₀.ker = (P : Subgroup C).subgroupOf N := by
      ext x
      exact hk₀ x
    have hk' : IsPGroup 2 f₀.ker := by
      rw [hker]
      exact P.isPGroup'.comap_of_injective N.subtype N.subtype_injective
    exact hk'.comap_of_injective eb.symm.toMonoidHom eb.symm.injective
  have ho : Odd (Nat.card Eˣ) := by
    rw [Nat.card_units,hE]
    apply Nat.odd_iff.mpr
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [pow_succ]
    have hpos : 0 < (2 : ℕ)^k := pow_pos (by decide) _
    omega
  let τ : MulAut Eˣ := Units.mapEquiv σ.toMulEquiv
  have he (b : B₀) : τ (f b) = f (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) := by
    apply (he₀ (eb.symm b)
      (eb.symm (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b)) ?_).symm
    apply hj
    change j (α (eb.symm b)) = _
    have heb (c : B₀) : j (eb.symm c) = c := congrArg Subtype.val (eb.apply_symm_apply c)
    change (t : G) * j (eb.symm b) * (t : G)⁻¹ = _
    rw [heb,heb]
    rfl
  let X := SourceActions.Markings.image B₀ (F.Li L 1) f
  have hX : Nat.card X = 3 :=
    (SourceActions.Markings.image_card B₀ (F.Li L 1) hAB f hk ho).trans
      (pointResidual_core_quotient_card_at h structural)
  obtain ⟨hgen,hfix⟩ := ContainedProjectiveAt.point_borel_torus_supplement_at h structural B₀ hBM hAres hBA f hf hk ho
    t t.property.2 (hTB t.property.1) τ he
  have hinv := SourceActions.Markings.image_inverted B₀ (F.Li L 1) hAB f hk ho
    ⟨t,hTB t.property.1⟩
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) t.property.1) τ he hti
  have hsmall := FiniteField.card_le_four_of_inverted_cubic_fixed_supplement σ X _ hX
    hgen hfix hinv
  rw [hE] at hsmall
  have hnot : ¬ 3 ≤ n := by
    intro hh
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hh
    norm_num at hp
    omega
  omega


/-- A contained binary L₂ component is the literal A₅ carrier row. -/
theorem local_linearTwo_contained_component_row_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    WholeResidualAssembly.ComponentRows (C ⧸ pCore 2 C) := by
  have hn2 := local_linearTwo_contained_field_four_at d h hab structural previous
    faithful earlier I hI C hC hin hE hn e
  have hcard : Nat.card E = 4 := by
    rw [hE, hn2]
    norm_num
  exact Or.inr (Or.inl ⟨5, by decide, by decide,
    ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      hcard).some⟩⟩)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
