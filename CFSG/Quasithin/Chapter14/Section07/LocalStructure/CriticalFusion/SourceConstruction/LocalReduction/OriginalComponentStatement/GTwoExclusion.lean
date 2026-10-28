module
public import Theory.SpecificGroups.G2.InvertedCubicBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.RankTwoContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentCentralResidual

/-!
# Exclusion of the nonbinary G₂ component row

For every original local I and every actual C-component C, the literal
C/O₂(C) cannot be G₂(2ⁿ) with n > 1. The existing cubic-rank argument
first puts the original L₁ in C. Solvable Sylow-overgroup control puts it
in the normalizer of the original T∩C, which 14.7.29 places in N_G(L).

On the actual split torus quotient, the original inverter in T∩L fixes
the source action-kernel supplement and inverts the cubic image of L₁.
Thus every displacement belongs to that cubic subgroup. The full G₂
inner–field calculation acts identically on both torus coordinates, so a
nontrivial action has at least four displacements. This forces trivial
torus action, contradicting the original cubic inversion.

This discharges the G₂ row of 14.7.41(2) without a supplied point
containment, Borel marking or inverter. Earlier structural, faithful and
14.7.10 hypotheses remain explicit. Central-cover and module reductions,
and the all-component Earlier14747 assembly, remain separate obligations.

Source: Aschbacher–Smith 14.7.40–41, printed p.1061, refs/quasithin.pdf.
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

/-- No original local component has a nonbinary G₂ quotient. -/
theorem local_gTwo_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.G2.Model E) : False := by
  have hlarge : 2 < Nat.card E := by
    rw [hE]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  have hin := local_gTwo_component_contains_point d h hab structural previous
    faithful earlier I hI C hC hlarge e
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hCN := local_cComponent_normal d h hab structural previous faithful earlier
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
      IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card h structural)
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
      (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) hx) (j a)
  let q : C →* Atlas.G2.Model E := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker ≤ (P : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hAN : A ≤ N :=
    Atlas.G2.InvertedCubicBorel.solvable_sylow_normalized_le_normalizer
      hlarge q hq P hqk A hPA
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
  have hBM := point_normalized_solvable_le_normalizer d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hBA := point_normalized_solvable_normalizes_point d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hAres : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype := by
    have hh := embedded_pResidual_mono 2 hAB
    have hpA : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
    rw [(pResidual_eq_top_iff 2 _).mpr hpA,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  obtain ⟨t,hti⟩ := exists_point_core_inverter (F := F) h structural
  let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let α : MulAut C := MulAut.conjNormal t'
  let β : MulAut (Atlas.G2.Model E) := MulAut.congr e ((pCore 2 C).quotientAut α)
  have hact (x : C) : q (α x) = β (q x) := by
    change e (QuotientGroup.mk' _ (α x)) =
      e ((pCore 2 C).quotientAut α (e.symm (e (QuotientGroup.mk' _ x))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  obtain ⟨f₀,τ,hf₀,hk₀,he₀,htrivial⟩ :=
    Atlas.G2.InvertedCubicBorel.exists_normalizer_torus_action
      hlarge q hq P hqk α β hact (hPpres t' t.property.1)
  let Z := Eˣ × Eˣ
  let eb : N ≃* B₀ := equivMapOfInjective N j hj
  let f : B₀ →* Z := f₀.comp eb.symm.toMonoidHom
  have hf : Function.Surjective f := hf₀.comp eb.symm.surjective
  have hk : IsPGroup 2 f.ker := by
    have hker : f₀.ker = (P : Subgroup C).subgroupOf N := by
      ext x
      exact hk₀ x
    have hk' : IsPGroup 2 f₀.ker := by
      rw [hker]
      exact P.isPGroup'.comap_of_injective N.subtype N.subtype_injective
    exact hk'.comap_of_injective eb.symm.toMonoidHom eb.symm.injective
  have ho : Odd (Nat.card Z) := by
    rw [Nat.card_congr Atlas.G2.torusParameterEquiv.toEquiv]
    exact Atlas.G2.EvenBorelTorus.card_torus_odd
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
      (pointResidual_core_quotient_card h structural)
  obtain ⟨hgen,hfix⟩ := point_borel_torus_supplement h structural B₀ hBM hAres hBA f hf hk ho
    t t.property.2 (hTB t.property.1) τ he
  have hinv := SourceActions.Markings.image_inverted B₀ (F.Li L 1) hAB f hk ho
    ⟨t,hTB t.property.1⟩
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) t.property.1) τ he hti
  have hτne : τ ≠ 1 := by
    intro htau
    have hbot : X = ⊥ := eq_bot_iff.mpr fun x hx => by
      have hi := hinv x hx
      rw [htau] at hi
      change x = x⁻¹ at hi
      have htwo : x^2 = 1 := by
        rw [pow_two]
        exact (congrArg (x * ·) hi).trans (mul_inv_cancel _)
      have hthree : x^3 = 1 := by
        have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : X))
        rw [hX] at hh
        exact congrArg Subtype.val hh
      simpa [pow_succ,htwo] using hthree
    have hh := X.eq_bot_iff_card.mp hbot
    omega
  apply hτne
  apply htrivial
  let δ : Z →* Z := τ.toMonoidHom * (MonoidHom.id _)⁻¹
  have hd (x : Z) : δ x = τ x * x⁻¹ := rfl
  have hle : δ.range ≤ X := by
    rintro _ ⟨x,rfl⟩
    have hx : x ∈ X ⊔ _ := hgen ▸ mem_top x
    obtain ⟨p,hp,c,hc,rfl⟩ := mem_sup_of_normal_right.mp hx
    rw [map_mul,hd,hd,hinv p hp,hfix c hc,mul_inv_cancel,mul_one]
    exact X.mul_mem (X.inv_mem hp) (X.inv_mem hp)
  exact (card_le_of_le hle).trans_eq hX

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
