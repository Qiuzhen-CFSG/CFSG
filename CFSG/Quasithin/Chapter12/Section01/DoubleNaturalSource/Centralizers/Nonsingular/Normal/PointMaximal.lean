module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.CubicExclusion
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.FourMaximal
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# Completing the normal-residual branches of the nonsingular centralizer argument

The restriction of the original normalizer action to LT is surjective and
has a two-group kernel. The given relative Sylow C_T(w), together with L_w,
therefore gives the full inverse image of the nonsingular stabilizer. The
concrete degree-four maximality theorem proves that L_w C_T(w) is maximal
in LT. This discharges the remaining C.5.7 premise and excludes the cubic
block, completing the degree-four normal-residual implication.

The final application joins this result with the proved degree-five normal
branch. Characteristic two and the nonnormal-parabolic fixed-line argument
remain explicit source obligations of qt-d-double-natural-centralizers.
The pure-fusion and corrected MS obligations retain their independent owners
and their final discharge at qt-d-1222-double-natural. No earlier use of
degree-four zeroth closure occurs here.

Source: Aschbacher--Smith, 12.1.1, printed pp.788--789; C.5.7, printed p.160.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (B : DoubledBranch T L V n)

omit [Finite G] in
/-- The literal action restricted to LT has a two-group kernel. -/
theorem join_action_kernel_twoGroup (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsPGroup 2 (B.actionProjection.comp (inclusion (sup_le L.le_normalizer hTM))).ker := by
  let J := L ⊔ (T : Subgroup G)
  let f : J →* B.ActionQuotient :=
    B.actionProjection.comp (inclusion (sup_le L.le_normalizer hTM))
  let Lj := L.subgroupOf J
  let Tj := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let : Lj.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTM)
  have hgen : Lj ⊔ (Tj : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  let e : Lj ≃* L := subgroupOfEquivOfLe le_sup_left
  have hk : IsPGroup 2 (f.comp Lj.subtype).ker := by
    have he : f.comp Lj.subtype = B.componentToActionQuotient.comp e.toMonoidHom := rfl
    rw [he,← MonoidHom.comap_ker,B.componentToActionQuotient_ker]
    exact pCore_isPGroup.comap_of_injective e.toMonoidHom e.injective
  exact f.kernel_isPGroup_of_normal_supplement Lj Tj Tj.isPGroup' hgen hk

/-- LT already induces the full original normalizer action quotient. -/
theorem join_action_surjective (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Function.Surjective (B.actionProjection.comp (inclusion (sup_le L.le_normalizer hTM))) := by
  let J := L ⊔ (T : Subgroup G)
  let f : J →* B.ActionQuotient :=
    B.actionProjection.comp (inclusion (sup_le L.le_normalizer hTM))
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hL : B.componentToActionQuotient.range ≤ f.range := by
    rintro a ⟨l,rfl⟩
    exact ⟨⟨l,mem_sup_left l.property⟩,rfl⟩
  have hP : (P : Subgroup B.ActionQuotient) ≤ f.range := by
    rintro a ⟨t,ht,rfl⟩
    exact ⟨⟨t,mem_sup_right ht⟩,rfl⟩
  let : B.componentToActionQuotient.range.Normal :=
    normal_of_index_eq_two B.component_range_index
  have hquot : IsPGroup 2 (B.ActionQuotient ⧸ B.componentToActionQuotient.range) :=
    IsPGroup.of_card (n := 1) B.component_range_index
  have hr := (pResidual_le_iff_isPGroup_quotient 2 B.componentToActionQuotient.range).mpr hquot
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top P]
  exact sup_le (hr.trans hL) hP

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Maximality of the literal nonsingular point join in LT in degree four. -/
theorem doubleNatural_four_adapted_pointJoin_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      IsCoatom ((B.pointResidual w ⊔ B.pointSylow w).subgroupOf (L ⊔ (T : Subgroup G))) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let M := L ⊔ (T : Subgroup G)
  let J := B.pointResidual w ⊔ B.pointSylow w
  have hMN : M ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  let f : M →* B.ActionQuotient := B.actionProjection.comp (inclusion hMN)
  have hf : Function.Surjective f := B.join_action_surjective D.sylow_normalizes_component
  have hker := B.join_action_kernel_twoGroup D.sylow_normalizes_component
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hJM : J ≤ M := sup_le ((B.pointResidual_le w).trans (inf_le_left.trans le_sup_left))
    (inf_le_left.trans le_sup_right)
  have hJN : J ≤ B.localPointCentralizer w := sup_le
    (le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)) hPM
  have hkJ : f.ker ≤ J.subgroupOf M := by
    intro x hx
    have ht : (x : G) ∈ (T : Subgroup G) := hker.le_sylow_of_normal P hx
    have hc : (x : G) ∈ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      have he : B.actionProjection (inclusion hMN x) = 1 := hx
      have hh := (QuotientGroup.eq_one_iff (inclusion hMN x)).mp he
      rw [normalizerAction_ker] at hh
      exact hh
    exact mem_sup_right ⟨ht,mem_centralizer_singleton_iff.mpr (hc _ w.property).symm⟩
  have hmap : (J.subgroupOf M).map f = S.setup.stabilizer (Additive.ofMul w) := by
    apply le_antisymm
    · rintro a ⟨j,hj,rfl⟩
      have hh : inclusion hMN j ∈ (S.setup.stabilizer (Additive.ofMul w)).comap
          B.actionProjection := by
        rw [S.stabilizer_comap]
        exact (hJN hj).2
      exact hh
    · intro a ha
      obtain ⟨j,hj⟩ := S.adapted_pointJoin_action_surjective w hw hPM ⟨a,ha⟩
      exact ⟨⟨j,hJM j.property⟩,j.property,congrArg Subtype.val hj⟩
  have hmax : IsCoatom (S.setup.stabilizer (Additive.ofMul w)) := by
    apply (OrderIso.isCoatom_iff S.setup.model.group.mapSubgroup _).mp
    change IsCoatom ((S.setup.stabilizer (Additive.ofMul w)).map S.setup.model.group.toMonoidHom)
    rw [S.setup.stabilizer_map]
    apply BinaryNaturalDual.VectorStabilizers.four_nonsingular_stabilizer_isCoatom
    have hh : S.setup.quadratic (Additive.ofMul w) = 1 := by
      rw [S.quadratic_eq]
      exact hw.nonsingular
    simpa only [S.setup.quadratic_apply] using hh
  have he : (S.setup.stabilizer (Additive.ofMul w)).comap f = J.subgroupOf M := by
    rw [←hmap,comap_map_eq_self hkJ]
  rw [←he]
  exact isCoatom_comap_of_surjective hf hmax

/-- The degree-four normal-residual branch of 12.1.1, with cubic maximality discharged. -/
theorem doubleNatural_four_adapted_normal_centralizer_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      B.pointCentralizer w ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn
  exact D.doubleNatural_four_adapted_normal_centralizer_le_of_pointJoin_maximal h B S w hw hc hn
    (D.doubleNatural_four_adapted_pointJoin_maximal h B S w hw)

/-- Both normal-residual branches are discharged in the nonsingular and degree-five closure consumer. -/
theorem doubleNatural_nonsingular_controls_of_characteristic_parabolic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hchar hparabolic
  apply D.doubleNatural_nonsingular_controls_of_pointJoin_maximal_of_many h hmany B hchar _ hparabolic
  intro hn S w hw
  subst n
  exact D.doubleNatural_four_adapted_pointJoin_maximal h B S w hw

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
