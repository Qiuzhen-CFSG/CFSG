module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.OffenderSource
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages

/-!
# Structure of the literal residual offender actor

The exact map B → BP identifies BP with B/O₂(B). The earlier 14.3.4(1–2)
classification supplies quasisimplicity and R₁-normalization. The original
QTKE hypothesis supplies SQTK with the full known-simple class. Since
P = BP R₁⁺, its quotient by BP is a two-group.

Maximum elementary subgroups of the specified R₁ give best offenders on
the same E, even after restriction to P. Thus [B,J(R₁)]=B implies BP ≤ Q.
For this literal Q, the two-group quotient and quasisimplicity give F*(Q)=BP
once O₂(Q)=1 is established; offender generation follows by restriction.
The constructor assembles these proved fields while retaining the source
normality, commutator and two-core premises. It is not the completed source
application. EarlierFaithfulClassification is the universal 14.3.4 input,
owned by qt-14-03-prelim.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070 (PDF p.1087), and B.2.4–5 / B.5.1.
-/

@[expose] public section
noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ResidualNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

noncomputable def residualComponentOffenderEquiv
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (B ⧸ pCore 2 B) ≃* residualOffenderComponent (L := L) (F := F) B :=
  (QuotientGroup.quotientMulEquivOfEq (residualComponentToOffender_ker hB).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (residualComponentToOffender hB)
      (residualComponentToOffender_surjective hB))

include d

theorem residualOffenderComponent_simple
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    IsSimpleGroup (residualOffenderComponent (L := L) (F := F) B) := by
  rcases (d.residual_component_group_classification earlier hSylow hB).1 with ⟨e⟩ | ⟨e⟩
  · obtain ⟨e⟩ := e
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((residualComponentOffenderEquiv hB).symm.trans e).isSimpleGroup
  · obtain ⟨e⟩ := e
    let : IsSimpleGroup Matrix.PSL3Two.PSL :=
      Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    exact ((residualComponentOffenderEquiv hB).symm.trans e).isSimpleGroup

theorem residualOffenderComponent_quasisimple
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    IsQuasisimple (residualOffenderComponent (L := L) (F := F) B) := by
  let C := residualOffenderComponent (L := L) (F := F) B
  let := d.residualOffenderComponent_simple earlier hSylow hB
  let := residual_component_perfect hB
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := residualComponentToOffender hB) (residualComponentToOffender_surjective hB)
  have hz : center C = ⊥ := by
    apply (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center C) inferInstance).resolve_right
    intro he
    let : IsMulCommutative C := center_eq_top_iff.mp he
    exact Group.IsPerfect.not_isSolvable C inferInstance
  exact { toIsPerfect := inferInstance
          simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
            QuotientGroup.quotientBot).isSimpleGroup }

theorem residual_component_sqtk
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    IsSQTK KnownSimple.IsKnownSimple B := by
  have he : E F ≠ ⊥ := by
    intro hz
    apply d.z_ne_one
    exact mem_bot.mp (hz ▸ point_le_E (by rw [d.point]; exact mem_zpowers _))
  let := d.residualSpan_elementary hSylow
  have hlocal : IsTwoLocal (normalizer (E F : Set G)) :=
    ⟨E F, he, IsElementaryAbelian.isPGroup 2 (E F), rfl⟩
  have hn := d.counterexample.qtke.twoLocal_sqtk hlocal
  have hBN : B ≤ normalizer (E F : Set G) :=
    (hB.1.trans J_le_Y).trans d.residual_Y_normalizes_E
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hBN)).mp (hn.subgroup _)

theorem residualOffenderComponent_sqtk
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    IsSQTK KnownSimple.IsKnownSimple (residualOffenderComponent (L := L) (F := F) B) := by
  apply (IsSQTK.equiv (residualComponentOffenderEquiv hB)).mp
  have hsq := d.residual_component_sqtk hSylow hB
  refine ⟨?_, hsq.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho
    (pCore 2 B) pCore_isPGroup).trans (hsq.stronglyQuasithin p hp ho)

theorem residualOffenderComponent_normal
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (residualOffenderComponent (L := L) (F := F) B).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have hBY : B ≤ Y L F := hB.1.trans J_le_Y
  have hn : B ⊔ F.Ri L 1 ≤ normalizer (B : Set G) :=
    sup_le B.le_normalizer (residual_R_le_sylow.trans
      (d.residual_T_normalizes_component earlier hSylow hB))
  have hni : (B ⊔ F.Ri L 1).subgroupOf (Y L F) ≤
      normalizer (B.subgroupOf (Y L F) : Set (Y L F)) := by
    rw [← subgroupOf_normalizer_eq hBY]
    exact comap_mono hn
  exact (map_mono hni).trans (le_normalizer_map _)


theorem residualOffenderActor_two_quotient
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := d.residualOffenderComponent_normal earlier hSylow hB
    IsPGroup 2 (residualOffenderActor (L := L) (F := F) B ⧸
      residualOffenderComponent (L := L) (F := F) B) := by
  let := d.residualOffenderComponent_normal earlier hSylow hB
  let P := residualOffenderActor (L := L) (F := F) B
  let C := residualOffenderComponent (L := L) (F := F) B
  let q := residualOffenderQuotient (L := L) (F := F)
  let R := ((F.Ri L 1).subgroupOf (Y L F)).map q
  have hBY : B ≤ Y L F := hB.1.trans J_le_Y
  have hRY : F.Ri L 1 ≤ Y L F := le_sup_right
  have hRP : R ≤ P := map_mono (comap_mono (show F.Ri L 1 ≤ B ⊔ F.Ri L 1 from le_sup_right))
  have hi : B.subgroupOf (Y L F) ⊔ (F.Ri L 1).subgroupOf (Y L F) =
      (B ⊔ F.Ri L 1).subgroupOf (Y L F) := by
    apply map_injective (Y L F).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBY,
      map_subgroupOf_eq_of_le hRY, map_subgroupOf_eq_of_le (sup_le hBY hRY)]
  have hgen : C ⊔ R.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, residualOffenderComponent_map_subtype,
      map_subgroupOf_eq_of_le hRP, ← MonoidHom.range_eq_map, range_subtype]
    change (B.subgroupOf (Y L F)).map q ⊔ ((F.Ri L 1).subgroupOf (Y L F)).map q = P
    rw [← Subgroup.map_sup, hi]
    rfl
  exact isPGroup_quotient_of_sup_eq_top C (R.subgroupOf P)
    (((T.isPGroup'.to_le residual_R_le_sylow).comap_subtype.map q).comap_subtype) hgen

theorem residualOffenderSubgroup_generated
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    let := (d.residualSpan_reduced hSylow).elementary
    offenderSubgroup ((d.residualOffenderAction hSylow B).comp
      (d.residualOffenderSubgroup hSylow B).subtype) = ⊤ := by
  let := (d.residualSpan_reduced hSylow).elementary
  exact offenderSubgroup_restrict_eq_top _

theorem residualOffenderSubgroup_normal
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    (d.residualOffenderSubgroup hSylow B).Normal := by
  let := (d.residualSpan_reduced hSylow).elementary
  exact offenderSubgroup_normal _

theorem residualOffenderSubgroup_twoCore_of_actor
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G)
    (hcore : pCore 2 (residualOffenderActor (L := L) (F := F) B) = ⊥) :
    pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 (d.residualOffenderSubgroup_normal hSylow B).isSubnormal,
    hcore]
  exact (MonoidHom.ker_eq_bot_iff _).mpr (d.residualOffenderSubgroup hSylow B).subtype_injective

theorem residualOffenderSubgroup_fitting
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hCQ : residualOffenderComponent (L := L) (F := F) B ≤
      d.residualOffenderSubgroup hSylow B)
    (hcore : pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥) :
    generalizedFitting (d.residualOffenderSubgroup hSylow B) =
      (residualOffenderComponent (L := L) (F := F) B).subgroupOf
        (d.residualOffenderSubgroup hSylow B) := by
  let P := residualOffenderActor (L := L) (F := F) B
  let C := residualOffenderComponent (L := L) (F := F) B
  let Q := d.residualOffenderSubgroup hSylow B
  let : C.Normal := d.residualOffenderComponent_normal earlier hSylow hB
  let : IsQuasisimple C := d.residualOffenderComponent_quasisimple earlier hSylow hB
  let : IsQuasisimple (C.subgroupOf Q) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCQ).symm
  have hquot : IsPGroup 2 (Q ⧸ C.subgroupOf Q) := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) x
    obtain ⟨n, hn⟩ := d.residualOffenderActor_two_quotient earlier hSylow hB
      (QuotientGroup.mk' C a.val)
    refine ⟨n, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    change a.val ^ 2 ^ n ∈ C
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' C (a.val ^ 2 ^ n) = 1
    rwa [map_pow]
  exact generalizedFitting_eq_of_quasisimple_two_quotient (C.subgroupOf Q) hquot hcore


/-- Every maximum elementary subgroup of the specified R₁ contributes a best
 offender after passing to P; this retains the action on the whole E. -/
theorem residual_sylowThompson_image_le_offender
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    (Stellmacher.elementaryAbelianMaxJ ((F.Ri L 1).subgroupOf (Y L F))).map
      (residualOffenderQuotient (L := L) (F := F)) ≤
      (d.residualOffenderSubgroup hSylow B).map
        (residualOffenderActor (L := L) (F := F) B).subtype := by
  let := (d.residualSpan_reduced hSylow).normal
  let := (d.residualSpan_reduced hSylow).elementary
  let q := residualOffenderQuotient (L := L) (F := F)
  let P := residualOffenderActor (L := L) (F := F) B
  let Q := d.residualOffenderSubgroup hSylow B
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hz : A.map q = ⊥
  · rw [hz]; exact bot_le
  have hbest : IsBestOffender (d.residualRepresentation hSylow) (A.map q) :=
    Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      ((E F).subgroupOf (Y L F)) q (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (d.residual_internal_centralizer_eq_core hSylow).symm)
      ((F.Ri L 1).subgroupOf (Y L F)) A (comap_mono (d.residualSpan_le_R hSylow)) hA hz
  have hAP : A.map q ≤ P := map_mono (hA.1.trans
    (comap_mono (show F.Ri L 1 ≤ B ⊔ F.Ri L 1 from le_sup_right)))
  have hm := map_mono (f := P.subtype)
    ((hbest.subgroupOf (d.residualRepresentation hSylow) hAP).le_offenderSubgroup
      ((d.residualRepresentation hSylow).comp P.subtype))
  rwa [map_subgroupOf_eq_of_le hAP] at hm

/-- Thompson commutator generation puts the distinguished component in the
 actual offender group. Mere FF for the larger actor is not used. -/
theorem residualOffenderComponent_le_of_commutator
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hc : ⁅B, Stellmacher.elementaryAbelianMaxJ (F.Ri L 1)⁆ = B) :
    residualOffenderComponent (L := L) (F := F) B ≤ d.residualOffenderSubgroup hSylow B := by
  let P := residualOffenderActor (L := L) (F := F) B
  let Q := d.residualOffenderSubgroup hSylow B
  let q := residualOffenderQuotient (L := L) (F := F)
  let R := Stellmacher.elementaryAbelianMaxJ ((F.Ri L 1).subgroupOf (Y L F))
  have hBY : B ≤ Y L F := hB.1.trans J_le_Y
  have hci : ⁅B.subgroupOf (Y L F), R⁆ = B.subgroupOf (Y L F) := by
    apply map_injective (Y L F).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hBY]
    change ⁅B, (Stellmacher.elementaryAbelianMaxJ
      ((F.Ri L 1).subgroupOf (Y L F))).map (Y L F).subtype⁆ = B
    rw [← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ Y L F from le_sup_right), hc]
  let : Q.Normal := d.residualOffenderSubgroup_normal hSylow B
  have hn : P ≤ normalizer (Q.map P.subtype : Set (Y L F ⧸ pCore 2 (Y L F))) := by
    have hh := le_normalizer_map (H := Q) P.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
  have he : ⁅residualOffenderComponentPlus (L := L) (F := F) B, R.map q⁆ =
      residualOffenderComponentPlus (L := L) (F := F) B := by
    change ⁅(B.subgroupOf (Y L F)).map q, R.map q⁆ = _
    rw [← map_commutator, hci]
    rfl
  have hm : residualOffenderComponentPlus (L := L) (F := F) B ≤ Q.map P.subtype := by
    rw [← he]
    exact (commutator_mono residualOffenderComponentPlus_le_actor
      (d.residual_sylowThompson_image_le_offender hSylow B)).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  rw [← residualOffenderComponent_map_subtype] at hm
  exact (map_le_map_iff_of_injective P.subtype_injective).mp hm

/-- Assemble all eight source-input fields from the three remaining local facts.
The full known-simple class is supplied by the original QTKE hypothesis. -/
theorem offenderSourceInput_of_source_facts
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hn : (B.subgroupOf (normalizer (K F : Set G))).Normal)
    (hc : ⁅B, Stellmacher.elementaryAbelianMaxJ (F.Ri L 1)⁆ = B)
    (hcore : pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥) :
    OffenderSourceInput d KnownSimple.IsKnownSimple hSylow hB := by
  have hCQ := d.residualOffenderComponent_le_of_commutator hSylow hB hc
  let Q := d.residualOffenderSubgroup hSylow B
  let C := residualOffenderComponent (L := L) (F := F) B
  let : IsQuasisimple C := d.residualOffenderComponent_quasisimple earlier hSylow hB
  refine ⟨hn, hc, hCQ, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hCQ).symm,
    (IsSQTK.equiv (subgroupOfEquivOfLe hCQ)).mpr (d.residualOffenderComponent_sqtk hSylow hB),
    ?_, hcore, d.residualOffenderSubgroup_generated hSylow B⟩
  have hf := d.residualOffenderSubgroup_fitting earlier hSylow hB hCQ hcore
  have hnil : Group.IsNilpotent (center Q) := by
    refine ⟨1, ?_⟩
    rw [upperCentralSeries_one_eq_top_iff]
    infer_instance
  have hz : center Q ≤ generalizedFitting Q :=
    (show center Q ≤ fittingSubgroup Q from le_sSup ⟨inferInstance, hnil⟩).trans
      (fitting_le_generalizedFitting Q)
  rw [hf] at hz ⊢
  exact (sup_eq_left.mpr hz).symm

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
