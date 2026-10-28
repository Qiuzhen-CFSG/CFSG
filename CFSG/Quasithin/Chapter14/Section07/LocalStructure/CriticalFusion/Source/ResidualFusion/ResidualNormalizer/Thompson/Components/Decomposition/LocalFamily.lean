module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.MarkedActions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal

/-!
# The reduced witness and faithful component in 14.7.67

The source uses 1.2.10 on a local overgroup containing the ambient Sylow
subgroup T. The original Y = DR₁ need not contain T. We show that T
normalizes D, R₁, Y and E, put the original component into YT, and prove
that the same E is reduced there. This supplies every hypothesis of the
reduced-witness direction of 1.2.10.

We also prove that direction directly for this witness: [B,E] lies in
Ω₁(Z(O₂(B))), is nonzero, and equals [[B,E],B]. Thus the intrinsic
signalizer module of B is nonzero. The actual earlier 14.3.4(1–2) then
supplies the two quotient alternatives, maximality and T-normalization.
That earlier universal implication is produced by qt-14-03-prelim; its
module clause (3) is a separate obligation, not inferred from group names.

Finally the literal projection B → Y/O₂(Y), and the marked representation
already used by the consumer, both have kernel O₂(B). Invariants are
identified with the original ambient centralizer. These results prepare
the B.5.1 application; they do not assert a splitting or a small-module
identification. The normality, Thompson-generation, offender reduction
and complete module-classification steps remain with Decomposition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.2.10, printed p.507; 14.3.4, p.990; 14.7.67(4), p.1070 (PDF p.1087).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)

omit [Finite G] in
theorem residual_T_normalizes_D : (T : Subgroup G) ≤ normalizer (D F : Set G) :=
  ((F.invariant 1).trans (H_normalizes_K F)).trans normalizer_K_normalizes_D

omit [Finite G] in
theorem residual_T_normalizes_R : (T : Subgroup G) ≤ normalizer (F.Ri L 1 : Set G) :=
  (show (T : Subgroup G) ≤ F.Li L 1 ⊔ T from le_sup_right).trans
    ((F.Li L 1 ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

omit [Finite G] in
theorem residual_T_normalizes_Y : (T : Subgroup G) ≤ normalizer (Y L F : Set G) :=
  (le_inf residual_T_normalizes_D residual_T_normalizes_R).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

include d

/-- E is elementary on the literal ambient carrier. -/
theorem residualSpan_elementary
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    IsElementaryAbelian 2 (E F) := by
  let := (d.residualSpan_reduced hSylow).elementary
  have hh := IsElementaryAbelian.map (p := 2) (Y L F).subtype
    (A := (E F).subgroupOf (Y L F))
  rwa [map_subgroupOf_eq_of_le
    (show E F ≤ Y L F from d.residualSpan_le_D.trans le_sup_left)] at hh

theorem residual_T_normalizes_E : (T : Subgroup G) ≤ normalizer (E F : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro t ht x ⟨a, ha, z, hz, rfl⟩
  have hc := mem_centralizer_iff.mp (d.H_centralizes_point (F.invariant 1 ht)) z hz
  apply Subgroup.subset_closure
  refine ⟨t * a * t⁻¹, le_normalizer_iff.mp residual_T_normalizes_D t ht a ha,
    z, hz, ?_⟩
  have hi : t⁻¹ * z * t = z := by rw [mul_assoc, hc]; simp
  calc
    (t * a * t⁻¹) * z * (t * a * t⁻¹)⁻¹ =
        t * a * (t⁻¹ * z * t) * a⁻¹ * t⁻¹ := by group
    _ = t * (a * z * a⁻¹) * t⁻¹ := by rw [hi]; group

theorem residualSpan_le_sylowJoin_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    E F ≤ (Y L F ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := d.residualSpan_elementary hSylow
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (E F))
    (d.residualSpan_le_D.trans (le_sup_left.trans le_sup_left))
    (sup_le d.residual_Y_normalizes_E d.residual_T_normalizes_E)

theorem residual_sylowJoin_mem_HOver
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    Y L F ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
  refine ⟨?_, fun _ hx => (show (T : Subgroup G) ≤ Y L F ⊔ T from le_sup_right) hx⟩
  intro he
  have hz : d.z ∈ E F := point_le_E (by rw [d.point]; exact mem_zpowers _)
  have hh := d.residualSpan_le_sylowJoin_core hSylow hz
  rw [he] at hh
  exact d.z_ne_one (mem_bot.mp hh)

omit d [Finite G] in
theorem residual_component_in_sylowJoin {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ∈ Chapter1.cComponentsIn (Y L F ⊔ (T : Subgroup G)) :=
  cComponent_join_sylow (residual_component_in_Y hB) residual_T_normalizes_Y

theorem residual_component_mem_localFamily
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ∈ Chapter1.L G (T : Subgroup G) :=
  ((Chapter1.lemma_1_2_6 T (d.residual_sylowJoin_mem_HOver hSylow)).1
    (residual_component_in_sylowJoin hB)).2

/-- Restriction of the reduced action kills the component's intrinsic two-core. -/
theorem residual_component_core_centralizes
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B.pCoreIn 2 ≤ centralizer (E F : Set G) := by
  have hBY := residual_component_in_Y hB
  exact (pCoreAmbient_mono_of_isSubnormalIn B (Y L F) 2 hBY.1 hBY.2.subnormal).trans
    ((d.residualSpan_centralizer_eq_core hSylow).symm.le.trans inf_le_right)

/-- The reduced witness proves the actual intrinsic module is nonzero. -/
theorem residual_component_faithful
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ∈ MainForward.faithfulLocalComponents T := by
  have hlocal := d.residual_component_mem_localFamily hSylow hB
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  have hBY := residual_component_in_Y hB
  have hEY : E F ≤ Y L F := d.residualSpan_le_D.trans le_sup_left
  have hBE : B ≤ normalizer (E F : Set G) := hBY.1.trans d.residual_Y_normalizes_E
  let := d.residualSpan_elementary hSylow
  have hcomm : ⁅B, E F⁆ ≤ B.pCoreIn 2 :=
    signalizer_commutator_le_pCore B (Y L F) (E F) hBY.1 hBY.2.subnormal hp
      ((isTwoSignalizer_iff _ _ _).mpr
        ⟨hEY, IsElementaryAbelian.isPGroup 2 (E F), hBE⟩)
  have hmove : ⁅B, E F⁆ ≠ ⊥ := fun he =>
    d.residual_component_not_centralizes hB (commutator_eq_bot_iff_le_centralizer.mp he)
  have hleE : ⁅B, E F⁆ ≤ E F := le_normalizer_iff_commutator_le_right.mp hBE
  have homega : ⁅B, E F⁆ ≤ Stellmacher.omegaOneCenterAmbient (B.pCoreIn 2) := by
    intro x hx
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hcomm hx, elemPow_eq_one_of_isElementaryAbelian x (hleE hx),
        fun q hq => (mem_centralizer_iff.mp
          (d.residual_component_core_centralizes hSylow hB hq) x (hleE hx)).symm⟩
  have hidem : ⁅⁅B, E F⁆, B⁆ = ⁅B, E F⁆ := by
    have hr : BenderSuzuki.External.hktPResidual 2 B = ⊤ :=
      hp _ BenderSuzuki.External.hktPResidual_normal
        BenderSuzuki.External.hktPResidual_quotient_isPGroup
    have hm : (BenderSuzuki.External.hktPResidual 2 B).map B.subtype = B := by
      rw [hr, ← MonoidHom.range_eq_map, range_subtype]
    have hh := BenderSuzuki.External.commutator_map_pResidual_idempotent_of_isPGroup
      2 (E F) B (IsElementaryAbelian.isPGroup 2 (E F)) hBE
    dsimp only at hh
    rw [hm, commutator_comm (E F) B] at hh
    exact hh
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (d.counterexample.qtke.evenCharacteristic T)).mpr
  refine ⟨hlocal, ?_⟩
  intro he
  apply hmove
  apply le_bot_iff.mp
  have hh := commutator_mono homega (le_refl B)
  rw [hidem] at hh
  have hi : ⁅Stellmacher.omegaOneCenterAmbient (B.pCoreIn 2), B⁆ =
      intrinsicSignalizerModule B := by
    rw [intrinsicSignalizerModule, signalizerModule_eq_commutator_omegaCenter, commutator_comm]
    rfl
  rwa [hi, he] at hh

/-- The same span is reduced in the Sylow overgroup required by 1.2.10. -/
theorem residualSpan_reduced_sylowJoin
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    IsPReduced 2 ((E F).subgroupOf (Y L F ⊔ (T : Subgroup G))) := by
  let H := Y L F ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let Z := (F.Vi 1).subgroupOf H
  have hZH : F.Vi 1 ≤ H := d.point_le_D.trans (le_sup_left.trans le_sup_left)
  have hZP : Z ≤ (P : Subgroup H) := by
    intro z hz
    exact (F.le_seed 1).trans d.natural.chosen.le_sylow hz
  let ZP := Z.subgroupOf (P : Subgroup H)
  let := d.U_elementary
  let : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_le d.conjugationSection.kernel_le
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf hZH
  have hZPc : ZP ≤ center (P : Subgroup H) := by
    intro z hz
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_iff.mp
      (d.H_centralizes_point (F.invariant 1 t.property)) z hz).symm
  let : ZP.Normal := ⟨by
    intro z hz t
    simpa only [(mem_center_iff.mp (hZPc hz)) t, mul_inv_cancel_right] using hz⟩
  have hZPr : IsPReduced 2 ZP := by
    refine ⟨inferInstance, IsElementaryAbelian.subgroupOf hZP, ?_⟩
    have hC : centralizer (ZP : Set (P : Subgroup H)) = ⊤ := by
      apply top_unique
      intro t _ z hz
      exact ((mem_center_iff.mp (hZPc hz)) t).symm
    apply bot_unique
    intro x _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (ZP : Set (P : Subgroup H))) x
    exact (QuotientGroup.eq_one_iff t).mpr (hC.symm ▸ mem_top t)
  have hspan : E F = conjugateSpanBy (F.Vi 1) H :=
    le_antisymm (conjugateSpanBy_mono le_rfl (le_sup_left.trans le_sup_left))
      (conjugateSpanBy_le point_le_E (sup_le d.residual_Y_normalizes_E d.residual_T_normalizes_E))
  have heq : normalClosure (Z : Set H) = (E F).subgroupOf H := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hZH, ← hspan]
  let := d.residualSpan_elementary hSylow
  have he : IsElementaryAbelian 2 (normalClosure (Z : Set H)) := by
    rw [heq]
    exact IsElementaryAbelian.subgroupOf
      (d.residualSpan_le_D.trans (le_sup_left.trans le_sup_left))
  have hh := hZPr.normalClosure_of_sylow_le P (P : Subgroup H) le_rfl ZP
  rw [map_subgroupOf_eq_of_le hZP] at hh
  exact heq ▸ hh he

/-- All hypotheses of the faithful-membership direction of 1.2.10, on YT. -/
theorem residual_component_reduced_witness
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    Y L F ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) ∧
    B ∈ Chapter1.cComponentsIn (Y L F ⊔ (T : Subgroup G)) ∧
    IsPReduced 2 ((E F).subgroupOf (Y L F ⊔ (T : Subgroup G))) ∧
    ⁅E F, B⁆ ≠ ⊥ := by
  refine ⟨d.residual_sylowJoin_mem_HOver hSylow,
    residual_component_in_sylowJoin hB, d.residualSpan_reduced_sylowJoin hSylow, ?_⟩
  rw [commutator_comm]
  exact fun he => d.residual_component_not_centralizes hB
    (commutator_eq_bot_iff_le_centralizer.mp he)

/-- Apply the complete group-theoretic clauses (1–2) of 14.3.4.
Its separate module clause (3) is still required for the decomposition. -/
theorem residual_component_group_classification
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((B ⧸ pCore 2 B) ≃* Matrix.PSL3Two.PSL)) ∧
    (B.subgroupOf (B ⊔ (T : Subgroup G))).Normal ∧ B ∈ Chapter1.LStar G T := by
  obtain ⟨hl, hf⟩ := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T B).mp
    (d.residual_component_faithful hSylow hB)
  exact earlier B hl hf

/-- The actual ambient Sylow normalizes the component. -/
theorem residual_T_normalizes_component
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (T : Subgroup G) ≤ normalizer (B : Set G) :=
  le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left)).mp
      (d.residual_component_group_classification earlier hSylow hB).2.1)

omit d in
/-- The projection used by the marked component action has exactly the intrinsic two-core kernel. -/
theorem residual_component_projection_ker {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    ((QuotientGroup.mk' (pCore 2 (Y L F))).comp
      (inclusion (hB.1.trans J_le_Y))).ker = pCore 2 B := by
  have hBY := residual_component_in_Y hB
  have hcore := pCoreAmbient_mono_of_isSubnormalIn B (Y L F) 2 hBY.1 hBY.2.subnormal
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hb
    have hb' := (QuotientGroup.eq_one_iff (inclusion hBY.1 b)).mp hb
    have h := inf_pCoreIn_le_of_le 2 hBY.1
      ⟨b.property, mem_map_of_mem (Y L F).subtype hb'⟩
    obtain ⟨c, hc, he⟩ := h
    exact (B.subtype_injective he) ▸ hc
  · intro hb
    apply (QuotientGroup.eq_one_iff (inclusion hBY.1 b)).mpr
    obtain ⟨c, hc, he⟩ := hcore (mem_map_of_mem B.subtype hb)
    exact (show c = inclusion hBY.1 b from Subtype.ext he) ▸ hc

/-- The same kernel statement for the original representation, not a replacement action. -/
theorem residualComponentRepresentation_ker
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    let := (d.residualSpan_reduced hSylow).elementary
    (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y)).ker = pCore 2 B := by
  let := (d.residualSpan_reduced hSylow).elementary
  exact (MonoidHom.ker_comp_of_injective _ _ (d.residualRepresentation_faithful hSylow)).trans
    (residual_component_projection_ker hB)

/-- Ambient conjugation on every vector of the fixed marked module. -/
theorem residualComponentRepresentation_apply
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F) (b : B)
    (v : Additive ((E F).subgroupOf (Y L F))) :
    let := (d.residualSpan_reduced hSylow).elementary
    (((d.residualComponentRepresentation hSylow hBY b v).toMul : Y L F) : G) =
      (b : G) * ((v.toMul : Y L F) : G) * (b : G)⁻¹ :=
  d.residualRepresentation_apply hSylow (inclusion hBY b) v

/-- Invariants of the marked representation are the literal ambient centralizer in E. -/
theorem residualComponentRepresentation_mem_invariants
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hBY : B ≤ Y L F)
    (v : Additive ((E F).subgroupOf (Y L F))) :
    let := (d.residualSpan_reduced hSylow).elementary
    v ∈ (d.residualComponentRepresentation hSylow hBY).invariants ↔
      ((v.toMul : Y L F) : G) ∈ centralizer (B : Set G) := by
  let := (d.residualSpan_reduced hSylow).elementary
  constructor
  · intro hv b hb
    have h := congrArg (fun w : Additive ((E F).subgroupOf (Y L F)) =>
      ((w.toMul : Y L F) : G)) (hv (⟨b, hb⟩ : B))
    rw [d.residualComponentRepresentation_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hv b
    apply Subtype.ext
    apply Subtype.ext
    exact (d.residualComponentRepresentation_apply hSylow hBY b v).trans
      (mul_inv_eq_iff_eq_mul.mpr (hv b b.property))

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
