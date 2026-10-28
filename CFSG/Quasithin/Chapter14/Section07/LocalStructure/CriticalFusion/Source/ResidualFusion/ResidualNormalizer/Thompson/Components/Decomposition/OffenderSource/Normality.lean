module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.OffenderSource.Structure
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.ElementaryThompsonComponentGeneration

/-!
# Source normality and Thompson generation in N_G(K)

A C-component B of J(Y) lies in D. Restriction to D and normality of D in
N_G(K) make B a C-component of that full normalizer. The earlier 14.3.4
classification makes its two-core image an ordinary quasisimple component.
The original QTKE hypothesis bounds every odd prime rank of N_G(K)/O₂.
The given Sylow T normalizes B, so the component orbit bound proves B normal
in N_G(K). Solvable-quotient reflection returns this to the original B.

Now Sylow-conjugate generation of J(Y) gives [B,J(R₁)] = B. The literal
best-offender bridge consequently gives BP ≤ Q. Combining these results
with Structure leaves precisely O₂(Q)=1 to establish for the proposed actor.
The final conditional theorem applies the complete six-clause B.5.1 contract
to the same action on E. It does not claim the source application before the
two-core premise is discharged. The genuine universal earlier inputs retain
their producers qt-14-03-prelim (14.3.4) and qt-b05-quasisimple (B.5.1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070 (PDF p.1087), A.3.8(3), and B.5.1.
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

/-- First restrict from Y to D, then use D's relative normality in N_G(K). -/
theorem residual_component_in_normalizer {B : Subgroup G}
    (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B ∈ Chapter1.cComponentsIn (normalizer (K F : Set G)) := by
  let N := normalizer (K F : Set G)
  have hBD := residual_component_le_D hB
  have hD : (B.subgroupOf (D F)).IsCComponent :=
    (residual_component_in_Y hB).2.subgroupOf_of_le hBD le_sup_left
  have hn : ((D F).subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer normalizer_K_normalizes_D
  have hh := (hD.map_equiv (subgroupOfEquivOfLe D_le_normalizer).symm).map_subtype hn.isSubnormal
  have hf : ((D F).subgroupOf N).subtype.comp
      (subgroupOfEquivOfLe (D_le_normalizer (F := F))).symm.toMonoidHom =
      inclusion D_le_normalizer := by ext; rfl
  rw [map_map, hf] at hh
  have he : (B.subgroupOf (D F)).map (inclusion (D_le_normalizer (F := F))) =
      B.subgroupOf N := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      exact ⟨⟨b, hBD hb⟩, hb, rfl⟩
  exact ⟨hBD.trans D_le_normalizer, he ▸ hh⟩

include d

/-- Characteristic two and the original nonidentity point make the normalizer
 a subgroup of a proper two-local, so the original QTKE hypothesis applies. -/
theorem residual_normalizer_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (K F : Set G)) := by
  let N := normalizer (K F : Set G)
  have hcore : N.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hc : pCore 2 N = ⊥ := (map_eq_bot_iff_of_injective _ N.subtype_injective).mp hz
    let z : N := ⟨d.z, D_le_normalizer (d.point_le_D (by rw [d.point]; exact mem_zpowers _))⟩
    have hm : z ∈ pCore 2 N := d.residual_normalizer_characteristicTwo (by
      rw [hc]
      intro a ha
      rw [mem_bot.mp ha]
      simp)
    have hz1 : z = 1 := mem_bot.mp (hc ▸ hm)
    exact d.z_ne_one (congrArg N.subtype hz1)
  have hlocal : IsTwoLocal (normalizer (N.pCoreIn 2 : Set G)) :=
    ⟨N.pCoreIn 2, hcore, isPGroup_pCoreIn 2 N, rfl⟩
  have hs := d.counterexample.qtke.twoLocal_sqtk hlocal
  have hNN : N ≤ normalizer (N.pCoreIn 2 : Set G) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hNN)).mp (hs.subgroup _)

/-- The source normality in the full N_G(K), not just in BT. -/
theorem residual_component_normal_in_normalizer
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (B.subgroupOf (normalizer (K F : Set G))).Normal := by
  let N := normalizer (K F : Set G)
  let C := B.subgroupOf N
  have hBN := residual_component_in_normalizer hB
  let q := QuotientGroup.mk' (pCore 2 N)
  let Cbar := C.map q
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  let : IsQuasisimple (residualOffenderComponent (L := L) (F := F) B) :=
    d.residualOffenderComponent_quasisimple earlier hSylow hB
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (residualComponentOffenderEquiv hB).symm
  let e : (C ⧸ pCore 2 C) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBN.1) (pCore_map_iso 2 _)
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple Cbar := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hBN.2)
  have hbar : IsComponent (N ⧸ pCore 2 N) Cbar :=
    ⟨(hBN.2.map_quotient (pCore 2 N)).subnormal, inferInstance⟩
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  let S : Sylow 2 N := T.subtype hTN
  have hSC : (S : Subgroup N) ≤ normalizer (C : Set N) := by
    rw [← subgroupOf_normalizer_eq hBN.1]
    exact comap_mono (d.residual_T_normalizes_component earlier hSylow hB)
  have hs : ((S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))) :
      Subgroup (N ⧸ pCore 2 N)) ≤ normalizer (Cbar : Set (N ⧸ pCore 2 N)) :=
    (map_mono hSC).trans (le_normalizer_map q)
  have hnormal : Cbar.Normal := hbar.normal_of_sylow_normalizes_of_odd_rank_le_two
    (fun p hp ho => by
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 N) pCore_isPGroup).trans
        (d.residual_normalizer_sqtk.stronglyQuasithin p hp ho)) _ hs
  exact cComponent_normal_of_quotient_normal hBN.2 (pCore 2 N) hnormal

/-- Global Thompson generation and relative normality give the exact source commutator. -/
theorem residual_component_commutator_sylowThompson
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    ⁅B, Stellmacher.elementaryAbelianMaxJ (F.Ri L 1)⁆ = B := by
  have hBN := residual_component_in_normalizer hB
  have hn := (normal_subgroupOf_iff_le_normalizer hBN.1).mp
    (d.residual_component_normal_in_normalizer earlier hSylow hB)
  let : (B.subgroupOf (Y L F)).Normal :=
    normal_subgroupOf_of_le_normalizer (residual_Y_le_normalizer_K.trans hn)
  have hBY : B ≤ Y L F := hB.1.trans J_le_Y
  have hBJ : B.subgroupOf (Y L F) ≤ Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (Y L F)) := by
    apply (map_le_map_iff_of_injective (Y L F).subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hBY,
      ← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hB.1
  obtain ⟨S, hS⟩ := hSylow
  have hh := congrArg (map (Y L F).subtype)
    (Stellmacher.normal_cComponent_commutator_maxJ S (residual_component_in_Y hB).2 hBJ)
  rwa [map_commutator, map_subgroupOf_eq_of_le hBY,
    ← Stellmacher.elementaryAbelianMaxJ_map_injective _ (Y L F).subtype_injective, hS] at hh

/-- The original component is contained in the literal offender actor,
 with Thompson commutator generation now discharged. -/
theorem residual_component_le_offender
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    residualOffenderComponent (L := L) (F := F) B ≤ d.residualOffenderSubgroup hSylow B :=
  d.residualOffenderComponent_le_of_commutator hSylow hB
    (d.residual_component_commutator_sylowThompson earlier hSylow hB)

/-- All source-input fields except the remaining two-core calculation are now
 discharged on the literal offender group. -/
theorem offenderSourceInput_of_twoCore
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hcore : pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥) :
    OffenderSourceInput d KnownSimple.IsKnownSimple hSylow hB :=
  d.offenderSourceInput_of_source_facts earlier hSylow hB
    (d.residual_component_normal_in_normalizer earlier hSylow hB)
    (d.residual_component_commutator_sylowThompson earlier hSylow hB) hcore

/-- The complete B.5.1 conclusion on the original E-action, with only the
 source two-core calculation and the genuine earlier universal inputs explicit. -/
theorem offenderSourceClassification_of_twoCore
    (classification : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hcore : pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((d.residualOffenderAction hSylow B).comp (d.residualOffenderSubgroup hSylow B).subtype)
      ((residualOffenderComponent (L := L) (F := F) B).subgroupOf
        (d.residualOffenderSubgroup hSylow B))) :=
  d.offenderSourceClassification classification hSylow hB
    (d.offenderSourceInput_of_twoCore earlier hSylow hB hcore)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
