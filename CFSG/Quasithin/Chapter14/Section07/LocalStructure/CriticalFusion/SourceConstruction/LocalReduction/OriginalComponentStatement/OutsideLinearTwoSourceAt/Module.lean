module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideSymmetric
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Actions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideReductionAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Seed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoModule

/-!
# Field four and rank eight in the original outside linear-two section

The original Borel fixes a nonzero seed in an actual irreducible quotient
retaining the normal component. The point cubic and its centralizing
inverter make the FF multiplicity theorem apply to this same quotient.
The natural alternative contradicts the fixed seed, leaving field four
and an alternating-five constituent in the multiplicity space. Doubling
that space gives rank at least eight in the original literal U_I/V₁.
Source: Aschbacher–Smith 14.7.42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual original reduced section has field degree two and rank at least eight. -/
theorem local_reduced_field_four_rank_ge_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G))
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(2,E)) :
    n = 2 ∧ ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ _a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        8 ≤ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  obtain ⟨hnorm,_,s,hsc,hsi⟩ := local_linearTwo_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout hE hn e
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro z hz
    apply e.injective
    rw [map_one]
    have hez : e z ∈ center PSL(2,E) := by
      apply mem_center_iff.mpr
      intro x
      obtain ⟨y,rfl⟩ := e.surjective x
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hz y)
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot,mem_bot] using hez
  let q := QuotientGroup.mk' (pCore 2 I)
  let K := C.map q
  let X := ((F.Li L 1).subgroupOf I).map q
  obtain ⟨hpoint,hKn,hXn,hK,hcard,hcomm,_,_,hcommon⟩ :=
    OutsideActors.local_structure_at d h hab structural previous
      faithful earlier I hI C hC hgen hnorm hz
  let := hpoint
  let : K.Normal := hKn
  let : X.Normal := hXn
  let : IsQuasisimple K := hK.2
  have hzK : center K = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr (cComponentTwoCoreQuotientEquiv hC).symm ⟨k,hk⟩).property
    change (cComponentTwoCoreQuotientEquiv hC).symm k ∈ center (C ⧸ pCore 2 C) at hh
    rw [hz,mem_bot] at hh
    exact (cComponentTwoCoreQuotientEquiv hC).symm.map_eq_one_iff.mp hh
  have hcent : X ≤ centralizer (K : Set (HStar I)) := by
    intro x hx k hk
    exact (hcomm ⟨k,hk⟩ ⟨x,hx⟩).eq
  obtain ⟨σ,_,hσ,hmark⟩ := outside_symmetric_embedding I C hC (F.Li L 1)
    (F.Li_one_le_of_mem_Hz hI) (T : Subgroup G) (F.sylow_le_of_mem_Hz hI)
    T.isPGroup' hgen hcent hzK hcard ⟨s,F.sylow_le_of_mem_Hz hI s.property⟩
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) s.property)
    hsc hsi
  obtain ⟨hU,a,hratio⟩ := WholeResidualAssembly.local_quadratic_bound_at h structural hab I hI
  let := hU
  obtain ⟨N,hN,hirr,hretain⟩ := OutsideProjectiveAt.local_component_irreducible_quotient_at
    h hab structural previous faithful I hI C hC a
  have hmove := OutsideActors.local_point_movement_at h I (F.Li_one_le_of_mem_Hz hI) hpoint a
  obtain ⟨hfaith,hfull,hqratio⟩ := OutsideModule.retained_quotient a.representation K X
    hcard hcommon σ hmark hmove N hretain hratio
  obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff N.quotientRepresentation).mp hqratio
  let : Finite (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) :=
    Finite.of_surjective N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective
  obtain ⟨S,v,hv,hfix⟩ := local_borel_residual_fixed_seed_at
    d h hab structural previous faithful earlier I hI C hout a N hN.ne_top
  obtain ⟨hn2,hdim⟩ := OutsideLinearTwoModule.field_four_and_dimension_ge_eight
    N.quotientRepresentation hfaith hirr K X (local_star_sqtk h I hI) hcard hcommon σ
    (fun k t => hσ ⟨t,rfl⟩ k k.property) hmark hfull A hA hquad hbound
    (by omega) hE ((cComponentTwoCoreQuotientEquiv hC).symm.trans e) S v hv hfix
  exact ⟨hn2,hU,a,hdim.trans N.toSubmodule.finrank_quotient_le⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
