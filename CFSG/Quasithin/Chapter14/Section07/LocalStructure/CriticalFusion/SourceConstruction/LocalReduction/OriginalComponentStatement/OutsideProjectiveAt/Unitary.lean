module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveNormalityAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideSymmetric
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.UnitaryActions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideReductionAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Quotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule.Unitary

/-!
# The actual outside even-degree unitary component is impossible

The original component and point actions supply the normal cubic and its
centralizing inverter in the same local two-core quotient. A quotient of
the literal original module is chosen retaining the component action.
Its faithful quadratic multiplicity action contradicts the unitary FF
classification. No action, quotient, cubic, or module model is supplied
by the caller. All structural inputs concern the original group and Sylow only.
Source: Aschbacher–Smith 14.7.42–43, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The reduced original local has no outside even-degree unitary-three component. -/
theorem local_reduced_outside_even_unitary_impossible_at
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
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  obtain ⟨hnorm,_,s,hsc,hsi⟩ := unitary_component_normalizes_point_at
    d h hab structural previous faithful earlier I hI C hout J hn hE hconj e
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    have hze := HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by omega : 0 < n) hE hconj
    apply bot_unique
    intro z hz
    have hh := (centerCongr e ⟨z,hz⟩).property
    change e z ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hh
    rw [hze,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
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
  obtain ⟨N,_,_,hretain⟩ := local_component_irreducible_quotient_at
    h hab structural previous faithful I hI C hC a
  have hmove := OutsideActors.local_point_movement_at h I (F.Li_one_le_of_mem_Hz hI) hpoint a
  obtain ⟨hfaith,hfull,hqratio⟩ := OutsideModule.retained_quotient a.representation K X
    hcard hcommon σ hmark hmove N hretain hratio
  obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff N.quotientRepresentation).mp hqratio
  let : Finite (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) :=
    Finite.of_surjective N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective
  exact OutsideModule.outside_even_unitary_false N.quotientRepresentation hfaith K X
    hcard hcommon σ (fun k t => hσ ⟨t,rfl⟩ k k.property) hmark hfull A hA hquad hbound
    hzK (local_star_sqtk h I hI) J (by omega) heven
    (by simpa only [pow_mul,Nat.mul_comm] using hE) hconj
    ((cComponentTwoCoreQuotientEquiv hC).symm.trans e)

/-- Every original local excludes an outside even-degree unitary-three
component, with the actual reduced local and module constructed internally. -/
theorem local_outside_even_unitary_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  let : C.Normal := local_projective_unitaryThree_normal_at d h hab structural previous
    faithful earlier I hI C hC J (by omega) hE hconj e
  obtain ⟨I',_,hI',C',hC',hCN,_,hgen,hout',_,_,⟨ec⟩⟩ :=
    local_outside_normal_component_reduction_at h structural I hI C hC hout
  let := hCN
  exact local_reduced_outside_even_unitary_impossible_at d h hab structural previous faithful earlier
    I' hI' C' hC' hout' hgen J hn heven hE hconj (ec.symm.trans e)

/-- The packaged outside PSU-three row of every even nonbinary field degree
is excluded under the original hypotheses. -/
theorem local_outside_even_unitary_model_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 (2^n) := by
  rintro ⟨E,hEf,hEfin,J,hE,hconj,⟨e⟩⟩
  exact local_outside_even_unitary_impossible_at d h hab structural previous faithful earlier
    I hI C hC hout J hn heven hE hconj e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
