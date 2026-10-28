module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedUnitaryThree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearThree
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.QuadraticActor

/-!
# Projective exceptional components in the original local action

For each actual component of every original local, pass to its C L₁ T
reduction and retain the literal U_J/V₁ representation. Its quadratic
actor is faithful on the same component image. The proved B.4.2–5
projective obstructions exclude PSL₃(4) and PSU₃(8), including arbitrary
component centralizers and nonsplit module kernels. Transport uses the
intrinsic component two-core and its actual map into J/O₂(J).

The preceding Borel restrictions then exclude every contained nonbinary
projective linear-three or unitary-three component. Even-degree linear
components and odd-degree unitary components are excluded without a
containment premise. The special central covers and the remaining
outside-component module arguments still belong to 14.7.40–47.

Source: Aschbacher–Smith 14.7.41,43–44, printed pp.1061–1062,
refs/quasithin.pdf, using B.4.2–5 and F.9.18 on the original section.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original component quotient is neither PSL₃(4) nor PSU₃(8).
Normality, the reduced local and the faithful quadratic actor are all
constructed from the original source hypotheses. -/
theorem local_projective_exceptional_components_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    (¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4) ∧
      (¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 8) := by
  let K := C.map I.subtype
  have hK : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := K.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := KJ.map q
  obtain ⟨_,hJ,hKJ,hn,_,_,_,hnB,_,hU,a,_,A,_,hA,hquad,hcod,hfaith⟩ :=
    local_normal_component_quadratic_reduction d h hab structural previous faithful earlier
      I K hI (map_subtype_le _) hK
  let := hU
  let : B.Normal := hnB
  let ec : C ≃* KJ := (equivMapOfInjective C I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  let e : (C ⧸ pCore 2 C) ≃* B :=
    (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).trans
      (cComponentTwoCoreQuotientEquiv hKJ)
  have hs := local_star_sqtk h J hJ
  constructor
  · intro hm
    exact LinearThreeFour.Projective.no_quadratic_actor a.representation B (A.map q)
      hs (hm.of_mulEquiv e.symm) a.faithful hA hquad hcod hfaith
  · intro hm
    exact UnitaryEight.Projective.no_quadratic_actor a.representation B (A.map q)
      hs (hm.of_mulEquiv e.symm) a.faithful hA hquad hcod hfaith


/-- The contained projective linear-three branch of 14.7.41 is impossible:
the original Borel forces field four, excluded on the actual module. -/
theorem local_linearThree_contained_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : False := by
  have hn2 := local_linearThree_contained_field_four d h hab structural previous faithful
    earlier I hI C hC hin hE hn e
  exact (local_projective_exceptional_components_impossible d h hab structural previous
    faithful earlier I hI C hC).1 ⟨E,inferInstance,inferInstance,by simpa [hn2] using hE,⟨e⟩⟩

/-- Every even-degree nonbinary projective linear-three component is excluded,
without an assumed containment of the original point residual. -/
theorem local_even_linearThree_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E)) : False := by
  have hn2 := local_even_linearThree_component_field_four d h hab structural previous
    faithful earlier I hI C hC hE hn heven e
  exact (local_projective_exceptional_components_impossible d h hab structural previous
    faithful earlier I hI C hC).1 ⟨E,inferInstance,inferInstance,by simpa [hn2] using hE,⟨e⟩⟩

/-- The contained projective unitary-three branch of 14.7.41 is impossible:
the original Borel forces field eight, excluded on the actual module. -/
theorem local_unitaryThree_contained_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  have hn3 := local_unitaryThree_contained_field_eight d h hab structural previous faithful
    earlier I hI C hC hin J hn hE hconj e
  exact (local_projective_exceptional_components_impossible d h hab structural previous
    faithful earlier I hI C hC).2 ⟨E,inferInstance,inferInstance,J,
      by simpa [hn3] using hE,by simpa [hn3] using hconj,⟨e⟩⟩

/-- Every odd-degree nonbinary projective unitary-three component is excluded,
with original point containment supplied by the three-rank argument. -/
theorem local_odd_unitaryThree_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n)) (hodd : Odd n)
    (e : (C ⧸ pCore 2 C) ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    False := by
  have hin := local_odd_unitaryThree_contains_point d h hab structural previous
    faithful earlier I hI C hC J hn hE hconj hodd e
  exact local_unitaryThree_contained_impossible d h hab structural previous faithful
    earlier I hI C hC hin J hn hE hconj e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
