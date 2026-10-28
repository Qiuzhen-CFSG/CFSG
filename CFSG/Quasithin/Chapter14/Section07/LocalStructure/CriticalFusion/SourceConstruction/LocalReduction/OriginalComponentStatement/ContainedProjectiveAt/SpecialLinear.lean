module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.ProjectiveExceptions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.LinearModule
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.RankBound

/-!
# Same-group SpecialLinearExclusion source

The original proof is replayed with Structural1222At and Theorem12213At
on the same G,T. Actual component, quotient and module maps are retained.
Source: Aschbacher--Smith 14.7.41--44, printed pp.1061--1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3FourNaturalDual
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original critical denominator contradicts the actual natural-plus-dual
module, retaining both its rank comparison and its single commutator line. -/
theorem reduced_special_linearThree_four_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* SL)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) : False := by
  classical
  have hfield : Nat.card Representation.SL3FourNaturalDual.F = 2^2 := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    rfl
  obtain ⟨_,hAn,_,hCN,_⟩ := local_even_special_linearThree_center_and_inverter_at
    d h hab structural previous faithful earlier I hI C hC hfield (by decide) e
  let := hCN
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let : B.Normal := hCN.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨eB,E,hE⟩ := reduced_special_linearThree_four_coordinates_at
    d h hab structural previous faithful earlier I hI C hC e hgen a
  have hdim : 2 < Module.finrank (ZMod 2)
      (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
    rw [E.finrank_eq,finrank_space]
    decide
  let D := Chapter12.Section09.NaturalSource.naturalF9Setup F L I
  let hf := WholeResidualAssembly.GuardedSource.local_f9_hypothesis h hab structural previous I hI
  let : IsElementaryAbelian 2 D.UH := inferInstanceAs (IsElementaryAbelian 2 (F.UH I))
  obtain ⟨c⟩ := WholeResidualAssembly.GuardedSource.local_normal_point_selected_endpoint h hab structural previous I hI hAn a hdim
  have hb := (WholeResidualAssembly.GuardedSource.local_f9_critical_bounds h hab structural previous I hI).1
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  have hshape := QuadraticActors.criticalShapes_of_equivariant_unbounded a.representation
    a.faithful B eB E hE (actorImage I (c.endpoint.conjugate D.UH))
    c.quadratic.1 c.quadratic.2.1 c.quadratic.2.2
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono hf.plus_le le_rfl
  have hBH : c.endpoint.conjugate D.UH ≤ I :=
    (map_mono hUV).trans (c.endpoint.large_le hb)
  have hreverse : D.UH ≤ I.map (MulAut.conj c.endpoint.representative).toMonoidHom :=
    hUV.trans (c.endpoint.reverse_le hb)
  have hline := s.critical_line_displacement_of_conjugate (c.endpoint.conjugate D.UH)
    c.endpoint.representative hreverse hf.point_card
  obtain ⟨z,hz⟩ := (finrank_le_one_iff (K := ZMod 2)).mp hline.1
  apply critical_obstruction a.representation (actorImage I (c.endpoint.conjugate D.UH))
    hshape (s.image (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁))) z.val
  · have hdq := s.quotient_finrank
      (commutatorPreimage D.UH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁))
      (s.line_le_DH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁) hBH)
    exact hdq.le.trans c.comparison
  · intro x hx v hv
    have hm := hline.2 x hx v hv
    obtain ⟨b,hb⟩ := hz ⟨a.representation x v-v,hm⟩
    exact Submodule.mem_span_singleton.mpr ⟨b,congrArg Subtype.val hb⟩

/-- Apply the SL₃(4) contradiction to every original component through its
constructed C L₁ T local and literal intrinsic two-core quotient. -/
theorem local_special_linearThree_four_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* SL) : False := by
  have hfield : Nat.card Representation.SL3FourNaturalDual.F = 2^2 := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    rfl
  have hin := (local_even_special_linearThree_center_and_inverter_at
    d h hab structural previous faithful earlier I hI C hC hfield (by decide) e).1
  let K := C.map I.subtype
  have hK : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := K.subgroupOf J
  have hnC := (local_even_special_linearThree_center_and_inverter_at
    d h hab structural previous faithful earlier I hI C hC hfield (by decide) e).2.2.2.choose
  have hnK : (K.subgroupOf I).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hnC
  obtain ⟨_,hJ,hKJ,_,_,_,_,_,_,hU,a,_⟩ := normal_component_quadratic_reduction_at
    h hab structural previous faithful I K hI (map_subtype_le _) hK hnK
  let := hU
  let ec : C ≃* KJ := (equivMapOfInjective C I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  let eJ := (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).symm.trans e
  have heJ : K ⊔ (T : Subgroup G) = J := by
    change K ⊔ (T : Subgroup G) = K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
    rw [←sup_assoc,sup_eq_left.mpr hin]
  have hgen : KJ ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right.trans le_sup_right),heJ,subgroupOf_self]
  exact reduced_special_linearThree_four_impossible_at
    d h hab structural previous faithful earlier J hJ KJ hKJ eJ hgen a

/-- Exclude the source SL₃(4) row over any actual four-element field. -/
theorem local_special_linearThree_four_not_isSL_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 4 := by
  rintro ⟨Q,hQ,hfin,hcard,⟨e⟩⟩
  let := Fintype.ofFinite Q
  let eF : Q ≃+* Representation.SL3FourNaturalDual.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hcard,SL2FourNatural.card_field])
  exact local_special_linearThree_four_impossible_at d h hab structural previous faithful
    earlier I hI C hC (e.trans (Atlas.fieldEquivSL 3 eF))

/-- The actual Borel forces field four in every even-degree nonbinary SL₃
row; its natural-plus-dual module then gives the original contradiction. -/
theorem local_even_special_linearThree_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2^n) (hn : 1 < n) (heven : Even n)
    (e : (C ⧸ pCore 2 C) ≃* SL(3,E)) : False := by
  have hn2 := (local_even_special_linearThree_graph_at d h hab structural previous faithful
    earlier I hI C hC hE hn heven e).1
  exact local_special_linearThree_four_not_isSL_at d h hab structural previous faithful earlier
    I hI C hC ⟨E,inferInstance,inferInstance,by simpa [hn2] using hE,⟨e⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
