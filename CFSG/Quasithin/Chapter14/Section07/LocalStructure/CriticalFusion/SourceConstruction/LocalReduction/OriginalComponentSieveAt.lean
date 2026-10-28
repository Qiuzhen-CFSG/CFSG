module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentCatalogueAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.At
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryRankContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.RankTwoExceptionsAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Special
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.TripleAlternatingSix
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.MathieuSourceAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt.Escape
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.ComponentStatement
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The original component sieve with only the binary rank-one row remaining

Apply the actual component catalogue to the literal C/O₂(C). The genuine
same-group source exclusions remove every nonbinary projective, special,
rank-two, and exceptional-cover alternative. Explicit binary coefficient
and derived-group equivalences identify the surviving carriers, and the
proved source containment theorems place the original point in each one.

The conclusion deliberately retains the binary PSL₂(2ⁿ) alternative. It is
an unconditional intermediate towards 14.7.47, not the full component
statement, and assumes no part of that later statement. All earlier
structural inputs concern the original group and Sylow subgroup.
Source: Aschbacher–Smith 14.7.30,36,40–47, printed pp.1055–1063,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components OriginalComponentStatement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem binary_linear_equiv {X : Type*} [Group X] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X n 2) : Nonempty (X ≃* SL(n,ZMod 2)) := by
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
  exact ⟨e.trans ((Atlas.fieldEquivPSL n (Atlas.G2.binaryFieldEquiv hE)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL hn))⟩

private def ambientCoreEquiv (I : Subgroup G) (C : Subgroup I) :
    (C ⧸ pCore 2 C) ≃* (C.map I.subtype ⧸ pCore 2 (C.map I.subtype)) :=
  QuotientGroup.congr _ _ (equivMapOfInjective C I.subtype I.subtype_injective)
    (pCore_map_iso 2 (equivMapOfInjective C I.subtype I.subtype_injective))

/-- Every actual original component either has a binary PSL₂ quotient, or
contains the original point residual and has one of the permitted carriers. -/
theorem local_component_binary_rank_one_or_rows_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2^n)) ∨
      (F.Li L 1 ≤ C.map I.subtype ∧ WholeResidualAssembly.ComponentRows (C ⧸ pCore 2 C)) := by
  have hm := local_component_catalogue_at d h hab structural previous faithful earlier I hI C hC
  cases hm with
  | linear_two n hn he => exact Or.inl ⟨n,hn,he⟩
  | projective_three unitary n hn he =>
    cases unitary with
    | false =>
      change ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2^n) at he
      have hn1 : 1 ≤ n := hn
      by_cases hn2 : 1 < n
      · exact (OutsideProjectiveAt.local_nonbinary_linearThree_model_impossible_at
          d h hab structural previous faithful earlier I hI C hC n hn2 he).elim
      · have hn' : n = 1 := by omega
        subst n
        obtain ⟨e⟩ := binary_linear_equiv (by decide : 0 < 3) (by simpa using he)
        refine Or.inr ⟨?_,Or.inl ⟨3,by decide,by decide,⟨e⟩⟩⟩
        exact local_binaryThree_component_contains_point_at d h hab structural previous
          faithful earlier I hI C hC (e.trans Matrix.PSL3Two.equiv)
    | true =>
      exact (OutsideProjectiveAt.local_nonbinary_unitaryThree_model_impossible_at
        d h hab structural previous faithful earlier I hI C hC n hn he).elim
  | special_three unitary n hn hm he =>
    exact (ContainedProjectiveAt.local_special_three_catalogue_impossible_at
      d h hab structural previous faithful earlier I hI C hC unitary n hn hm he).elim
  | symplectic n hn he =>
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := he
    by_cases hn2 : 2 ≤ n
    · let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hE
      exact (local_symplecticFour_component_impossible_at d h hab structural previous faithful
        earlier I hI C hC hE (by omega)
        (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hE hn2))).elim
    · have hn1 : n = 1 := by omega
      let eA := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (by simpa [hn1] using hE))
      exact Or.inr ⟨local_binary_alternating_component_contains_point_at h hab structural previous
        faithful I hI C hC (Or.inl rfl) eA,Or.inr (Or.inl ⟨6,by decide,by decide,⟨eA⟩⟩)⟩
  | g2 n hn he =>
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := he
    by_cases hn2 : 2 ≤ n
    · let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hE
      exact (local_gTwo_component_impossible_at d h hab structural previous faithful
        earlier I hI C hC hE (by omega)
        (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hE))).elim
    · have hn1 : n = 1 := by omega
      let eG := e.trans (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv
        (Atlas.G2.binaryFieldEquiv (by simpa [hn1] using hE)))
      exact Or.inr ⟨local_binary_gTwo_component_contains_point_at h hab structural previous
        faithful I hI C hC eG,Or.inr (Or.inr ⟨eG⟩)⟩
  | linear_four he =>
    obtain ⟨e⟩ := binary_linear_equiv (by decide : 0 < 4) he
    exact Or.inr ⟨local_binary_linear_component_contains_point_at h hab structural previous
      faithful I hI C hC (Or.inl rfl) e,Or.inl ⟨4,by decide,by decide,⟨e⟩⟩⟩
  | linear_five he =>
    obtain ⟨e⟩ := binary_linear_equiv (by decide : 0 < 5) he
    exact Or.inr ⟨local_binary_linear_component_contains_point_at h hab structural previous
      faithful I hI C hC (Or.inr rfl) e,Or.inl ⟨5,by decide,by decide,⟨e⟩⟩⟩
  | alternating_seven he =>
    obtain ⟨e⟩ := he
    exact Or.inr ⟨local_binary_alternating_component_contains_point_at h hab structural previous
      faithful I hI C hC (Or.inr rfl) e,Or.inr (Or.inl ⟨7,by decide,by decide,⟨e⟩⟩)⟩
  | alternating_six_cover he =>
    obtain ⟨e⟩ := he
    exact (local_triple_alternatingSix_component_impossible_at d h hab structural previous
      faithful earlier I hI C hC e).elim
  | mathieu he =>
    obtain ⟨e⟩ := he
    have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
      simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
    exact (local_mathieu_component_impossible_at d h hab structural previous faithful earlier
      I (C.map I.subtype) hI (map_subtype_le C) hC'
      ⟨(ambientCoreEquiv I C).symm.trans e⟩).elim
  | mathieu_cover he =>
    obtain ⟨e⟩ := he
    have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
      simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
    exact (TripleMathieuSourceAt.local_triple_mathieu_component_impossible_at
      d h hab structural previous faithful earlier I (C.map I.subtype) hI (map_subtype_le C) hC'
      ⟨(ambientCoreEquiv I C).symm.trans e⟩).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
