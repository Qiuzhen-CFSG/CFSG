module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.Movement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.ModuleSelection

/-!
# Original linear-five exclusion and the symmetric-eight source reduction

The original component models supply point-core movement, so the established
inner exclusion has its core-commutator input. The actual invariant minimal
parabolic excludes degree five. In degree four it constructs the symmetric
eight quotient and the middle parabolic; the complete ambient irreducible
catalogue then selects the natural six-space on the actual maximal quotient.
No quotient marking, parabolic, seed action, or core commutator is an input.

The same movement argument also discharges the alternating-six row.
The degree-four conclusion remains a natural proper quotient. Fixation of
its stabilizer through a general noncentral module kernel is not asserted.
Source: Aschbacher–Smith 14.7.49 and 14.7.51, printed pp.1064–1065.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open AlternatingSevenSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original alternating-six row, with core movement supplied by its
intrinsic quotient order and the actual point component. -/
theorem source_14_7_49_alternating_six_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have hlarge : 168 < Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hm := local_large_component_plane_moved_at d h hab structural previous faithful
    earlier source47 I hI C hC hlarge
  have hc := core_commutator_eq_point_of_plane_moved h hab hm
  have hgen := (local_component_eq_residual_at d h hab structural previous faithful
    earlier source47 I hI C hC).2.1
  exact (InnerLinearExclusion.Guarded.local_relative_component_small_inner_rows
    h hab structural previous faithful source47 hc I hI C hC
    (source47 I hI C hC).1 hgen.symm).2.1 ⟨e⟩

/-- The original linear-five row is excluded without any supplied
core-commutator or noninner-action premise. -/
theorem source_14_7_51_linear_five_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  rintro ⟨e⟩
  have hc := (local_linear_graph_movement_at d h hab structural previous faithful
    earlier source47 I hI C hC 5 (Or.inr rfl) e).2
  exact local_five_impossible_at d h hab structural previous faithful earlier source47
    hc I hI C hC e

/-- Every selected ambient irreducible proper quotient of the original
linear-four local is its marked symmetric-eight natural six-space.
The quotient marking and middle parabolic are constructed internally. -/
theorem local_four_quotient_natural_marking_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hirr : IsIrreducible N.quotientRepresentation)
    (hq : BinaryOffender.quadraticRatio N.quotientRepresentation ≤ 2) :
    ∃ b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8),
      (C.map (QuotientGroup.mk' (pCore 2 I))).map b.toMonoidHom = alternatingGroup (Fin 8) ∧
      IsEightNatural N.quotientRepresentation b := by
  have hc := (local_linear_graph_movement_at d h hab structural previous faithful
    earlier source47 I hI C hC 4 (Or.inl rfl) e).2
  obtain ⟨b,_,hb⟩ := local_four_symmetric_marking_at d h hab structural previous faithful
    earlier source47 hc I hI C hC e
  obtain ⟨eK,P,A,B,hAB,hA,hB,hP,hLP,hPE⟩ := local_four_middle_parabolic_at
    d h hab structural previous faithful earlier source47 hc I hI C hC e
  exact ⟨b,hb,local_symmetric_eight_quotient_natural_at d h hab structural previous
    faithful earlier source47 I hI C hC a N hN hirr hq b eK hb P A B hAB hA hB hP hLP hPE⟩

/-- The actual maximal quotient in the remaining original degree-four row:
its carrier is U_I/V₁ modulo a maximal invariant subspace, its whole actor
is faithful and irreducible, and its marked module is the natural six-space. -/
theorem local_four_exists_natural_quotient_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
        (N : Subrepresentation a.representation)
        (b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8)),
        BinaryOffender.quadraticRatio a.representation ≤ 2 ∧ IsCoatom N ∧
        IsIrreducible N.quotientRepresentation ∧
        Function.Injective N.quotientRepresentation ∧
        BinaryOffender.quadraticRatio N.quotientRepresentation ≤ 2 ∧
        (C.map (QuotientGroup.mk' (pCore 2 I))).map b.toMonoidHom = alternatingGroup (Fin 8) ∧
        IsEightNatural N.quotientRepresentation b := by
  obtain ⟨hU,hr⟩ := local_exists_faithful_irreducible_quotient_at
    d h hab structural previous faithful earlier source47 I hI C hC
  let := hU
  obtain ⟨a,ha,N,hN,hirr,hf,hq⟩ := hr
  obtain ⟨b,hb,hn⟩ := local_four_quotient_natural_marking_at d h hab structural previous
    faithful earlier source47 I hI C hC e a N hN.ne_top hirr hq
  exact ⟨hU,a,N,b,ha,hN,hirr,hf,hq,hb,hn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
