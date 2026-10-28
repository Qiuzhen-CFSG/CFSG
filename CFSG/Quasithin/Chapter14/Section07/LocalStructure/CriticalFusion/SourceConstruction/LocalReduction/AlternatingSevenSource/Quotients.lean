module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Marking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import Theory.Representation.SimpleNormalFaithfulQuotient
public import Theory.Representation.BinaryConjugationSection.FullMovement
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Faithful irreducible quotients of the original local span

Source 14.7.48 gives [U_I,C]=U_I for every actual component C of a local
I in H_z. The conjugation coordinates identify this with full movement by
the literal image of C in I/O₂(I). That image is simple and has trivial
centralizer. Consequently every proper invariant quotient is faithful.
Choosing a maximal invariant subspace gives the faithful irreducible
quotient used at the beginning of 14.7.50, and the original quadratic
actor supplies the same bound on the quotient.

All earlier inputs are at the original G,T. No irreducible action,
quotient faithfulness or module marking is an additional source premise.
The component classification remains Earlier14747, whose producer is
qt-d-14752-local-reduction. The dimension dichotomy and row exclusions
are not asserted by this module.

Source: Aschbacher–Smith 14.7.48(2) and 14.7.50, printed p.1064,
refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def actionSection {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z) :
    BinaryConjugationSection I U Z
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
    map_one' := (QuotientGroup.mk' (Z.subgroupOf U)).map_one
    map_mul' := (QuotientGroup.mk' (Z.subgroupOf U)).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := QuotientGroup.ker_mk' _
  equivariant i u := (a.conjugation i u).symm

/-- Source 14.7.48(2), transported to the actual quotient module and component image. -/
theorem local_module_fully_moved_at
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
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    subspaceCommutator a.representation ⊤
      (C.map (QuotientGroup.mk' (pCore 2 I))) = ⊤ := by
  have hm := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).2.2
  have hh := (actionSection a).subspaceCommutator_eq_top_of_movement
    (C.map I.subtype) (map_subtype_le C) (by
      rw [commutator_comm,hm]
      exact (sup_eq_left.mpr a.kernel_le).symm)
  have he : (C.map I.subtype).subgroupOf I = C := by
    exact comap_map_eq_self_of_injective I.subtype_injective C
  rw [he,subspaceCommutator_comp_map] at hh
  exact hh

/-- Every proper invariant quotient retains the faithful original local actor.
This is stronger than the maximal-quotient faithfulness needed in 14.7.50,
and follows from the already proved simple component and full movement. -/
theorem local_proper_quotient_faithful_at
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
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤) :
    Function.Injective N.quotientRepresentation := by
  have hr := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  let : C.Normal := hr ▸ inferInstance
  let B := C.map (QuotientGroup.mk' (pCore 2 I))
  let : B.Normal := (inferInstance : C.Normal).map _ (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup B := ((source47 I hI C hC).2.of_equiv
    (cComponentTwoCoreQuotientEquiv hC)).isSimpleGroup
  exact quotient_faithful_of_simple_normal_full_movement a.representation B
    (local_unique_component_and_fitting_at d h hab structural previous faithful earlier
      source47 I hI C hC).2.2
    (local_module_fully_moved_at d h hab structural previous faithful earlier source47
      I hI C hC a) N hN

/-- The opening maximal-quotient construction of 14.7.50, with its actual
U_I/V₁ carrier and inherited quadratic bound. No quotient, action or
faithfulness premise is supplied by the caller. -/
theorem local_exists_faithful_irreducible_quotient_at
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
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ N : Subrepresentation a.representation, IsCoatom N ∧
          IsIrreducible N.quotientRepresentation ∧
          Function.Injective N.quotientRepresentation ∧
          quadraticRatio N.quotientRepresentation ≤ 2 := by
  obtain ⟨hU,a,ha⟩ := local_quadratic_bound_at h structural hab I hI
  let := hU
  have hne : F.Vi 1 ≠ F.UH I := by
    intro he
    have hV : V ≤ F.Vi 1 := by rw [he]; exact le_conjugateSpanBy V I
    have hh := card_le_of_le hV
    have hVcard : Nat.card V = 8 := by
      simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [hVcard,F.card 1 (by decide)] at hh
    omega
  have hproper : (F.Vi 1).subgroupOf (F.UH I) ≠ ⊤ := by
    intro he
    exact hne (le_antisymm a.kernel_le (subgroupOf_eq_top.mp he))
  let : Nontrivial ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) :=
    QuotientGroup.nontrivial_iff.mpr hproper
  let := SimpleHeadQuotient.subrepresentation_coatomic a.representation
  obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation a.representation)
  refine ⟨hU,a,ha,N,hN,SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN,
    local_proper_quotient_faithful_at d h hab structural previous faithful earlier
      source47 I hI C hC a N hN.ne_top,?_⟩
  obtain ⟨A,hA,hquad,hbound⟩ := (quadraticRatio_le_two_iff a.representation).mp ha
  refine (quadraticRatio_le_two_iff N.quotientRepresentation).mpr ⟨A,hA,?_,?_⟩
  · exact quadratic_of_equivariant_surjection a.representation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hquad
  · have hb := fixedCodim_quotient_add_subrepresentation_le a.representation N A
    omega
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
