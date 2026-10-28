module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.PreDescentSource.Geometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Application
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The source offender argument on the original singular line

The earlier local structure constructs the original marked geometry. Its
Thompson and normalizer control supply the local premises of the maximum-rank
calculation and of the classification consumer. Simple QTKE supplies SQTK for
the original line normalizer; the three-prime restriction uses the original
fixed plane Z_S of 15.3.49(5).

The resulting action is the canonical faithful quotient action on the actual
first summand of V_E/E. We retain same-I best generation, the original I_0
image and exact kernel, both moved dimensions and the original index-three
intersection. The original and temporary two-cores remain separate.

The classification theorem is conditional on the full adequate B.5 input for
KnownSimple.IsKnownSimple. Its universal proof remains with the B.5 owner and
its discharge with the Section 15.3 assembly. No terminal conclusion about
the original G_E is assumed or asserted here.

Source: Aschbacher–Smith, proof of 15.3.67, printed pp.1153–1154
(combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceCompletion

open LocalStructure GoldschmidtCore.LocalRelations
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer OriginalComparison

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

omit [Finite G] in
/-- The earlier orthogonal coordinates supply the elementary structure used
by the original paired action; no extra module hypothesis is required. -/
theorem module_elementary (s : EarlierData T M Mc P E) :
    IsElementaryAbelian 2 (localModule T M) := by
  let : IsElementaryAbelian 2 (Multiplicative OrthogonalFourBinary.Space) := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro v
      rw [pow_two]
      change v.toAdd + v.toAdd = 0
      exact CharTwo.add_self_eq_zero _ }
  exact IsElementaryAbelian.of_surjective s.natural.coordinates.symm.toMonoidHom
    s.natural.coordinates.symm.surjective

private theorem local_controls (s : EarlierData T M Mc P E) :
    elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G) ∧
    normalizer (localModule T M : Set G) ≤ M ∧
    ¬ lineI E ≤ lineM M E := by
  let := module_elementary s
  let r := initialStructure s
  have hV : localModule T M ≠ ⊥ := by
    intro h
    have hE : E = ⊥ := bot_unique (s.line_le.trans h.le)
    have hc := s.line_card
    rw [hE, card_bot] at hc
    omega
  refine ⟨?_, ?_, fun h => r.thompson_escape (h.trans inf_le_left)⟩
  · rw [r.thompson]
    exact (sSup_le fun _ hA => hA.1).trans
      (inf_le_right.trans (centralizer_le s.line_le))
  · exact (s.ordering.1.1.eq_of_le
      ⟨localModule T M, hV, IsElementaryAbelian.isPGroup 2 _, rfl⟩
      s.natural.normalizes).symm.le

/-- The full displayed calculation on the canonical quotient of original
geometry. Keeping the action parameter abstract avoids expanding the source
construction while elaborating its dependent fixed-space types. -/
def RankConclusions {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
    (o : Geometry.OriginalData Y T V M E Pc) : Prop :=
    let := o.module_normal
    let := o.module_elementary
    let H := temporaryLineNormalizer T V E
    let U := Replacement.Transvections.localSpan T V E
    let Q := localCore T V E
    let q := QuotientGroup.mk' Q
    let C := centralizer (U : Set H)
    let f := QuotientGroup.mk' C
    let σ := o.pairedRepresentation f (QuotientGroup.mk'_surjective C)
      (QuotientGroup.ker_mk' C)
    ∃ A ∈ elementaryAbelianMaxSubgroups ((lineT T E).subgroupOf H),
      A ≤ localCentralizer T V E ∧
      let B := A ⊓ Q
      let D := A ⊓ centralizer (U : Set H)
      let F := U ⊓ centralizer (A : Set H)
      let N := quotientRank (U ⊓ centralizer (B : Set H)) F
      A.map q ≠ ⊥ ∧ F = A ⊓ U ∧
      rank (A.map q) + rank (B.map f) + rank D = rank A ∧
      rank (D ⊔ U) = rank D + quotientRank U F ∧
      quotientRank U F ≤ rank (A.map q) + rank (B.map f) ∧
      quotientRank U (U ⊓ centralizer (B : Set H)) = 2 * rank (B.map f) ∧
      rank (B.map f) + N ≤ rank (A.map q) ∧
      quotientRank U F + N ≤ 2 * rank (A.map q) ∧
      IsOffender σ (A.map q) ∧
      2 * fixedCodim σ (A.map q) + N ≤ 2 * rank (A.map q)

/-- The displayed source inequalities on an actual maximum of the unchanged
T_E, with actual quotient fixed spaces and no classification input. -/
theorem source_offender_inequalities (s : EarlierData T M Mc P E) :
    let := module_elementary s
    RankConclusions (PreDescentSource.originalData s) := by
  let := module_elementary s
  let o := PreDescentSource.originalData s
  let := o.module_normal
  let := o.module_elementary
  let C := centralizer (Replacement.Transvections.localSpan T (localModule T M) E :
    Set (temporaryLineNormalizer T (localModule T M) E))
  obtain ⟨hJ, hNM, hI⟩ := local_controls s
  exact SourceRanks.exists_source_offender o hJ hNM hI
    (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)

/-- The complete original-action conclusion, retaining the identical temporary
Thompson image, original I_0, exact section kernel and full original I action. -/
def OriginalConclusions {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
    (o : Geometry.OriginalData Y T V M E Pc) : Prop :=
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
    let C := centralizer
      (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
    let f := QuotientGroup.mk' C
    let hf := QuotientGroup.mk'_surjective C
    let hker := QuotientGroup.ker_mk' C
    let σ := o.pairedRepresentation f hf hker
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (originalRepresentation σ) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker (originalRepresentation σ)) = 2 ∧
    (originalRepresentation σ).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (originalActor T V E) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker
      (FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker))) = 2 ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3

/-- The full pre-descent offender conclusion for the full known-simple class.
All local action, Sylow, maximum-family, marker and model witnesses are
constructed from the earlier source data. Only the genuine universal earlier
classification implication remains explicit. -/
theorem source_conclusions (s : EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple.{u} G)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      KnownSimple.IsKnownSimple.{u}) :
    let := module_elementary s
    OriginalConclusions (PreDescentSource.originalData s) := by
  let := module_elementary s
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le s.line_le
  have hE : E ≠ ⊥ := by
    intro h
    have hc := s.line_card
    rw [h, card_bot] at hc
    omega
  have hSQTK : IsSQTK KnownSimple.IsKnownSimple (lineNormalizer E) :=
    hG.twoLocal_sqtk ⟨E, hE, IsElementaryAbelian.isPGroup 2 E, rfl⟩
  let r := initialStructure s
  obtain ⟨hJ, hNM, hI⟩ := local_controls s
  exact SourceClassification.Application.canonical_original_conclusions_of_classification
    (PreDescentSource.originalData s) hJ hNM hI r.thompson_product
    r.thompson_normalizer_control hSQTK
    (fixedPlane (localModule T M) (planeStabilizer T P)) inf_le_left hZ classify

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceCompletion
