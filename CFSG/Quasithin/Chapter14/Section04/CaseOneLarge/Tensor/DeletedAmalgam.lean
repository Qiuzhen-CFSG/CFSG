module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedCore
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import Theory.GroupTheory.SylowNormalizedResidual
public import Theory.SpecificGroups.SL2.CardFourEquiv
/-!
# The actual mixed rank-one amalgam in the deleted tensor case

The literal H∞ and I₂ satisfy every clause of corrected Hypothesis F.1.1
with the original Sylow subgroup T. Their two-core quotients are identified
with A₅ and S₃, hence with the concrete rank-one models. The cubic Borel is
T ∩ I₂. The other Borel lies in X₂T, which normalizes I₂ by the deleted
action calculation. The original point and plane give nontrivial two-cores
in the two parabolics, so condition (E) supplies characteristic two.

The preceding residual argument makes the actual generated group G₀T
core-free. Thus neither T ≤ G₀ nor U = O₂(H) is imposed. The F.1.12
exclusion of this mixed configuration remains to be proved; this module
constructs its source hypotheses without a recognition callback.

Source: Aschbacher--Smith 14.4.10(3), printed p.1011, and F.1.1,
printed p.259. All inclusions, quotients and the original conjugator are
those of the given counterexample and invariant flag.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The genuine F.1.1 input for the literal pair H∞, I₂ and the original T. -/
theorem source_tensor_deleted_amalgam (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ChapterF.Source.HypothesisF11 ![component F.H, F.I₂ L] (T : Subgroup G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  obtain ⟨e, _, hgen, _, hIG, hIN, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare
      (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  have hTK : (T : Subgroup G) ≤ normalizer (component F.H : Set G) :=
    (F.invariant 1).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (solvableResidual F.H)))
  have hTI : (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hSylK : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ component F.H) (component F.H) :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (F.invariant 1), map_subgroupOf_eq_of_le (F.invariant 1)⟩
      (map_subtype_le _) (TensorDeleted.component_isCComponent (starComponentEquiv hAD c.actor)).subnormal
  have hSylI : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ F.I₂ L) (F.I₂ L) :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (F.invariant 2), map_subgroupOf_eq_of_le (F.invariant 2)⟩ hIG hIN.isSubnormal
  have hBI : ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) = (T : Subgroup G) ⊓ F.I₂ L := by
    convert ChapterF.Source.borel_eq_of_cubic_local_sylow _ _ hSylI e using 1
    simp only [ChapterF.Source.borel, inf_assoc, inf_idem]
  have hsecond : second F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    (source_tensor_deleted_reduction d earlier hq chosen structural alternatives F hne hZ
      g hg hgP hgH c hdel).2.2.2.2.2.2.2.2
  have hBK : borel F.H (T : Subgroup G) ≤ second F.H (T : Subgroup G) ⊔ (T : Subgroup G) :=
    le_embedded_pResidual_sup_sylow_of_normalizes T _ (borel_T_normalized (F.invariant 1))
  have hcross : borel F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) :=
    hBK.trans (sup_le hsecond hTI)
  have hcore := source_tensor_deleted_sylow_join_core_eq_bot d earlier hq chosen
    structural alternatives classification F hne g hgP hgH c hdel
  let eK := TensorDeleted.componentQuotient (starComponentEquiv hAD c.actor)
  have hmodelK : ChapterF.Source.IsRankOneModel (coreQuotient (component F.H)) := by
    apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
    refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 2 (by decide)]
    · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
      exact ⟨eK.trans a.symm⟩
  have hmodelI : ChapterF.Source.IsRankOneModel (coreQuotient (F.I₂ L)) := by
    obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
      (K := ZMod 2) (by simp)
    exact .linear 1 (by decide) ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨e.trans a.symm⟩⟩
  have hchar (A : Subgroup G) (hTA : (T : Subgroup G) ≤ A) (hQ : A.pCoreIn 2 ≠ ⊥) :
      generalizedFitting A = pCore 2 A :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (d.qtke.evenCharacteristic T) ⟨hQ, hTA⟩))
  refine { finite_S := inferInstance
           S_isP := T.isPGroup'
           S_normalizes := ?_
           sylow := ?_
           quotient := ?_
           cross := ?_
           twoCore_free := ?_
           characteristic_two := ?_ }
  · intro i; fin_cases i
    · exact hTK
    · exact hTI
  · intro i; fin_cases i
    · exact hSylK
    · exact hSylI
  · intro i; fin_cases i
    · exact hmodelK
    · exact hmodelI
  · intro i; fin_cases i
    · change ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) ≤ _
      rw [hBI]
      exact inf_le_left.trans hTK
    · exact hcross
  · change pCore 2 (component F.H ⊔ F.I₂ L ⊔ (T : Subgroup G) : Subgroup G) = ⊥
    rw [sup_comm (component F.H) (F.I₂ L)]
    exact (map_eq_bot_iff_of_injective _
      (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)).subtype_injective).mp hcore
  · intro i; fin_cases i
    · change generalizedFitting (component F.H ⊔ (T : Subgroup G) ⊔
        ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) : Subgroup G) =
        pCore 2 (component F.H ⊔ (T : Subgroup G) ⊔
          ChapterF.Source.borel (F.I₂ L) (T : Subgroup G) : Subgroup G)
      rw [hBI, sup_eq_left.mpr (show (T : Subgroup G) ⊓ F.I₂ L ≤
        component F.H ⊔ (T : Subgroup G) from inf_le_left.trans le_sup_right)]
      exact hchar _ le_sup_right (source_tensor_component_local chosen F c).2.2
    · let A := F.I₂ L ⊔ (T : Subgroup G) ⊔ borel F.H (T : Subgroup G)
      change generalizedFitting A = pCore 2 A
      have hAG : A ≤ F.Gi 2 := sup_le (sup_le hIG (F.invariant 2))
        (hBK.trans (sup_le
          ((source_tensor_deleted_plane_centralizer d earlier hq chosen F hne hZ c hdel).trans
            (Subgroup.centralizer_le_normalizer _)) (F.invariant 2)))
      have hPA : F.Vi 2 ≤ A := ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans
        ((le_sup_left.trans hgen.ge).trans (le_sup_left.trans le_sup_left))
      have hp : IsPGroup 2 (F.Vi 2) :=
        (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 2)) (inclusion_injective _)
      have hQ := le_pCoreIn_of_normalizes hp hPA hAG
      have hneQ : A.pCoreIn 2 ≠ ⊥ := by
        intro he
        have heP := bot_unique (he ▸ hQ)
        have hc := F.card 2 (by decide)
        rw [heP, card_bot] at hc
        norm_num at hc
      exact hchar A (le_sup_right.trans le_sup_left) hneQ

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
