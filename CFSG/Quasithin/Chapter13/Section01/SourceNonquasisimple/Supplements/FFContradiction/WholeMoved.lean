module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.WholeMoved
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Normalizer

/-!
# The original candidate's whole moved module is its natural tensor

The common double-commutator support lies in the literal K-displacement
space of D. The sharp tensor argument therefore kills the chosen chief
section's denominator and identifies its upper space with all of [D,K̂].
It is nine-dimensional and irreducible for the same original actor group.
The candidate application retains both natural markings, the common-axis
actor, its Thompson-image equality and its lifted normalizer control.

The controlled index and final generation contradiction remain with
qt-d-1319-ff-contradiction. Earlier geometry is assembled by
qt-d-1317-supplements. Source: Aschbacher--Smith 13.1.9, printed p.871.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The prescribed double-commutator support lies in the whole K-moved space,
under the original quotient-action coordinates. -/
theorem commonDoubleSpace_le_moved {T L Y : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :
    commonDoubleSpace T L Y j ≤ subspaceCommutator (hatRepresentation T L Y j) ⊤
      (hatImage T L Y j (thompsonCommutator T L Y j)) := by
  let D := commonModule T L Y j
  let E := commonGroup T L Y j
  let S := (canonicalSupplement T L).subgroupOf E
  let K := (thompsonCommutator T L Y j).subgroupOf E
  have he := NormalElementaryQuotient.commutatorSpace_eq D (hatMap T L Y j)
    (QuotientGroup.mk'_surjective _) (hatMap_ker T L Y j) K
  change NormalElementaryQuotient.commutatorSpace D K =
    subspaceCommutator (hatRepresentation T L Y j) ⊤
      (hatImage T L Y j (thompsonCommutator T L Y j)) at he
  rw [←he]
  intro v hv
  exact commutator_mono (commutator_le_left D S) le_rfl hv

/-- The same literal tensor is the entire moved module, with zero denominator. -/
theorem common_chief_whole_moved {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (hcod : fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
      (hatImage (T : Subgroup G) L Y j A) = 3)
    {c : CommonHatChief (T : Subgroup G) L Y A j}
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} {t : c.NaturalTensor hc}
    (o : t.OtherNatural) :
    c.lower = ⊥ ∧
      c.upper.toSubmodule = subspaceCommutator (hatRepresentation (T : Subgroup G) L Y j) ⊤
        (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator (hatRepresentation (T : Subgroup G) L Y j) ⊤
        (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))) = 9 :=
  o.whole_moved (common_chief_hat_actor_le w hTH hAH hTL ha hA o)
    (ha.actor_bound A hA hAn).1.2 hAn hcod.le commonDoubleSpace_le_moved


/-- The literal candidate has a nine-dimensional irreducible whole moved
module with the same natural tensor and controlled actor normalizer. -/
theorem candidate_whole_tensor (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    j = 1 ∧ ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧
            rank (hatImage (T : Subgroup G) L Y j A) = 2 ∧
            fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) = 3 ∧
            hatImage (T : Subgroup G) L Y j (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j) =
              hatImage (T : Subgroup G) L Y j A ∧
            liftedActorNormalizer (T : Subgroup G) L Y A j ≤ normalizer (L : Set G) ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
                hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
                  hatImage (T : Subgroup G) L Y j A⁆ = ⊥,
                  ∃ t : c.NaturalTensor hc, ∃ o : t.OtherNatural,
                    c.lower = ⊥ ∧
                    c.upper.toSubmodule = subspaceCommutator
                      (hatRepresentation (T : Subgroup G) L Y j) ⊤
                      (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
                    Module.finrank (ZMod 2) c.upper.toSubmodule = 9 ∧
                    IsIrreducible c.upper.toRepresentation ∧
                    o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
                      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2 := by
  obtain ⟨hj1,Y,w,n,rest⟩ :=
    candidate_tensor_actor_normalizer h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,rest⟩ := rest
  let := e
  obtain ⟨ha,hKY,h3,A,hA,hAn,hr,hcod,hJA,hnorm,c,hε,hc,t,o,haxis⟩ := rest
  let := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  let := o.second.isSimpleGroup
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hwhole := common_chief_whole_moved w hTH (hAC.trans hC.1) hTL ha hA hAn hcod o
  exact ⟨hj1,Y,w,n,e,ha,hKY,h3,A,hA,hAn,hr,hcod,hJA,hnorm,c,hε,hc,t,o,
    hwhole.1,hwhole.2.1,hwhole.2.1 ▸ hwhole.2.2,c.whole_irreducible hwhole.1,haxis⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
