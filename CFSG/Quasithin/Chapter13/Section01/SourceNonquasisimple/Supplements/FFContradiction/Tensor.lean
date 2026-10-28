module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.SharpAction

/-!
# Canonical natural factor and tensor coordinates in the escaping candidate

On the original common chief section, sharp displacement three forces three
copies of an absolutely irreducible constituent of K̂Â. Its displacement is
one. The literal commuting product action now gives an external tensor
isomorphism, and the faithful perfect canonical factor is identified with
SL₃(2) acting naturally on the three-dimensional multiplicity space. The
chosen actor remains faithful on the constituent and has rank two there.

The application constructs all of this for the same escaping Y, Thompson
actor and centralizer-quotient representation. It retains the controlled
normalizer premise from the still-required Thompson factorization. The
other constituent must still be recognized as the natural L₃(2) module;
the full tensor marking and final generation contradiction remain with
qt-d-1319-ff-contradiction. Earlier canonical geometry is discharged by
qt-d-1317-supplements.

Source: Aschbacher--Smith 13.1.9, printed p.871, after equality in (*).
-/

public noncomputable section

open scoped IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Construct tensor coordinates and the canonical natural three-space on the literal section. -/
theorem common_chief_naturalTensor (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    (hcod : fixedCodim (sectionRepresentation
      ((hatRepresentation (T : Subgroup G) L Y j).comp
        (CommonChief.actorGroup
          (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
          (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
          (hatImage (T : Subgroup G) L Y j A)).subtype) c.lower c.upper)
      ((hatImage (T : Subgroup G) L Y j A).subgroupOf
        (CommonChief.actorGroup
          (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
          (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
          (hatImage (T : Subgroup G) L Y j A))) = 3) :
    ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥, Nonempty (c.NaturalTensor hc) := by
  let := common_canonical_perfect h hmany hL hn (Y := Y) (j := j)
  let : Nontrivial (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L)) :=
    (nontrivial_iff_ne_bot _).mpr ha.canonical_nontrivial
  have hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono le_rfl (sup_le
      (map_mono (subgroupOf_mono _ le_sup_left))
      (map_mono (subgroupOf_mono _ (hA.1.trans le_sup_right))))).trans ha.commute.le
  exact ⟨hc,c.exists_naturalTensor hc (common_chief_canonical_faithful ha c) hcod⟩

/-- The original actor loses no rank on the constructed tensor constituent.
Relative normality is supplied by the same refined escaping witness. -/
theorem common_chief_tensor_actor_rank {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} (t : c.NaturalTensor hc) :
    rank (actionSubgroup t.tensor.constituent.toRepresentation
      ((hatImage (T : Subgroup G) L Y j A).subgroupOf
        (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
          hatImage (T : Subgroup G) L Y j A))) = rank (hatImage (T : Subgroup G) L Y j A) := by
  let := hat_commutator_normal w hTH hAH hTL j
  exact t.actor_rank (common_actor_faithful ha hA)

/-- The original candidate supplies the tensor and its canonical natural factor,
with the same rank-two actor. Its constituent rank is preserved by the preceding theorem. -/
theorem candidate_common_chief_tensor (h : Hypothesis1311 T)
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
          (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
            ClassicalGroup.IsPSL (XiQuotient Y) 3 2) ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧
            rank (hatImage (T : Subgroup G) L Y j A) = 2 ∧
            fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) = 3 ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
                hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
                  hatImage (T : Subgroup G) L Y j A⁆ = ⊥, Nonempty (c.NaturalTensor hc) := by
  obtain ⟨hj1,Y,w,n,e,ha,hKY,_,hmodel,_,_,A,hA,hAn,_,hr,hcod,c,hε,hsection⟩ :=
    candidate_common_chief_sharp h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  let := e
  exact ⟨hj1,Y,w,n,e,ha,hKY,hmodel,A,hA,hAn,hr,hcod,c,hε,
    common_chief_naturalTensor h hmany hL hn ha hA c hsection⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
