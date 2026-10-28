module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.OtherFactor
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Tensor
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Both natural factors in the literal escaping candidate

The original common-chief tensor retains its canonical natural factor.
On that very tensor, a faithful rank-two actor fixing a hyperplane excludes
an alternating-five second factor; the surviving binary linear-three factor
has natural degree three. The action marking and coordinate map belong to
the original constituent. In particular its actor image lies in the second
factor image under the literal chief-section quotient action. Its matrix
image is the full group fixing the common plane pointwise, namely the two-core
of that plane's stabilizer. The actor and chief section remain the original ones.

The controlled Thompson normalizer premise remains explicit. Its construction
and the final generation contradiction belong to qt-d-1319-ff-contradiction;
earlier canonical geometry is discharged by qt-d-1317-supplements.
Source: Aschbacher--Smith 13.1.9, printed p.871.
-/

public noncomputable section
open scoped IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- On the original tensor constituent, the second factor is naturally SL₃(2).
No choice of a different chief section or a different actor is made. -/
theorem common_chief_otherTensor {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (hr : rank (hatImage (T : Subgroup G) L Y j A) = 2)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} (t : c.NaturalTensor hc)
    (hmodel : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2)
    (heq : Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))) :
    ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∧ Nonempty t.OtherNatural := by
  let := hat_commutator_normal w hTH hAH hTL j
  have he := (ha.actor_bound A hA hAn).1.2
  have hf := common_actor_faithful ha hA
  have hr' : 1 < rank (hatImage (T : Subgroup G) L Y j A) := by omega
  obtain ⟨e⟩ := heq
  have h3 : ClassicalGroup.IsPSL (XiQuotient Y) 3 2 := by
    rcases hmodel with h5 | h3
    · obtain ⟨e5⟩ := h5
      exact (t.not_alternating_five he hf hr' (e.symm.trans e5)).elim
    · exact h3
  refine ⟨h3,?_⟩
  obtain ⟨F,hF,hfin,hcard,⟨f⟩⟩ := h3
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  let ek := ((e.symm.trans f).trans (Atlas.fieldEquivPSL 3 ef)).trans Matrix.PSL3Two.equiv.symm
  exact t.exists_otherNatural he hf hr' ek

/-- The same escaping candidate has two actual natural tensor factors. -/
theorem candidate_common_chief_both_tensors (h : Hypothesis1311 T)
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
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
                hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
                  hatImage (T : Subgroup G) L Y j A⁆ = ⊥,
                  ∃ t : c.NaturalTensor hc, ∃ o : t.OtherNatural,
                    c.ActorImageContained ∧
                    o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
                      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2 := by
  obtain ⟨hj1,Y,w,n,rest⟩ :=
    candidate_common_chief_sharp h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,rest⟩ := rest
  let := e
  obtain ⟨ha,hKY,_,hmodel,heq,hsimple,A,hA,hAn,_,hr,hcod,c,hε,hsection⟩ := rest
  let := hsimple
  obtain ⟨hc,⟨t⟩⟩ := common_chief_naturalTensor h hmany hL hn ha hA c hsection
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨h3,⟨o⟩⟩ := common_chief_otherTensor w hTH (hAC.trans hC.1) hTL ha hA hAn hr c t hmodel heq
  let := hat_commutator_normal w hTH (hAC.trans hC.1) hTL j
  exact ⟨hj1,Y,w,n,e,ha,hKY,h3,A,hA,hAn,hr,hcod,c,hε,hc,t,o,
    o.section_actor_image_le,
    o.matrixActor_eq_core (ha.actor_bound A hA hAn).1.2 (common_actor_faithful ha hA) hr⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
