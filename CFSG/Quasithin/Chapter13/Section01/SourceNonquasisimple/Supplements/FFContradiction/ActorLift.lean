module
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Tensor.ActorFamily
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OtherTensor

/-!
# The original Thompson image is the common-axis tensor actor

A natural tensor marking realizes the chosen actor by the simple K-factor
on the literal common chief section. The centralizer of K in the reduced
KR-image is trivial, so this equality lifts to the original action on D.
For every nontrivial member of the same Thompson family, construct its
common section and repeat the sharp displacement argument. This puts every
family image in K. Returning to the original tensor, three-copy displacement
and the unique doubled-natural offender in a Sylow of SL₃(2) identify all
these images with the same four-group. Generation now gives Ĵ_j(R) = Â.
The candidate theorem retains the same Y, quotient maps and tensor witness.

The controlled index, the lift to the entire moved module and the final
generation contradiction remain obligations of qt-d-1319-ff-contradiction.
Earlier canonical geometry belongs to qt-d-1317-supplements.
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

theorem common_chief_hat_actor_le {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    {c : CommonHatChief (T : Subgroup G) L Y A j}
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} {t : c.NaturalTensor hc}
    (o : t.OtherNatural) :
    hatImage (T : Subgroup G) L Y j A ≤
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) := by
  let K := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  let R := hatImage (T : Subgroup G) L Y j (radicalSylowCentralizer (T : Subgroup G) L)
  let F := commonGroup (T : Subgroup G) L Y j
  let := hat_commutator_normal w hTH hAH hTL j
  let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := o.second.symm.toMonoidHom) o.second.symm.surjective
  have hKR : hatImage (T : Subgroup G) L Y j
      (thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer (T : Subgroup G) L) = K ⊔ R := by
    unfold hatImage
    rw [subgroupOf_sup (show thompsonCommutator (T : Subgroup G) L Y j ≤ F from
      le_sup_left.trans le_sup_right)
      (show radicalSylowCentralizer (T : Subgroup G) L ≤ F from le_sup_right.trans le_sup_right),Subgroup.map_sup]
    rfl
  have hcore : pCore 2 (K ⊔ R : Subgroup (HatGroup (T : Subgroup G) L Y j)) = ⊥ := by
    rw [←hKR]
    exact ha.second_core
  have hRp : IsPGroup 2 R :=
    (T.isPGroup'.to_le (radicalSylowCentralizer_le (T : Subgroup G) L)).comap_subtype.map _
  exact o.actor_le R (map_mono (subgroupOf_mono _ hA.1))
    (centralizer_inf_sup_eq_bot_of_simple_two_supplement K R
      (Group.IsPerfect.not_isMulCommutative K) hRp hcore)

/-- Every Thompson-family actor, including those not chosen initially, lies in
K under the original action on D. -/
theorem common_all_hat_actors_le (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ} (hj : j ≤ 1)
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hKY : thompsonCommutator (T : Subgroup G) L Y j = Y)
    (hm : ⁅⁅omegaClosure (T : Subgroup G) L Y j,canonicalSupplement (T : Subgroup G) L⁆,
      thompsonCommutator (T : Subgroup G) L Y j⁆ ≠ ⊥)
    (hmodel : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2)
    (heq : Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))) :
    ∀ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
      hatImage (T : Subgroup G) L Y j A ≤
        hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) := by
  intro A hA
  by_cases hAn : hatImage (T : Subgroup G) L Y j A = ⊥
  · rw [hAn]
    exact bot_le
  obtain ⟨c⟩ := common_chief_section_of_commutator_eq (A := A)
    h hmany hL hn w hH hTH hAH hAC hTL hKY hm
  have hmodel' : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∨ Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3)) :=
    hmodel.imp_right Or.inl
  have hr := common_actor_rank_le_two w hTH hAH hTL ha hA hAn hmodel' heq
  have hl := common_chief_actor_displacement h hmany hL hn w hTH hAH hTL ha hA hAn c
  have hb := ha.actor_bound A hA hAn
  have hbound := hb.2
  have hr2 : rank (hatImage (T : Subgroup G) L Y j A) = 2 := by omega
  have hcod : fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
      (hatImage (T : Subgroup G) L Y j A) = 3 := by have := hb.2; omega
  let := common_canonical_perfect h hmany hL hn (Y := Y) (j := j)
  have hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono le_rfl (sup_le
      (map_mono (subgroupOf_mono _ le_sup_left))
      (map_mono (subgroupOf_mono _ (hA.1.trans le_sup_right))))).trans ha.commute.le
  have hε := common_chief_section_epsilon w hTH hAH hTL ha hA c
  have hsection := le_antisymm (c.actor_displacement_le.trans_eq hcod)
    (c.actor_displacement hc hb.1 hε)
  obtain ⟨hc',⟨t⟩⟩ := common_chief_naturalTensor h hmany hL hn ha hA c hsection
  obtain ⟨_,⟨o⟩⟩ := common_chief_otherTensor w hTH hAH hTL ha hA hAn hr2 c t hmodel heq
  exact common_chief_hat_actor_le w hTH hAH hTL ha hA o

private theorem hatImage_thompson_le {T L Y : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal] {B : Subgroup (HatGroup T L Y j)}
    (hf : ∀ A ∈ thompsonFamily (radicalSylowCentralizer T L) j,
      hatImage T L Y j A ≤ B) :
    hatImage T L Y j (thompsonJ (radicalSylowCentralizer T L) j) ≤ B := by
  let E := commonGroup T L Y j
  let q := hatMap T L Y j
  let P := B.comap q
  have hJR : thompsonJ (radicalSylowCentralizer T L) j ≤ P.map E.subtype := by
    apply sSup_le
    intro A hA
    have hAE : A ≤ E := hA.1.trans (le_sup_right.trans le_sup_right)
    intro a ha
    refine ⟨⟨a,hAE ha⟩,?_,rfl⟩
    exact hf A hA (mem_map_of_mem q ha)
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,hba⟩ := hJR ha
  have he : b = a := Subtype.ext hba
  exact he ▸ hb

/-- All nontrivial Thompson-family images coincide with the marked common-axis
four-group on the original D-action. -/
theorem common_thompson_image_eq_actor (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ} (hj : j ≤ 1)
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hKY : thompsonCommutator (T : Subgroup G) L Y j = Y)
    (hm : ⁅⁅omegaClosure (T : Subgroup G) L Y j,canonicalSupplement (T : Subgroup G) L⁆,
      thompsonCommutator (T : Subgroup G) L Y j⁆ ≠ ⊥)
    (hmodel : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2)
    (heq : Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)))
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (hAr : rank (hatImage (T : Subgroup G) L Y j A) = 2)
    {c : CommonHatChief (T : Subgroup G) L Y A j}
    {hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥} {t : c.NaturalTensor hc}
    (o : t.OtherNatural) :
    hatImage (T : Subgroup G) L Y j (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j) =
      hatImage (T : Subgroup G) L Y j A := by
  have hall := common_all_hat_actors_le h hmany hL hn w hH hTH hAH hAC hTL hj ha hKY hm hmodel heq
  have hAK := hall A hA
  let R := hatImage (T : Subgroup G) L Y j (radicalSylowCentralizer (T : Subgroup G) L)
  have hRp : IsPGroup 2 R :=
    (T.isPGroup'.to_le (radicalSylowCentralizer_le (T : Subgroup G) L)).comap_subtype.map _
  apply le_antisymm
  · apply hatImage_thompson_le
    intro B hB
    by_cases hBn : hatImage (T : Subgroup G) L Y j B = ⊥
    · rw [hBn]; exact bot_le
    obtain ⟨cB⟩ := common_chief_section_of_commutator_eq (A := B)
      h hmany hL hn w hH hTH hAH hAC hTL hKY hm
    have hBbound := ha.actor_bound B hB hBn
    have hBupper := hBbound.2
    have hBdim := common_chief_actor_displacement h hmany hL hn w hTH hAH hTL ha hB hBn cB
    have hBsmall := common_actor_rank_le_two w hTH hAH hTL ha hB hBn
      (hmodel.imp_right Or.inl) heq
    have hBr : rank (hatImage (T : Subgroup G) L Y j B) = 2 := by omega
    have hBcod : fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
        (hatImage (T : Subgroup G) L Y j B) = 3 := by omega
    have hBK := hall B hB
    have hb := t.constituent_fixedCodim_le (hatImage (T : Subgroup G) L Y j B) hBK
    rw [hBcod] at hb
    have he := o.unique_actor hAK R (hatImage (T : Subgroup G) L Y j B) hRp
      (map_mono (subgroupOf_mono _ hA.1)) (map_mono (subgroupOf_mono _ hB.1))
      hBK (ha.actor_bound A hA hAn).1 hBbound.1 hAr hBr (by omega)
    exact he.le
  · exact map_mono (subgroupOf_mono _ (le_sSup hA))

/-- The literal candidate has Ĵ_j(R) = Â, with the same common-axis natural tensor. -/
theorem candidate_thompson_image_eq_actor (h : Hypothesis1311 T)
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
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              ∃ hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
                hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
                  hatImage (T : Subgroup G) L Y j A⁆ = ⊥,
                  ∃ t : c.NaturalTensor hc, ∃ o : t.OtherNatural,
                    o.matrixActor = (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer
                      (fixedSpace BinaryLinearThree.W o.matrixActor)).pCoreIn 2 := by
  obtain ⟨hj1,Y,w,n,rest⟩ :=
    candidate_common_chief_sharp h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  obtain ⟨e,rest⟩ := rest
  let := e
  obtain ⟨ha,hKY,_,hmodel,heq,hsimple,A,hA,hAn,_,hr,hcod,c,hε,hsection⟩ := rest
  let := hsimple
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hm := omegaClosure_double_movement h hmany hs hL hn w hH hTH
    (hAC.trans hC.1) hTL hN
  obtain ⟨hc,⟨t⟩⟩ := common_chief_naturalTensor h hmany hL hn ha hA c hsection
  obtain ⟨h3,⟨o⟩⟩ := common_chief_otherTensor w hTH (hAC.trans hC.1) hTL ha hA hAn hr c t hmodel heq
  have hJA := common_thompson_image_eq_actor h hmany hL hn w hH hTH
    (hAC.trans hC.1) hAC hTL hj ha hKY hm hmodel heq hA hAn hr o
  let := hat_commutator_normal w hTH (hAC.trans hC.1) hTL j
  exact ⟨hj1,Y,w,n,e,ha,hKY,h3,A,hA,hAn,hr,hcod,hJA,c,hε,hc,t,o,
    o.matrixActor_eq_core (ha.actor_bound A hA hAn).1.2 (common_actor_faithful ha hA) hr⟩
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
