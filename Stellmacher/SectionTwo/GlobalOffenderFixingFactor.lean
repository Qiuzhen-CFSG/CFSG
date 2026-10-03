module
public import Stellmacher.SectionTwo.NormalSupplementFixedPoints
public import Stellmacher.SectionThree.OffenderResidualClosure
public import Stellmacher.SectionOne.GlobalOffenderSupportSelection
public import Stellmacher.SectionTwo.LemmaTwoOne
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian

/-!
# A fixing offender factor on the original Section Two module

Let the finite solvable characteristic-two group be a member of the local
P-set relative to its given Sylow subgroup. For its exact faithful quotient
action on V, a vector fixed by nontrivial J but not by the Sylow image is
fixed by some raw one-seven factor.

The quotient faithfulness and (2.1) supply the Section One hypotheses.
The normal-closure residual identity makes the full preimage of E a normal
supplement of S. The proved fixed/commutator complement of the actual global
factor action, together with normal-supplement fixed-point transfer, shows
that C_V(E) is Sylow-fixed. The action-level support-selection theorem then
selects the required factor, retaining its original action on V.

This proves the choice of j with [w,E_j]=1 in Stellmacher (6.4), Journal of
Algebra 190 (1997), pp.31-32. The quotient groups and their action use the
bars retained in the journal scan of `refs/files/stellmacher-n-group.pdf`;
see also the abbreviated `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem exists_global_offender_factor_fixing
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hP : (⊤ : Subgroup G) ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    {X : Type u} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S) :
    letI := quotientConjugationAction S q hq hker
    let J := SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q)
    J ≠ ⊥ → ∀ w : vSubgroup S, w ∈ FixedPoints.subgroup J (vSubgroup S) →
      w ∉ FixedPoints.subgroup ((S : Subgroup G).map q) (vSubgroup S) →
      ∃ D : Subgroup X, SectionOne.IsOneSevenFactor (V := vSubgroup S) D ∧
        w ∈ FixedPoints.subgroup D (vSubgroup S) := by
  classical
  let V := vSubgroup S
  let _ := quotientConjugationAction S q hq hker
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let T := S.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (T : Subgroup X)
  let E := SectionOne.oneE (V := V) (T : Subgroup X)
  change J ≠ ⊥ → _
  intro hJ w hwJ hwS
  have hJS : J ≤ (T : Subgroup X) := sSup_le fun A hA => hA.1
  have hTne : (T : Subgroup X) ≠ ⊥ := fun hb => hJ (bot_unique (hb ▸ hJS))
  have hdvd : 2 ∣ Nat.card T := T.isPGroup'.card_eq_or_dvd.resolve_left
    (fun hc => hTne (Subgroup.card_eq_one.mp hc))
  let _ : Group.IsSolvable G := h.solvable
  have hOne : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective hq,
      even_iff_two_dvd.mpr (hdvd.trans (T : Subgroup X).card_subgroup_dvd_card),
      quotientConjugationAction_faithful S q hq hker, lemma_two_one h S q hq hker⟩
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hs
    apply hTne
    change (S : Subgroup G).map q = ⊥
    rw [hs, Subgroup.map_bot]
  have hthree : SectionThree.Hypotheses G (S : Subgroup G) :=
    ⟨h.even_order, hSne, S.isPGroup'⟩
  have hEeq := SectionThree.offender_normalClosure_eq_residual_sup S hthree hP h.solvable
    q hq hOne hJ
  let _ : E.Normal := Subgroup.normalClosure_normal
  have hRmap : (twoResidualAmbient (⊤ : Subgroup G)).map q =
      twoResidualAmbient (⊤ : Subgroup X) :=
    map_twoResidualAmbient_of_subgroup_image ⊤ q ⊤ (Subgroup.map_top_of_surjective q hq)
  have hRle : twoResidualAmbient (⊤ : Subgroup G) ≤ E.comap q := by
    apply Subgroup.map_le_iff_le_comap.mp
    rw [hRmap]
    change _ ≤ SectionOne.oneE (V := V) ((S : Subgroup G).map q)
    rw [hEeq]
    exact le_sup_left
  have hgen : E.comap q ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← SectionThree.twoResidual_sup_sylowImage hP.1.2.1]
    exact sup_le_sup_right hRle _
  have hcompl : IsCompl (FixedPoints.subgroup E V) (commutatorAction E V) := by
    have he := (SectionOne.oneSeven_global_identification hOne T).2
    change IsCompl (FixedPoints.subgroup (SectionOne.oneE (V := V) (T : Subgroup X)) V)
      (commutatorAction (SectionOne.oneE (V := V) (T : Subgroup X)) V)
    rw [he]
    exact SectionOne.oneSeven_global_fixed_support_compl
  have hfix := quotientConjugationAction_fixedPoints_le_sylow_of_normal_supplement
    S q hq hker E hgen hcompl.disjoint
  exact SectionOne.exists_oneSevenFactor_fixing_of_not_sylow_fixed hOne T hfix w hwJ hwS

end Stellmacher.SectionTwo
