module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalRows
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.PairedQuotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.SolvableFlags
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryResidual

/-!
# The binary terminal pair quotient and contradiction

The actual natural-five point-parabolic marking extends the component map
across S. The image of the literal KS is solvable, contains a Sylow
2-subgroup of GL₅(2), and retains the original residual's cubic rank two
through the two-group kernel. The solvable flag theorem then gives two
nonadjacent rank-one diagonal blocks, hence its S₃ × S₃ two-core quotient.
Transport through the original maps identifies KS/O₂(KS) with this quotient.

The preceding terminal row exclusions supply this natural-five marking
without a KS quotient premise. The resulting binary contradiction therefore
discharges every local small-action input. The final component application
also derives X = O^{3′}(I), I-normality and K ≤ X from the existing actual
binary residual theorem. Earlier plane geometry, component-orbit and NI/Omega
source inputs remain explicit for the plane-uniqueness assembly owner.

Source: Aschbacher--Smith 15.2.21 and the binary terminal branch of15.2.23,
printed pp.1114,1117; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction TerminalLinear
open BinaryLinear.OuterCyclic

private theorem pair_of_solvable_sylow_overgroup
    (P : Sylow 2 (LinearGroup 5)) (A : Subgroup (LinearGroup 5))
    [Group.IsSolvable A] (hPA : (P : Subgroup (LinearGroup 5)) ≤ A)
    (hr : 2 ≤ primeRank 3 A) :
    Nonempty ((A ⧸ pCore 2 A) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have h9 : 9 ∣ Nat.card A := by
    by_contra hh
    have h := primeRank_le_one_of_square_not_dvd (p := 3) hh
    omega
  have hc : Nat.card (LinearGroup 5) = 9999360 := by
    rw [← Nat.card_congr (matrixEquivLinear 5).toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hlo : 2 ≤ (Nat.card A).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h9
  have hhi : (Nat.card A).factorization 3 < 3 := by
    by_contra hh
    have hd : 3 ^ 3 ∣ Nat.card A :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr
        (Nat.le_of_not_gt hh)
    have hdG := hd.trans A.card_subgroup_dvd_card
    rw [hc] at hdG
    norm_num at hdG
  have hthree : (Nat.card A).factorization 3 = 2 := by omega
  obtain ⟨b,cuts,rfl⟩ := BinaryLinear.FiveFlagGeometry.isFlagParabolic_of_sylow_le P A hPA
  obtain ⟨i,j,_,hij,rfl⟩ :=
    BinaryLinear.SmallParabolicLevi.TwoNodes.cuts_eq_compl_pair_of_solvable_three_part
      b cuts inferInstance hthree
  exact ⟨(BinaryLinear.SmallParabolicLevi.TwoNodes.flagDiagonalQuotientEquiv b _).trans
    (BinaryLinear.SmallParabolicLevi.TwoNodes.pairFactorsEquiv i j hij)⟩

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The literal KS quotient in the natural-five row. Its image is a solvable
Sylow overgroup of GL₅(2), with two nonadjacent rank-one diagonal blocks. -/
theorem pair_quotient_of_point_image
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (v : Fin 5 → ZMod 2) (hv : v ≠ 0)
    (hm : (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      e.toMonoidHom = MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) v) :
    Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let S := smallActionS T ZS
  let E := X ⊔ S
  let J := KS H T ZS
  let N := J.subgroupOf E
  have hSI : S ≤ I := (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hEI : E ≤ I := sup_le hXI hSI
  have hJE : J ≤ E := sup_le_sup_right hKX S
  obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict
    (show S ≤ E from le_sup_right) hEI
  obtain ⟨f,hf,hker,_⟩ := point_image_extension d hI hn e v hv hm
  let A := N.map f
  let Q := P.mapSurjective hf
  have hQA : (Q : Subgroup (LinearGroup 5)) ≤ A := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨x,?_,rfl⟩
    exact (show S ≤ J from le_sup_right) (hP ▸ mem_map_of_mem E.subtype hx)
  have hJH : J ≤ H := sup_le (map_subtype_le _)
    (inf_le_left.trans d.geometry.outside.1.1.2)
  obtain ⟨eH⟩ := d.geometry.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  let : Group.IsSolvable H := Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk',range_subtype])
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJH)
  let a := subgroupOfEquivOfLe hJE
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := a.toMonoidHom) a.injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective (f.subgroupMap_surjective N)
  have hr : 2 ≤ primeRank 3 A := by
    rw [show A = N.map f from rfl,
      ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) f hker,
      primeRank_equiv 3 a]
    exact (PlaneUniquenessPreceding.LinearThree.residual_rank_two d).symm.le.trans
      (primeRank_mono 3 (show smallActionK H ≤ J from le_sup_left))
  obtain ⟨ep⟩ := pair_of_solvable_sylow_overgroup Q A hQA hr
  have hkN : IsPGroup 2 (f.subgroupMap N).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hker.comap_subtype
  let eq := (f.subgroupMap N).pCoreQuotientEquiv (f.subgroupMap_surjective N) hkN
  exact ⟨(QuotientGroup.congr (pCore 2 J) (pCore 2 N) a.symm (pCore_map_iso 2 a.symm)).trans
    (eq.trans ep)⟩

/-- The actual binary component supplies its KS pair quotient internally. -/
theorem binaryBranch_pair_quotient
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := U_elementary d hI hfit b.source.component.1
  obtain ⟨_,r,_,_,e,v,hv,hm⟩ :=
    binaryBranch_repeatedNatural_from_wreath d hI hfit hn hout b hX hKX
  exact pair_quotient_of_point_image d hI b.source.component.1 hn hKX e.groupEquiv v hv hm

/-- The binary terminal contradiction with every local small-action premise
discharged. Only the authorized earlier plane, component and NI/Omega inputs remain. -/
theorem binaryBranch_false_from_preceding
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) → False :=
  binaryBranch_false_from_smallActions d hquotient horbit hI hfit hn hout b hX hKX
    (binaryBranch_pair_quotient d hI hfit hn hout b hX hKX) hNI eNI

/-- Application to the selected binary component, deriving its relative
normality and residual placements from the existing component theorem. -/
theorem binaryComponent_false_from_preceding
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : ¬ X ≤ Mc) {n : ℕ} (b : BinaryBranch M I X n)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) → False := by
  have hX := ComponentCatalogue.binary_eq_threeResidual (hsource := hsource) hI b
  have hn := ComponentCatalogue.binary_normalized (hsource := hsource) hI b
  have hKX : (pResidual 2 H).map H.subtype ≤ X :=
    (ComponentCatalogue.binary_residual_le_M1 d hI b).trans inf_le_left
  exact binaryBranch_false_from_preceding d hquotient horbit hI hfit hn hout b hX hKX hNI eNI

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
