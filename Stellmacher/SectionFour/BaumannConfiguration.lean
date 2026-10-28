module

public import Stellmacher.SectionFour.LemmaFourFive
public import Stellmacher.SectionFour.OutsideMember
public import Stellmacher.SectionFour.BaumannPartner
public import Stellmacher.SectionFour.BaumannResidual
public import Stellmacher.SectionFour.LocalCharacteristicTwo

/-!
# The initial Baumann configuration in Stellmacher (4.6)

Assume the two-family cover and, toward the contradiction of (4.6), that
the family starred over `C` is contained in the family over `M`. This module
constructs the source pair `(P,Pstar)`, with `P ≤ C` and `Pstar` starred
over `M`, and the product `E = O²(Pstar)O₂(C)` having Sylow subgroup
`O₂(C)`. It also proves that `Pstar` is solvable of characteristic 2.

For `B₀ = C_{O₂(C)}(Ω₁(Z(J(O₂(C)))))`, the imported Baumann results give
normality in `S` and nonnormalization by `Pstar`. The residual/Sylow
factorization gives `Pstar ≤ E ⋁ S`. Applying (3.4), with the hereditary
Baumann identity to exclude its core branch, gives
`[O²(Pstar),B₀] = O²(Pstar)`. In particular the residual lies in the normal
closure of `B₀` inside `Pstar`, the local group used next in the source.

Source: `refs/latex/stellmacher-n-group.tex`, the first two paragraphs of
the proof of (4.6), through the application of (3.4).
-/

open scoped Pointwise

namespace Stellmacher.SectionFour

universe u

private theorem four_six_opening
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (mSubgroup S) (S : Subgroup G))
    (hstar : SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
      SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ∃ P Pstar E : Subgroup G,
      P ∈ SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∧
      P ∉ SectionThree.PSet (mSubgroup S) (S : Subgroup G) ∧
      Pstar ∈ SectionThree.PStarSet (mSubgroup S) (S : Subgroup G) ∧
      (P, Pstar) ∈ Lambda S ∧
      twoCoreAmbient (mSubgroup S) ≤ twoCoreAmbient (cSubgroup S) ∧
      (E : Set G) = (twoResidualAmbient Pstar : Set G) *
        (twoCoreAmbient (cSubgroup S) : Set G) ∧
      IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E := by
  obtain ⟨P, hP, hPM⟩ := exists_pSet_not_mem_mSubgroup S h
  have hPC : P ∈ SectionThree.PSet (cSubgroup S) (S : Subgroup G) := by
    rw [hcover] at hP
    exact hP.resolve_right hPM
  obtain ⟨Pstar, hPstar, hpair, hconditional⟩ :=
    lemma_four_five S h (hcover.trans (Set.union_comm _ _)) P hP hPM
  obtain ⟨hcore, E, hE, hSyl⟩ := hconditional hstar
  exact ⟨P, Pstar, E, hPC, hPM, hPstar, hpair, hcore, hE, hSyl⟩


private theorem pSet_sylow_le
    {G : Type u} [Group G] {S P U : Subgroup G}
    (hP : P ∈ SectionThree.PSet U S) : S ≤ P := by
  obtain ⟨T, hT⟩ := hP.1.2.1
  rw [← hT]
  exact Subgroup.map_subtype_le _

private theorem le_normalizer_core
    {G : Type u} [Group G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 L))).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

private theorem four_six_residual_setup
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P Pstar E : Subgroup G)
    (hpair : (P, Pstar) ∈ Lambda S) (hPC : P ≤ cSubgroup S)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G)) :
    let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
    Group.IsSolvable Pstar ∧ E ≤ Pstar ∧ Pstar ≤ E ⊔ (S : Subgroup G) ∧
      B ≤ (S : Subgroup G) ∧ (B.subgroupOf (S : Subgroup G)).Normal ∧
      ¬ Pstar ≤ Subgroup.normalizer (B : Set G) := by
  dsimp only
  let Q := twoCoreAmbient (cSubgroup S)
  let B := Q ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G)
  have hSP := pSet_sylow_le hpair.1
  have hSPstar := pSet_sylow_le hpair.2.1
  have hSC : (S : Subgroup G) ≤ cSubgroup S := hSP.trans hPC
  have hQS : Q ≤ (S : Subgroup G) := by
    let T : Sylow 2 (cSubgroup S) := S.subtype hSC
    have hTmap : (T : Subgroup (cSubgroup S)).map (cSubgroup S).subtype =
        (S : Subgroup G) := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSC]
    rw [← hTmap]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := cSubgroup S)).le_sylow_of_normal T)
  have hA : twoResidualAmbient Pstar ≤ Pstar := Subgroup.map_subtype_le _
  have hAE : twoResidualAmbient Pstar ≤ E := by
    intro a ha
    have haE : a ∈ (twoResidualAmbient Pstar : Set G) * (Q : Set G) :=
      ⟨a, ha, 1, Q.one_mem, mul_one a⟩
    rwa [← hE] at haE
  have hEP : E ≤ Pstar := by
    intro e he
    change e ∈ (E : Set G) at he
    rw [hE] at he
    obtain ⟨a, ha, q, hq, rfl⟩ := he
    exact Pstar.mul_mem (hA ha) (hSPstar (hQS hq))
  have hPS : Pstar ≤ E ⊔ (S : Subgroup G) := by
    have hfact : twoResidualAmbient Pstar ⊔ (S : Subgroup G) = Pstar :=
      SectionThree.twoResidual_sup_sylowImage hpair.2.1.1.2.1
    rw [← hfact]
    exact sup_le (hAE.trans le_sup_left) le_sup_right
  have hBS : B ≤ (S : Subgroup G) := inf_le_left.trans hQS
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    ((hSC.trans (le_normalizer_core _)).trans (normalizer_le_normalizer_baumann _))
  have hsolv : Group.IsSolvable Pstar := by
    let N := Subgroup.normalizer (twoCoreAmbient Pstar : Set G)
    have hPN : Pstar ≤ N := le_normalizer_core _
    have hNlocal : IsTwoLocal N :=
      ⟨twoCoreAmbient Pstar, hpair.2.1.1.2.2.1,
        (pCore_isPGroup (p := 2) (G := Pstar)).map Pstar.subtype, rfl⟩
    let _ : Group.IsSolvable N :=
      (h.local_solvable_characteristicTwo N hNlocal (hSPstar.trans hPN)).1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hPN)
  exact ⟨hsolv, hEP, hPS, hBS,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr hSN,
    baumann_not_normalized_by_partner S h.even_order P Pstar hpair hPC⟩


private theorem four_six_full_commutator
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P Pstar E : Subgroup G)
    (hpair : (P, Pstar) ∈ Lambda S) (hPC : P ≤ cSubgroup S)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    ⁅twoResidualAmbient Pstar,
      twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) :
          Set G)⁆ = twoResidualAmbient Pstar := by
  obtain ⟨hsolv, hEP, hPS, hBS, hBN, hnot⟩ :=
    four_six_residual_setup S h P Pstar E hpair hPC hE
  exact baumann_partner_full_commutator (S : Subgroup G)
    ⟨h.even_order, S.ne_bot_of_dvd_card h.even_order.two_dvd, S.isPGroup'⟩
    Pstar (twoCoreAmbient (cSubgroup S)) E _ hpair.2.1 hsolv hEP hPS hSyl rfl
    hBS hBN hnot


private theorem commutator_le_normalClosureIn
    {G : Type u} [Group G] (P A B : Subgroup G)
    (hAP : A ≤ P) (hBP : B ≤ P) :
    ⁅A, B⁆ ≤ (Subgroup.normalClosure (B.subgroupOf P : Set P)).map P.subtype := by
  calc
    ⁅A, B⁆ = ⁅A.subgroupOf P, B.subgroupOf P⁆.map P.subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAP,
        Subgroup.map_subgroupOf_eq_of_le hBP]
    _ ≤ _ := Subgroup.map_mono
      ((Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure).trans
        (Subgroup.commutator_le_right _ _))

/-- The initial Baumann configuration forced by the hypothetical containment in (4.6). -/
public theorem exists_baumann_configuration
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hcover : SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) =
      SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∪
        SectionThree.PSet (mSubgroup S) (S : Subgroup G))
    (hstar : SectionThree.PStarSet (cSubgroup S) (S : Subgroup G) ⊆
      SectionThree.PSet (mSubgroup S) (S : Subgroup G)) :
    ∃ P Pstar E : Subgroup G,
      P ∈ SectionThree.PSet (cSubgroup S) (S : Subgroup G) ∧
      Pstar ∈ SectionThree.PStarSet (mSubgroup S) (S : Subgroup G) ∧
      (P, Pstar) ∈ Lambda S ∧
      twoCoreAmbient (mSubgroup S) ≤ twoCoreAmbient (cSubgroup S) ∧
      (E : Set G) = (twoResidualAmbient Pstar : Set G) *
        (twoCoreAmbient (cSubgroup S) : Set G) ∧
      IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E ∧
      Group.IsSolvable Pstar ∧ IsCharacteristicTwoType Pstar ∧
      E ≤ Pstar ∧ Pstar ≤ E ⊔ (S : Subgroup G) ∧
      let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
      B ≤ (S : Subgroup G) ∧ (B.subgroupOf (S : Subgroup G)).Normal ∧
      ⁅twoResidualAmbient Pstar, B⁆ = twoResidualAmbient Pstar ∧
      twoResidualAmbient Pstar ≤
        (Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)).map Pstar.subtype := by
  obtain ⟨P, Pstar, E, hPC, _, hPstarM, hpair, hcore, hE, hSyl⟩ :=
    four_six_opening S h hcover hstar
  obtain ⟨hsolv, hEP, hPS, hBS, hBN, hnot⟩ :=
    four_six_residual_setup S h P Pstar E hpair hPC.1.1 hE
  have hcomm := four_six_full_commutator S h P Pstar E hpair hPC.1.1 hE hSyl
  refine ⟨P, Pstar, E, hPC, hPstarM, hpair, hcore, hE, hSyl, hsolv,
    characteristicTwo_of_mem_pSet S h Pstar hpair.2.1, hEP, hPS,
    hBS, hBN, hcomm, ?_⟩
  rw [← hcomm]
  exact commutator_le_normalClosureIn Pstar _ _ (Subgroup.map_subtype_le _)
    (hBS.trans (pSet_sylow_le hpair.2.1))


end Stellmacher.SectionFour
