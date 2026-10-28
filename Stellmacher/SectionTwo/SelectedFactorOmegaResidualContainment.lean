module
public import Stellmacher.SectionTwo.GlobalOffenderFixingFactor
public import Stellmacher.SectionTwo.SelectedFactorResidualModule
public import Theory.GroupAction.ThreeActionFourSupport

/-!
# A selected factor's module inside the omega-residual commutator

In the Section Two setting, assume the group belongs to the local P-family
over its supplied Sylow and the global offender subgroup is nontrivial.
For any specified raw one-seven factor D and subgroup F whose quotient
image contains D, the four-element D-module lies in
[Omega1(Z(S)), O^2(F)]. All actions use the original named centralizer
quotient; no Sylow invariance of D is assumed.

The local-family residual theorem gives a normal product E supplementing S,
and E normalizes D and its derived group of order three. If that derived
group fixed the omega-center, every conjugate of the omega-center would
also be fixed: factor its conjugator as e*s, use centralization by s, and
normalization of the derived group by e. This would kill its action on
the defining normal closure V, contrary to its four-element support.
The order-three orbit lemma therefore identifies the restricted action
commutator on the omega-center with the full support. The derived group
lies in the quotient image of O^2(F), since it has odd order. Lifting its
actors transports each restricted commutator generator into the literal
ambient omega-residual commutator.

Source: Stellmacher (6.4), Journal of Algebra 190 (1997), p.32, the selected
Vj contained in U=[Z,O^2(F1)]. The barred setup follows the journal scan;
refs/latex/stellmacher-n-group.tex is the accompanying transcription.
-/

namespace Stellmacher.SectionTwo
open scoped IsMulCommutative
universe u

private theorem normalClosure_centralizes_of_supplement
    {G : Type u} [Group G] (E S Z K : Subgroup G) [E.Normal]
    (hgen : E ⊔ S = ⊤) (hZS : Z ≤ Subgroup.centralizer (S : Set G))
    (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hZK : Z ≤ Subgroup.centralizer (K : Set G)) :
    Subgroup.normalClosure (Z : Set G) ≤ Subgroup.centralizer (K : Set G) := by
  have hNC : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (inferInstance : ((Subgroup.centralizer (K : Set G)).subgroupOf
        (Subgroup.normalizer (K : Set G))).Normal)
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨z, hz, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  obtain ⟨e, he, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
    (show g ∈ E ⊔ S by rw [hgen]; trivial)
  have hscent := Subgroup.mem_centralizer_iff.mp (hZS hz) s hs
  have hsfix : s * z * s⁻¹ = z := by rw [hscent, mul_inv_cancel_right]
  have hzcent := (Subgroup.mem_normalizer_iff.mp (hNC (hEK he)) z).mp (hZK hz)
  have heq : (e * s) * z * (e * s)⁻¹ = e * z * e⁻¹ := by
    calc
      _ = e * (s * z * s⁻¹) * e⁻¹ := by group
      _ = _ := by rw [hsfix]
  rwa [heq]

private theorem selected_factor_nonfixed_omega
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    (S : Sylow 2 G) (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S) (E D : Subgroup X) [E.Normal]
    (hgen : E.comap q ⊔ (S : Subgroup G) = ⊤)
    (hED : E ≤ Subgroup.normalizer (D : Set X)) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
      ¬ (zSubgroup S).subgroupOf (vSubgroup S) ≤
        FixedPoints.subgroup ((commutator D).map D.subtype) (vSubgroup S) := by
  let _ := quotientConjugationAction S q hq hker
  intro hD hfix
  let V := vSubgroup S
  let Z := zSubgroup S
  let A := (commutator D).map D.subtype
  have hZA : Z ≤ Subgroup.centralizer (A.comap q : Set G) := by
    intro z hz
    have hzV : z ∈ V := Subgroup.le_normalClosure hz
    have hm := Subgroup.mem_map_of_mem V.subtype (hfix (show (⟨z, hzV⟩ : V) ∈ Z.subgroupOf V from hz))
    rw [quotientConjugationAction_fixedPoints_map S q hq hker] at hm
    exact hm.2
  have hEA : E ≤ Subgroup.normalizer (A : Set X) := by
    intro e he
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hm := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hED he)
    dsimp only [A]
    rw [Subgroup.map_subtype_commutator, Subgroup.map_commutator, hm]
  have hEAn : E.comap q ≤ Subgroup.normalizer (A.comap q : Set G) :=
    (Subgroup.comap_mono hEA).trans (Subgroup.le_normalizer_comap q)
  have hZS : Z ≤ Subgroup.centralizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact ((mem_omegaOneCenterAmbient_iff (S : Subgroup G) z).mp hz).2.2 s hs
  have hVA : V ≤ Subgroup.centralizer (A.comap q : Set G) :=
    normalClosure_centralizes_of_supplement (E.comap q) S Z (A.comap q) hgen hZS hEAn hZA
  have hcomm : (commutatorAction A V).map V.subtype = ⊥ := by
    rw [quotientConjugationAction_commutator_map S q hq hker]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp hVA)
  have hbot : commutatorAction A V = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp hcomm
  have hcard : Nat.card (commutatorAction A V) = 4 := by
    rw [← SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    exact hD.2.2.1
  have hcard1 := Subgroup.card_eq_one.mpr hbot
  omega

private theorem threeSubgroup_le_twoResidualAmbient
    {X : Type u} [Group X] [Finite X] (A J : Subgroup X)
    (hAJ : A ≤ J) (hA : IsPGroup 3 A) : A ≤ twoResidualAmbient J := by
  let AJ := A.subgroupOf J
  have hAJ3 : IsPGroup 3 AJ := hA.comap_of_injective J.subtype J.subtype_injective
  have hAJR : AJ ≤ twoResidualSubgroup J := by
    intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    rintro N ⟨hN, n, hn⟩
    let _ : N.Normal := hN
    let f := QuotientGroup.mk' N
    have hquot : IsPGroup 2 (J ⧸ N) := IsPGroup.of_card (by
      simpa only [Subgroup.index_eq_card] using hn)
    have himg3 : IsPGroup 3 (AJ.map f) := hAJ3.map f
    have himg2 : IsPGroup 2 (AJ.map f) := hquot.to_subgroup (AJ.map f)
    have himg : AJ.map f = ⊥ := disjoint_self.mp
      (IsPGroup.disjoint_of_ne 3 2 (by decide) (AJ.map f) (AJ.map f) himg3 himg2)
    have hker := (Subgroup.map_eq_bot_iff AJ).mp himg hx
    simpa only [f, QuotientGroup.ker_mk'] using hker
  calc
    A = AJ.map J.subtype := (Subgroup.map_subgroupOf_eq_of_le hAJ).symm
    _ ≤ (twoResidualSubgroup J).map J.subtype := Subgroup.map_mono hAJR
    _ = twoResidualAmbient J := rfl

/-- A specified factor's module lies in the actual omega-residual commutator. -/
public theorem selected_factor_omega_residual_containment
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hP : (⊤ : Subgroup G) ∈ SectionThree.PSet ⊤ (S : Subgroup G))
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S) :
    letI := quotientConjugationAction S q hq hker
    SectionOne.oneJ (V := vSubgroup S) ((S : Subgroup G).map q) ≠ ⊥ →
      ∀ (D : Subgroup X), SectionOne.IsOneSevenFactor (V := vSubgroup S) D →
      ∀ F : Subgroup G, D ≤ F.map q →
      (commutatorAction D (vSubgroup S)).map (vSubgroup S).subtype ≤
        ⁅omegaOneCenterAmbient (S : Subgroup G), twoResidualAmbient F⁆ := by
  classical
  let V := vSubgroup S
  let _ := quotientConjugationAction S q hq hker
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let T := S.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (T : Subgroup X)
  let E := SectionOne.oneE (V := V) (T : Subgroup X)
  intro hJ D hD F hDF
  have hJS : J ≤ (T : Subgroup X) := sSup_le fun _ ha => ha.1
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
  obtain ⟨_, hprod, _⟩ := SectionOne.oneSeven_global_product hOne T
  have hEid := (SectionOne.oneSeven_global_identification hOne T).2
  change E = SectionOne.oneSevenGenerated (G := X) (V := V) at hEid
  have hED : E ≤ Subgroup.normalizer (D : Set X) := by
    rw [hEid]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sSup hD)).mp
      (hprod.2.1 D ((SectionOne.mem_oneSevenFactors_iff D).mpr hD))
  let A := (commutator D).map D.subtype
  let Z := (zSubgroup S).subgroupOf V
  have hnon : ¬ Z ≤ FixedPoints.subgroup A V :=
    selected_factor_nonfixed_omega S q hq hker E D hgen hED hD
  have hAcard : Nat.card A = 3 := hD.2.1.2.1
  have hfull := SectionOne.oneSevenFactor_full_commutator_eq_derived D hD
  have hMcard : Nat.card (commutatorAction A V) = 4 := by
    rw [← hfull]
    exact hD.2.2.1
  have hmodule : commutatorSubgroup A V Z = commutatorAction D V :=
    (three_action_commutator_eq_four_support Z hAcard hMcard hnon).trans hfull.symm
  have hAR : A ≤ (twoResidualAmbient F).map q := by
    rw [map_twoResidualAmbient_of_subgroup_image F q (F.map q) rfl]
    exact threeSubgroup_le_twoResidualAmbient A (F.map q)
      ((Subgroup.map_subtype_le _).trans hDF)
      (IsPGroup.of_card (n := 1) (by simpa using hAcard))
  rw [← hmodule, Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, z, hz, rfl⟩
  obtain ⟨r, hr, hra⟩ := hAR a.property
  change (z : G)⁻¹ * (((a : X) • z : V) : G) ∈
    (⁅omegaOneCenterAmbient (S : Subgroup G), twoResidualAmbient F⁆ : Subgroup G)
  rw [← hra, quotientConjugationAction_smul_coe S q hq hker]
  have hz' : (z : G) ∈ omegaOneCenterAmbient (S : Subgroup G) := hz
  have hc := Subgroup.commutator_mem_commutator
    ((omegaOneCenterAmbient (S : Subgroup G)).inv_mem hz') hr
  simpa only [commutatorElement_def, inv_inv, mul_assoc] using hc

end Stellmacher.SectionTwo
