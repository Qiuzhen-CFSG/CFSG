module
public import Stellmacher.SectionTwo.TwoFourLocalFactor
public import Stellmacher.SectionTwo.NativeBaumannActionFactors

/-!
# A generating local factor with its original action module

The noncentral Section Two setting supplies a local subgroup K whose Sylow
image is B(S), whose nested Frattini quotient is SL₂(2), and which generates
the ambient group together with S. This refinement retains a normal quotient
factor D contained in the image of K, with its four-element derived action
on the original V=⟨Ω₁(Z(S))^G⟩. The exact quotient-conjugation action is shared
throughout. No assertion that [V,K] itself has order four is made.

The rich native Baumann product supplies the factor family. The generating
coordinate lift is applied to that same family, and its image formula places
the chosen D inside the image of K. The (2.2) normal closure identity identifies
the family join with the image of the actual Baumann normal closure.

Source: Stellmacher (2.2)--(2.4) and the selected local factor in (6.1),
Journal of Algebra 190 (1997), pp.20 and30.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem two_four_exists_local_action_factor
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (hcore : pCore 2 G =
      (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G))
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    letI := quotientConjugationAction S q hq hker
    let B := (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
    let L := Subgroup.normalClosure (B : Set G)
    ∃ (K : Subgroup G) (PK : Sylow 2 K) (D : Subgroup barG),
      B ≤ K ∧ K ≤ L ∧ (PK : Subgroup K).map K.subtype = B ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      K ⊔ (S : Subgroup G) = ⊤ ∧
      D ≤ K.map q ∧ (D.subgroupOf (L.map q)).Normal ∧
      SectionOne.IsOneSevenFactor (V := vSubgroup S) D := by
  classical
  let _ := quotientConjugationAction S q hq hker
  let B := (S : Subgroup G) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let T := S.mapSurjective hq
  let Jbar := J.map q
  let Bbar := B.map q
  let Ebar := ⁅SectionOne.oddCore barG, Jbar⁆ ⊔ Jbar
  have hJne : Jbar ≠ ⊥ := by
    intro hbot
    have hJC : J ≤ Subgroup.centralizer (vSubgroup S : Set G) := by
      change J ≤ cSubgroup S
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff J).mp hbot
    exact hnot (Subgroup.le_centralizer_iff.mp hJC)
  have h22 := lemma_two_two h S q hq hker
    ((S : Subgroup G).map q) Jbar Bbar rfl B rfl rfl rfl hJne
  have hJleT : Jbar ≤ (T : Subgroup barG) :=
    (Subgroup.map_mono (show J ≤ (S : Subgroup G) from sSup_le fun _ hA => hA.1)).trans_eq
      (Sylow.coe_mapSurjective hq S).symm
  have hJinf : Jbar = (T : Subgroup barG) ⊓ Ebar := by
    simpa only [Ebar, SectionOne.oddCore] using
      (SectionOne.oddCore_commutator_join_sylow_inf T Jbar hJleT)
  have hEnormal : Ebar.Normal := h22.part_a
  let _ : Ebar.Normal := hEnormal
  have hclosure : Subgroup.normalClosure (Jbar : Set barG) = Ebar := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal (fun _ hx => (show Jbar ≤ Ebar from le_sup_right) hx)
    · exact sup_le
        ((Subgroup.commutator_mono le_rfl Subgroup.le_normalClosure).trans
          (Subgroup.commutator_le_right _ _)) Subgroup.le_normalClosure
  have hLmap : L.map q = Ebar := by
    rw [show L = Subgroup.normalClosure (B : Set G) from rfl,
      Subgroup.map_normalClosure _ q hq]
    change Subgroup.normalClosure (Bbar : Set barG) = Ebar
    rw [← h22.part_b]
    exact hclosure
  have hBclosure : Subgroup.normalClosure (Bbar : Set barG) = Ebar := by
    rw [← h22.part_b]
    exact hclosure
  obtain ⟨P, hPmap⟩ := lemma_two_three h S hcore B L rfl rfl
  obtain ⟨K₀, PK₀, _hBK₀, hK₀L, _hPK₀, _hK₀SL, hK₀gen⟩ :=
    two_four_exists_local_sl2Frattini_factor h S hcore hnot hunique
  have hgenL : L ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← hK₀gen]
    exact sup_le_sup_right hK₀L _
  obtain ⟨_hJB, n, D, hDgen, hDprod, _hDinj, hDF, hDN, _hVprod⟩ :=
    nativeBaumann_action_factors h S q hq hker B rfl hJne
  rw [hBclosure] at hDgen hDprod hDN
  obtain ⟨K, PK, i, hBK, hKL, hPK, hKSL, hgen, hKimage⟩ :=
    exists_generating_coordinate_frattini_lift_with_image h.solvable S T q hq
      Jbar Ebar B L P hPmap h22.part_b.symm hJinf hJne hLmap hgenL
      hunique hEnormal D hDprod (fun i => (hDF i).1)
  refine ⟨K, PK, D i, hBK, hKL, hPK, hKSL, hgen, ?_, ?_, hDF i⟩
  · rw [hKimage]
    exact le_sup_left
  · rw [hLmap]
    exact hDN i

end Stellmacher.SectionTwo
