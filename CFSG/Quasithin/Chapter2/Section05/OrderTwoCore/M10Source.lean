module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.SelectedEightSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalAutomizerSource
public import Theory.SpecificGroups.AlternatingSix.M10.SylowSemidihedral
public import ABG.ChapterII.Section1.SmallSubgroupConjugacy
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupTheory.QuotientTrivialIntersection
/-!
# Excluding an order-two source core in the M10 quotient branch

At core order two, the selected largest pair gives an elementary eight F in
the original Sylow Y, with its central four-group and a crossing conjugate
F^x escaping every Y-conjugate. Both eights contain the literal core. Their
images in the M10 quotient are Klein four subgroups of its semidihedral
Sylow, hence conjugate there. The quotient conjugator lifts to Y and the
kernel-contained eights lift exactly, contradicting escape.
Source: Aschbacher--Smith 2.5.21, printed pp.565--567.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem four_of_elementary_card {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 4) : IsKleinFour A := by
  refine ⟨hcard, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (IsElementaryAbelian.exponent_dvd_p 2 A) with h | h
  · let : Subsingleton A := Monoid.exp_eq_one_iff.mp h
    have hc : Nat.card A = 1 := by simp
    omega
  · exact h

private theorem standard_semidihedral_sixteen :
    Stellmacher.IsSemidihedralGroup (Semidihedral.StandardModel 4 (by decide)) := by
  refine ⟨4, by decide, ?_, Semidihedral.standardRotation 4 (by decide),
    Semidihedral.standardReflection 4 (by decide), ?_, ?_, ?_, ?_⟩
  · rw [Semidihedral.standardModel_card]
  · simpa using Semidihedral.standardRotation_order 4 (by decide)
  · simpa using Semidihedral.standardReflection_order 4 (by decide)
  · simpa using Semidihedral.standard_conjugation 4 (by decide)
  · exact Semidihedral.standard_generators 4 (by decide)

/-- The M10 alternative in original 2.5.21 excludes an order-two actual
two-core. The Γ* hypothesis supplies the selected largest pair. -/
theorem MathieuSourceSetup.m10_twoCore_card_ne_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eQ : (H ⧸ pCore 2 H) ≃* AlternatingSix.M10.extension) :
    Nat.card (twoCore H) ≠ 2 := by
  intro hcard
  let Y : Subgroup G := (S : Subgroup H).map H.subtype
  let C : Subgroup G := twoCore H
  obtain ⟨U,L,E,_,_,_,_,hFY,hFe,hFc,_,hZF,_,_,_,x,_,_,hxN,_,hescape⟩ :=
    MathieuSourceSetup.selected_eight_of_core_card_two c hG hempty hgen hb hstar hcard
  let F : Subgroup G := E ⊔ C
  let Fx : Subgroup G := F.conjBy x⁻¹
  let : IsElementaryAbelian 2 F := hFe
  have hYH : Y ≤ H := map_subtype_le _
  have hCZY : C ≤ centerIn Y := by
    obtain ⟨t,_,ht,_,htC,hCt,_,_,_,_,_,_,_,_,_,_⟩ :=
      MathieuSourceSetup.source_central_marks c hG hempty hgen hb
    have he : C = zpowers t :=
      (eq_of_le_of_card_ge (zpowers_le.mpr htC) (by
        rw [Nat.card_zpowers, ht, hcard])).symm
    rw [he]
    exact hCt ▸ inf_le_left
  have hFxY : Fx ≤ Y := by
    have hy : Y.conjBy x⁻¹ = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
    exact (map_mono hFY).trans hy.le
  have hCFx : C ≤ Fx := by
    have hy : (centerIn Y).conjBy x⁻¹ = centerIn Y := by
      apply mem_normalizer_iff_map_conj_eq.mp
      exact (normalizer (centerIn Y : Set G)).inv_mem
        (normalizes_centerIn (S := Y) (A := normalizer (Y : Set G)) le_rfl hxN)
    exact hCZY.trans (hy ▸ map_mono hZF)
  let : IsElementaryAbelian 2 Fx := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hFxc : Nat.card Fx = 8 := by
    change Nat.card (F.conjBy x⁻¹) = 8
    rw [conjBy, card_map_of_injective (MulAut.conj x⁻¹).injective, hFc]
  obtain ⟨f,hf,hker⟩ := MathieuSourceSetup.exists_surjective_core_model c hgen eQ
  have hkerC : f.ker = C.subgroupOf H := by
    rw [hker]
    exact congrArg (fun W : Subgroup G => W.subgroupOf H)
      (MathieuSourceSetup.core_eq_sylow_centralizer c hgen).symm
  let D : Subgroup H := Y.subgroupOf H
  have hDS : D = (S : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hYH]
  let P := S.mapSurjective hf
  have hDP : D.map f = (P : Subgroup AlternatingSix.M10.extension) := by
    rw [hDS]
    rfl
  let A : Subgroup H := F.subgroupOf H
  let B : Subgroup H := Fx.subgroupOf H
  have hFH : F ≤ H := hFY.trans hYH
  have hFxH : Fx ≤ H := hFxY.trans hYH
  have hAD : A ≤ D := fun _ ha => hFY ha
  have hBD : B ≤ D := fun _ ha => hFxY ha
  have hkerA : f.ker ≤ A := by
    rw [hkerC]
    intro a ha
    exact (show C ≤ F from le_sup_right) ha
  have hkerB : f.ker ≤ B := by
    rw [hkerC]
    exact fun _ ha => hCFx ha
  have hcA : Nat.card A = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv).trans hFc
  have hcB : Nat.card B = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFxH).toEquiv).trans hFxc
  have hcKer : Nat.card f.ker = 2 := by
    rw [hkerC, Nat.card_congr (subgroupOfEquivOfLe (hCZY.trans inf_le_left |>.trans hYH)).toEquiv]
    exact hcard
  have image_card (V : Subgroup H) (hKV : f.ker ≤ V) (hV : Nat.card V = 8) :
      Nat.card (V.map f) = 4 := by
    have h := IsElementaryAbelian.card_inf_ker_mul_card_map V f
    rw [inf_eq_right.mpr hKV, hcKer, hV] at h
    omega
  have hcAf : Nat.card (A.map f) = 4 := image_card A hkerA hcA
  have hcBf : Nat.card (B.map f) = 4 := image_card B hkerB hcB
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hFH
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hFxH
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hAf : IsKleinFour (A.map f) := four_of_elementary_card hcAf
  have hBf : IsKleinFour (B.map f) := four_of_elementary_card hcBf
  have hAP : A.map f ≤ (P : Subgroup AlternatingSix.M10.extension) := by
    rw [←hDP]
    exact map_mono hAD
  have hBP : B.map f ≤ (P : Subgroup AlternatingSix.M10.extension) := by
    rw [←hDP]
    exact map_mono hBD
  have hPsemi : Stellmacher.IsSemidihedralGroup P :=
    ABG.semidihedral_equiv (AlternatingSix.M10.sylowTwoEquivSemidihedral P).symm
      standard_semidihedral_sixteen
  obtain ⟨s, hs⟩ := ABG.QuasiDihedral.four_subgroup_ambient_conjugacy
    (P : Subgroup AlternatingSix.M10.extension) (B.map f) (A.map f)
    hPsemi hBP hAP hBf hAf
  have hsD : (s : AlternatingSix.M10.extension) ∈ D.map f := hDP.symm ▸ s.property
  obtain ⟨sH, hsHD, hsImage⟩ := hsD
  have hkerConj : f.ker ≤ A.conjBy sH := by
    have he : f.ker.map (MulAut.conj sH).toMonoidHom = f.ker :=
      Subgroup.Normal.map_conj_eq _ _
    exact he.ge.trans (map_mono hkerA)
  have hmapped : (A.conjBy sH).map f = B.map f := by
    rw [conjBy, Subgroup.image_conjugate, hsImage]
    exact hs
  have hAB : A.conjBy sH = B :=
    Subgroup.map_injective_of_ker_le f hkerConj hkerB hmapped
  have hambient := congrArg (fun V : Subgroup H => V.map H.subtype) hAB
  rw [conjBy, Subgroup.image_conjugate, map_subgroupOf_eq_of_le hFH,
    map_subgroupOf_eq_of_le hFxH] at hambient
  have hsY : (sH : G) ∈ Y := hsHD
  apply hescape (sH⁻¹ : G) (Y.inv_mem hsY)
  change Fx = F.conjBy ((sH : G)⁻¹)⁻¹
  rw [inv_inv, conjBy]
  exact hambient.symm
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
