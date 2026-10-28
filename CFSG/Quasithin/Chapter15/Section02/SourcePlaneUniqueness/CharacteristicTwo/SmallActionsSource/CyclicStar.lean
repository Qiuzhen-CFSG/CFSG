module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.SeedAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MiddleParabolic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCubicSylow
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaStarSetup
public import Theory.GroupTheory.CubicSectionKernel

/-!
# Excluding the original cyclic star residual

The original star residual is a normal cubic in M/O₂(M). An arbitrary
outside seed provides another cubic whose actual module image is not normal.
The two detected cubics exhaust the three-rank, forcing the literal star
kernel, and hence C_M(V), to have order prime to three. The middle-parabolic
seed in C_M(V) then contradicts reducibility of the L₄(2) component.

This proves the cyclic branch of the local split exclusion, retaining the
original seed, NI action, Y-star quotient and Kc marking throughout.
The preceding wreath, component-orbit and NI-image inputs retain their
existing source owners and final discharge in qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith 15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I Y₁ : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original cyclic star branch and an arbitrary outside seed force
C_M(V) to have order prime to three. -/
theorem cyclic_star_centralizer_coprime
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) Y₁) (hout : ¬ Y₁ ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
  let := hsource.prepared.elementary
  dsimp only
  intro ho hYbar
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let q := QuotientGroup.mk' (pCore 2 M)
  let g := omegaStarActor hsource.prepared.normalized ho
  let e := ho.2.2.2.1.some
  let f := e.toMonoidHom.comp g
  let A := (Y.subgroupOf M).map q
  obtain ⟨B,hBY,hB,hBimage⟩ := s.exists_cubic_action_lift d hI hout eNI
  let D := B.map q
  let : (Y.subgroupOf M).Normal := source_omega_lemma_15_2_3_2 T
    hsource.maximal.1.2 hsource.prepared.normalized ho
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hf : Function.Surjective f := e.surjective.comp
    (QuotientGroup.lift_surjective_of_surjective _ _
      (actionHom M V hsource.prepared.normalized).rangeRestrict_surjective
      (source_omega_core_le_kernel hsource.prepared.normalized ho))
  have hA : Nat.card A = 3 := source_omega_cyclic_star_card T hsource.maximal.1.2
    hsource.partner hsource.prepared ho hYbar
  have hqcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hiB : Function.Injective (q.comp B.subtype) :=
    injective_comp_subtype_of_coprime_ker q hqcop B
      (IsPGroup.of_card (n := 1) (by simpa using hB))
  have hD : Nat.card D = 3 := by
    let eb := MulEquiv.ofBijective (q.subgroupMap B)
      ⟨fun x y hh => hiB (congrArg Subtype.val hh),q.subgroupMap_surjective B⟩
    exact (Nat.card_congr eb.toEquiv).symm.trans hB
  have hm (L : Subgroup M) : (L.map q).map f =
      (L.map (action hsource)).map e.toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have hfA : Nat.card (A.map f) = 3 := by
    rw [hm,card_map_of_injective e.injective]
    exact hYbar
  have hRcard : Nat.card (residualImage hsource I) = 3 := by
    rw [card_map_of_injective (intersectionImage hsource I).subtype_injective]
    have hh := congrArg (fun K : Subgroup (Equiv.Perm (Fin 3)) => Nat.card K)
      (map_pResidual_of_surjective 2 eNI.toMonoidHom eNI.surjective)
    rwa [card_map_of_injective eNI.injective,
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at hh
  have hfD : Nat.card (D.map f) = 3 := by
    rw [hm,card_map_of_injective e.injective,hBimage]
    exact hRcard
  have hn : ¬ (D.map f).Normal := by
    rw [hm,hBimage]
    intro hn
    have hh := hn.comap e.toMonoidHom
    rw [comap_map_eq_self_of_injective e.injective] at hh
    exact residualImage_not_normal d hI (fun h => hout (s.le_NI.trans h)) hh
  have hr : primeRank 3 (M ⧸ pCore 2 M) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup]
    exact (hsource.ambient.twoLocal_sqtk hsource.maximal.1.1.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hcop := coprime_kernel_of_normal_and_nonnormal_cubics hr f hf A D hA hD hfA hfD hn
  have hfg : f.ker = g.ker := by
    ext x
    exact ⟨fun hx => e.injective (hx.trans e.map_one.symm),fun hx => by
      change e (g x) = 1
      rw [show g x = 1 from hx]
      exact e.map_one⟩
  let C := (M ⊓ centralizer (V : Set G)).subgroupOf M
  have hgc : g.ker = C.map q := omegaStarActor_ker hsource.prepared.normalized ho
  rw [hfg,hgc] at hcop
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hkc : Nat.Coprime 3 (Nat.card (q.subgroupMap C).ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hCc : Nat.card C = Nat.card (C.map q) * Nat.card (q.subgroupMap C).ker := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (q.subgroupMap C) (q.subgroupMap_surjective C)).toEquiv]
    exact card_eq_card_quotient_mul_card_subgroup (q.subgroupMap C).ker
  have hc : Nat.Coprime 3 (Nat.card C) := by
    rw [hCc]
    exact hcop.mul_right hkc
  rwa [Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_left : M ⊓ centralizer (V : Set G) ≤ M)).toEquiv] at hc

/-- The original cyclic alternative cannot coexist with a reducible L₄(2)
component and the source outside seed. -/
theorem linearFour_not_cyclic_star
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) Y₁) (hout : ¬ Y₁ ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 → False := by
  let := hsource.prepared.elementary
  dsimp only
  intro ho hc
  have hcop := cyclic_star_centralizer_coprime d hI s hout eNI ho hc
  have hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
    apply bot_unique
    apply primeToResidual_le
    rwa [index_bot]
  exact hnot (linearFour_irreducible_of_threePrime d hquotient horbit hI hC eK)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
