module

public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# A unique C-component and the solvable residual

Suppose a finite group H has a unique C-component K and the Fitting subgroup
of H/O₂(H) is trivial. The component correspondence through the two-core
makes the image of K the unique component of the quotient. Trivial Fitting
implies trivial solvable radical, so the image is simple and is exactly the
generalized Fitting subgroup. Its centralizer is trivial: a nontrivial
centralizer would either contribute solvable radical or another component.

The faithful outer action then identifies K with H∞ when its outer group
is solvable. If the outer group is a two-group, every Sylow two-subgroup
supplements K. The proof retains the actual two-core quotient map throughout.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.6.27 and the following paragraph, printed pp.934–935. These general
lemmas do not establish the component uniqueness or model hypotheses there.
-/

public section

open Subgroup Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- Trivial Fitting subgroup forces trivial solvable radical in a finite group. -/
theorem radical_bot_of_fitting_bot (hf : fittingSubgroup G = ⊥) :
    solvableRadical G = ⊥ := by
  let R := solvableRadical G
  have hFR : fittingSubgroup R = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ R.subtype_injective).mp
    exact le_bot_iff.mp ((fittingSubgroup_map_subtype_le_of_isSubnormal R
      (inferInstance : R.Normal).isSubnormal).trans hf.le)
  exact (card_le_one_iff_eq_bot R).mp
    ((fitting_eq_bot_iff_card_eq_one_of_solvable R).mp hFR).le

omit [Finite G] in
/-- The unique C-component is normal, since conjugation preserves C-components. -/
theorem IsCComponent.normal_of_unique (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K) : K.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  exact mem_normalizer_iff_map_conj_eq.mpr (hu _ (hK.map_equiv (MulAut.conj g)))

/-- With trivial Fitting subgroup, a unique C-component has trivial centralizer. -/
theorem IsCComponent.centralizer_bot_of_unique_of_fitting_bot (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup G = ⊥) : centralizer (K : Set G) = ⊥ := by
  let _ := hK.normal_of_unique hu
  let C := centralizer (K : Set G)
  by_cases hs : Group.IsSolvable C
  · exact le_bot_iff.mp ((le_solvableRadical C inferInstance hs).trans
      (radical_bot_of_fitting_bot hf).le)
  · obtain ⟨D, hD⟩ := exists_isCComponent_of_not_isSolvable hs
    have hDK := hu _ (hD.map_subtype (inferInstance : C.Normal).isSubnormal)
    have hKC : K ≤ C := hDK ▸ map_subtype_le D
    exact (hK.not_isSolvable (Group.isSolvable_of_comm
      (fun a b : K => Subtype.ext ((hKC a.property) b b.property).symm))).elim

/-- A unique C-component fills the genuine generalized Fitting subgroup when F = 1. -/
theorem IsCComponent.generalizedFitting_eq_of_unique_of_fitting_bot (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup G = ⊥) : generalizedFitting G = K := by
  rw [generalizedFitting, hf, bot_sup_eq,
    ← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot
      (radical_bot_of_fitting_bot hf)]
  apply le_antisymm (sSup_le fun D hD => (hu D hD).le)
  exact le_cComponentLayer hK

/-- Uniqueness of the C-component descends through every solvable normal kernel. -/
theorem IsCComponent.unique_map_quotient (_hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    {D : Subgroup (G ⧸ N)} (hD : D.IsCComponent) :
    D = K.map (QuotientGroup.mk' N) := by
  obtain ⟨E, hE, rfl⟩ := hD.exists_map_quotient_eq N
  rw [hu E hE]

/-- The actual image in the two-core quotient is its generalized Fitting subgroup. -/
theorem IsCComponent.generalizedFitting_twoCore_quotient_eq (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup (G ⧸ pCore 2 G) = ⊥) :
    generalizedFitting (G ⧸ pCore 2 G) = K.map (QuotientGroup.mk' (pCore 2 G)) := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  exact (hK.map_quotient _).generalizedFitting_eq_of_unique_of_fitting_bot
    (fun _ hD => hK.unique_map_quotient hu _ hD) hf

/-- Solvable outer automorphisms identify the original component with H∞. -/
theorem IsCComponent.solvableResidual_eq_of_twoCore_quotient (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup (G ⧸ pCore 2 G) = ⊥)
    [Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K))] :
    solvableResidual G = K := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let _ := hK.perfect
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  have hB : B.IsCComponent := hK.map_quotient _
  have huB : ∀ D : Subgroup (G ⧸ pCore 2 G), D.IsCComponent → D = B := by
    exact fun _ hD => hK.unique_map_quotient hu _ hD
  let _ := hB.normal_of_unique huB
  let _ : Group.IsSolvable (MulAut.Outer B) :=
    MulAut.isSolvable_outer_of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm
  let _ := quotient_isSolvable_of_centralizer_eq_bot B
    (hB.centralizer_bot_of_unique_of_fitting_bot huB hf)
  apply le_antisymm _ (le_solvableResidual_of_isPerfect K)
  apply perfect_le_cComponent_of_map_le hK (pCore 2 G)
  rw [map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)]
  exact solvableResidual_le_of_solvable_quotient B

/-- A two-group outer quotient makes K and a Sylow two-subgroup generate H. -/
theorem IsCComponent.sylow_sup_eq_top_of_outer_twoGroup (hK : K.IsCComponent)
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup (G ⧸ pCore 2 G) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (S : Sylow 2 G) : K ⊔ (S : Subgroup G) = ⊤ := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  have hB : B.IsCComponent := hK.map_quotient _
  have huB : ∀ D : Subgroup (G ⧸ pCore 2 G), D.IsCComponent → D = B := by
    exact fun _ hD => hK.unique_map_quotient hu _ hD
  let _ := hB.normal_of_unique huB
  have hoB : IsPGroup 2 (MulAut.Outer B) :=
    ho.of_equiv (MulAut.outerCongr (cComponentTwoCoreQuotientEquiv hK))
  have hp : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) := hoB.of_injective
    (MulAut.outerAction B) (MulAut.outerAction_injective B
      (hB.centralizer_bot_of_unique_of_fitting_bot huB hf))
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hg : B ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top Sbar]
    exact sup_le_sup (sInf_le ⟨inferInstance, hp⟩) le_rfl
  have hm : (K ⊔ (S : Subgroup G)).map q = ⊤ := by
    rw [map_sup]
    exact hg
  have hc : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have he := congrArg (comap q) hm
  rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at he
  rwa [sup_assoc, sup_eq_left.mpr hc] at he

/-- Vanishing odd prime cores, including three, kills F(H/O₂(H)). -/
theorem fitting_twoCore_quotient_eq_bot
    (hthree : pCore 3 (G ⧸ pCore 2 G) = ⊥)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (G ⧸ pCore 2 G) = ⊥) :
    fittingSubgroup (G ⧸ pCore 2 G) = ⊥ := by
  rw [fitting_eq_sup_pCore]
  apply le_bot_iff.mp
  apply iSup_le
  intro p
  have hp := (Nat.mem_primeFactors.mp p.val.property).1
  by_cases htwo : p.val.val = 2
  · rw [htwo, pCore_quotient_pCore_eq_bot]
  · by_cases hthree' : p.val.val = 3
    · rw [hthree', hthree]
    · rw [hlarge _ hp (by have := hp.two_le; omega)]

end Subgroup

