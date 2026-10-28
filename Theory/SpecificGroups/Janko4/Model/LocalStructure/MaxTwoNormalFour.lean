module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.ActionCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift

/-!
# No normal four-group in the literal J₄ max2 subgroup

Write H for the conjugated max2 subgroup and N for its certified seed normal
closure. The actual action on N/Z(N) is irreducible on binary twelve-space.
Thus O₂(H) acts trivially on this quotient. Extraspecial commutator duality
allows an inner twist of each such element to centralize N; the proved
relative centralizer bound puts the twist in N. Consequently N = O₂(H).

A normal subgroup W of order four lies in N. Its image in N/Z(N) is invariant
under the actual conjugation action of H. Irreducibility and the order 4096
of that quotient force the image to be trivial, putting W in the center of
order two, a contradiction. The established conjugation equivalence
`sourceSubgroupEquivLocal` transports this to the original ATLAS max2 words.
The elementary-abelian formulation is exactly the normal-four premise used
in the J₄ case of the sporadic inspection; the proof gives the stronger
exclusion without the elementary-abelian assumption.

Source: Aschbacher–Smith, combined manuscript, 15.3.43, printed p.1140;
GLS3, Table 5.3i and note 1, printed p.270, recorded in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The literal ATLAS word and coordinate
provenance remains in the imported `Conjugacy` and `Realization.ActionCore`
families. No ambient J₄ order, simplicity, automorphism rigidity or maximal
subgroup coverage is used.
-/

public section

open Subgroup
namespace Janko4.LocalStructure
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreComparison.CoordinateGenerators

private theorem normalClosure_eq_local_twoCore :
    localNormalClosure = pCore 2 localSubgroup := by
  have hN : localNormalClosure ≤ pCore 2 localSubgroup :=
    le_sSup ⟨localNormalClosure_normal, localNormalClosure_isPGroup⟩
  apply le_antisymm hN
  intro g hg
  let : IsExtraspecial 2 localNormalClosure := Realization.normalClosure_extraspecial
  have hk := Realization.localTwoCore_le_quotientAction_ker hg
  have hfix (z : localNormalClosure) (hz : z ∈ center localNormalClosure) :
      localNormalClosureAction g z = z := by
    rw [Realization.normalClosure_center] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    rw [map_zpow, OuterImageComparison.action_centralWord]
  have hmod (n : localNormalClosure) (_hn : n ∈ (⊤ : Subgroup localNormalClosure)) :
      localNormalClosureAction g n * n⁻¹ ∈ center localNormalClosure := by
    rw [Realization.normalClosure_center]
    apply (QuotientGroup.eq_one_iff _).mp
    change OuterImageComparison.projection (localNormalClosureAction g n * n⁻¹) = 1
    rw [map_mul, map_inv, ← OuterImageComparison.quotientAction_projection]
    rw [show OuterImageComparison.quotientAction g = 1 from hk]
    exact mul_inv_cancel _
  obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
    (⊤ : Subgroup localNormalClosure) le_top (localNormalClosureAction g) hfix hmod
  have hc : g * (r : localSubgroup) ∈ localNormalClosureAction.ker := by
    apply MulEquiv.ext
    intro n
    have h := congrArg (fun v : localNormalClosure => (v : localSubgroup))
      (hr n (mem_top n))
    apply Subtype.ext
    change (g * (r : localSubgroup)) * (n : localSubgroup) *
        (g * (r : localSubgroup))⁻¹ = n
    change g * ((r : localSubgroup) * (n : localSubgroup) * (r : localSubgroup)⁻¹) * g⁻¹ = n at h
    simpa only [mul_inv_rev, mul_assoc] using h
  have hm := localNormalClosure.mul_mem (localNormalClosureAction_ker_le hc)
    (localNormalClosure.inv_mem r.property)
  simpa only [mul_inv_cancel_right] using hm

/-- No normal subgroup of order four exists in the conjugated max2 carrier. -/
theorem max2_local_normal_card_ne_four (W : Subgroup localSubgroup) [W.Normal] :
    Nat.card W ≠ 4 := by
  intro hW
  have hWN : W ≤ localNormalClosure := by
    rw [normalClosure_eq_local_twoCore]
    exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 2) hW⟩
  let V := W.subgroupOf localNormalClosure
  have hV : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv).trans hW
  let D := V.map OuterImageComparison.projection
  have hD : D = ⊥ ∨ D = ⊤ := Realization.quotientAction_irreducible D (by
    rintro ⟨_, g, rfl⟩ _ ⟨v, hv, rfl⟩
    change OuterImageComparison.quotientAction g (OuterImageComparison.projection v) ∈ D
    rw [OuterImageComparison.quotientAction_projection]
    apply mem_map_of_mem
    exact Subgroup.Normal.conj_mem inferInstance (v : localSubgroup) hv g)
  rcases hD with hb | ht
  · have hVc : V ≤ center localNormalClosure := by
      rw [Realization.normalClosure_center]
      have hker : V ≤ OuterImageComparison.projection.ker :=
        (Subgroup.map_eq_bot_iff V).mp hb
      simpa only [OuterImageComparison.projection, QuotientGroup.ker_mk'] using hker
    have hc := Subgroup.card_le_of_le hVc
    rw [hV, Realization.normalClosure_center_card] at hc
    omega
  · have hc : Nat.card D ≤ Nat.card V := Nat.le_of_dvd (Nat.card_pos)
      (V.card_map_dvd OuterImageComparison.projection)
    rw [ht, Subgroup.card_top,
      Nat.card_congr OuterImageComparison.coordinates.toEquiv, hV] at hc
    norm_num [Nat.card_eq_fintype_card] at hc

/-- No normal subgroup of order four exists in the original ATLAS max2 carrier. -/
theorem max2_normal_card_ne_four (W : Subgroup sourceSubgroup) [W.Normal] :
    Nat.card W ≠ 4 := by
  let V := W.map sourceSubgroupEquivLocal.toMonoidHom
  let : V.Normal := (inferInstance : W.Normal).map
    sourceSubgroupEquivLocal.toMonoidHom sourceSubgroupEquivLocal.surjective
  have hn := max2_local_normal_card_ne_four V
  rwa [Subgroup.card_map_of_injective sourceSubgroupEquivLocal.injective] at hn

/-- The normal elementary four obstruction in the exact consumer convention. -/
theorem max2_no_normal_elementary_four (W : Subgroup sourceSubgroup)
    (hn : W.Normal) (_he : IsElementaryAbelian 2 W) : Nat.card W ≠ 4 := by
  let : W.Normal := hn
  exact max2_normal_card_ne_four W

end Janko4.LocalStructure
