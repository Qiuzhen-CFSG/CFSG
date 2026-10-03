module
public import Stellmacher.SectionOne.OneSevenFactorDefs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic

/-!
# Conjugation of the global factors in (1.7)

The refined Ω-star family is invariant under conjugation. Conjugating the
SL2 group transports its derived subgroup and its two action commutators.
The odd core is normal, so the condition of being normalized by the odd
core is preserved as well. This allows the join of all such factors to be
used as a normal subgroup in the global product argument of Stellmacher
(1.7), journal p.19; source: refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionOne
universe u

/-- The factor family used in (1.7) is invariant under ambient conjugation. -/
public theorem IsOneSevenFactor.conjBy
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (g : G) :
    IsOneSevenFactor (V := V) (D.conjBy g) := by
  let Dg : Subgroup G := D.conjBy g
  let W : Subgroup G := oddCore G
  let _ : W.Normal := pPrimeCore_normal
  have heq : (commutator Dg).map Dg.subtype =
      ((commutator D).map D.subtype).conjBy g := by
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subtype_commutator]
    exact (Subgroup.map_commutator D D (MulAut.conj g).toMonoidHom).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨e⟩ := hD.1
    exact ⟨((MulAut.conj g).subgroupMap D).symm.trans e⟩
  · rw [heq]
    exact RankOneThreeGroupAssembly.oneOmega_conjBy _ hD.2.1 g
  · rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D g,
      Subgroup.card_map_of_injective
        (f := (MulDistribMulAction.toMulAut G V g).toMonoidHom)
        (MulDistribMulAction.toMulAut G V g).injective]
    exact hD.2.2.1
  · have hWD : W ≤ Subgroup.normalizer (D : Set G) :=
      (show W ≤ W ⊔ D from le_sup_left).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hD.2.2.2)
    have hWDg : W ≤ Subgroup.normalizer (Dg : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro w hw d hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      have hc : g⁻¹ * w * g ∈ W := by
        simpa using (inferInstance : W.Normal).conj_mem w hw g⁻¹
      have hmem : (g⁻¹ * w * g) * d0 * (g⁻¹ * w * g)⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hWD hc) d0).mp hd0
      refine ⟨_, hmem, ?_⟩
      change g * ((g⁻¹ * w * g) * d0 * (g⁻¹ * w * g)⁻¹) * g⁻¹ =
        w * (g * d0 * g⁻¹) * w⁻¹
      group
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hWDg Dg.le_normalizer)

end Stellmacher.SectionOne
