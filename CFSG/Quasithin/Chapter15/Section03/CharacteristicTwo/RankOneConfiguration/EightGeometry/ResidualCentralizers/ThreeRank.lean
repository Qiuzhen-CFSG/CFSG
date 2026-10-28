module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import Theory.Quasithin.Rank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# The strict odd-prime rank hypothesis for A.3.18

The star kernel is a two-group by the given module-centralizer equality.
Restriction to L therefore gives a surjection with coprime kernel onto its
marked A₈ image. Two disjoint three-cycles in that image lift the lower
bound on three-rank through the coprime quotient.

This proves m₃(L) > 1 from the actual marking; the weaker positive-rank
field in `ComponentWitness` is not enough for the source application.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(3), printed p.1133, and A.3.18, p.51.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The marked A₈ image and the two-group action kernel give the strict
three-rank hypothesis needed in A.3.18. -/
theorem component_threeRank_gt_one_of_star_marking (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8)) :
    1 < primeRank 3 c.L := by
  have hk : IsPGroup 2 (d.starMap I).ker := by
    have hm : IsPGroup 2 ((d.starMap I).ker.map I.subtype) := by
      rw [star_kernel_eq_core_of_centralizer d c P hP hcentralizer]
      exact isPGroup_pCoreIn 2 I
    exact hm.of_equiv ((d.starMap I).ker.equivMapOfInjective
      I.subtype I.subtype_injective).symm
  let f := (e.toMonoidHom.comp (d.starMap I)).comp (inclusion (component_le c))
  have hker : f.ker = (d.starMap I).ker.comap (inclusion (component_le c)) := by
    change ((e.toMonoidHom.comp (d.starMap I)).ker).comap _ = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
  have hkp : IsPGroup 2 f.ker := by
    rw [hker]
    exact hk.comap_of_injective _ (inclusion_injective (component_le c))
  have hf : f.range = alternatingGroup (Fin 8) := by
    change ((c.L.subgroupOf I).map (d.starMap I)).map e.toMonoidHom = _ at hmark
    simpa only [f, MonoidHom.range_comp, inclusion_range, Subgroup.map_map] using hmark
  have hr : primeRank 3 f.range ≤ primeRank 3 c.L := by
    apply primeRank_le_of_surjective_of_coprime 3 f.rangeRestrict f.rangeRestrict_surjective
    rw [MonoidHom.ker_rangeRestrict]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkp
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [hf] at hr
  exact (show 1 < 2 from by decide).trans_le
    ((alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 8)).trans hr)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
