module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# The whole center of the checked Hall–Janko Sylow subgroup

The existing 128-element enumeration supplies all elements of the fixed Sylow
subgroup. Commutation with its seven generators, tested at two permutation
points, leaves only indices zero and six. The latter is the already checked
central involution. This proves the entire embedded center, not merely a
central subgroup or an abstract center isomorphism.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195;
the unchanged ATLAS J2G1-p100B0 carrier and Seed words.
-/

public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Subgroup Theory.GroupTheory GeneratorPair Seed PairNormalizer PairNormalizer.SylowData
open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
private theorem center_table_check : ∀ i : Fin 128,
    (∀ j : Fin 7,
      (sGenTable j * sTable i) 0 = (sTable i * sGenTable j) 0 ∧
      (sGenTable j * sTable i) 1 = (sTable i * sGenTable j) 1) →
    i = 0 ∨ i = 6 := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem involution_table_check : sTable 6 = FirstFusion.tPerm := by
  decide +kernel

private theorem sElement_six : sElement 6 = FirstFusion.t := by
  apply inclusion_injective
  rw [sElement_inclusion, FirstFusion.inclusion_t]
  exact involution_table_check

/-- The whole embedded center of the chosen Sylow subgroup is the central involution line. -/
theorem center_s : (center s).map s.subtype = zpowers FirstFusion.t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := exists_sElement x.property
    have hc : ∀ j : Fin 7,
        (sGenTable j * sTable i) 0 = (sTable i * sGenTable j) 0 ∧
        (sGenTable j * sTable i) 1 = (sTable i * sGenTable j) 1 := by
      intro j
      have h := congrArg (fun y : s => inclusion (y : Carrier))
        (mem_center_iff.mp hx ⟨sGenerator j, Subgroup.subset_closure ⟨j, rfl⟩⟩)
      change inclusion (sGenerator j * (x : Carrier)) = inclusion ((x : Carrier) * sGenerator j) at h
      rw [← hi, map_mul, map_mul, sGenerator_inclusion, sElement_inclusion] at h
      exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h,
        congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h⟩
    change (x : Carrier) ∈ zpowers FirstFusion.t
    rcases center_table_check i hc with rfl | rfl
    · have hx1 : (x : Carrier) = 1 := hi.symm
      rw [hx1]
      exact one_mem _
    · rw [← hi, sElement_six]
      exact mem_zpowers _
  · apply zpowers_le.mpr
    have ht : FirstFusion.t ∈ s := sElement_six ▸ sElement_mem 6
    refine ⟨⟨FirstFusion.t, ht⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (s_le_l₁ y.property)

/-- The central involution has order two in the unchanged carrier. -/
theorem central_involution_order : orderOf FirstFusion.t = 2 :=
  orderOf_eq_prime FirstFusion.t_pow_two FirstFusion.t_ne_one

/-- The chosen actual Sylow subgroup has center of order two. -/
theorem card_center_s : Nat.card (center s) = 2 := by
  rw [← card_map_of_injective s.subtype_injective, center_s, Nat.card_zpowers,
    central_involution_order]

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
