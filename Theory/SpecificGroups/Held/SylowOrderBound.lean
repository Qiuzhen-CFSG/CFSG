module
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations

/-!
# The Held Sylow two-part from its actual colored graph

The original four-word representative embeds in the group preserving its
colored orbit graph, whose certified order is at most 1024. Its already
proved self-normalization makes it Sylow. Conjugacy bounds every actual
Held Sylow by 1024, hence 2¹² cannot divide the carrier order.

No full Held order formula is required. This supplies the two-part
obstruction for the non-A₅ point-component comparison in Aschbacher–Smith
10.2.9, pp.750–751, using the ATLAS HeG1-p2058B0 words and GLS3 Table 5.3p.
-/

public section
open Subgroup
namespace Held
open LocalPairs.SylowGeometry.Calculations

/-- The actual Held Sylows inherit the certified graph bound. -/
theorem sylow_card_le_1024 (S : Sylow 2 He) : Nat.card S ≤ 1024 := by
  have hrep : Nat.card representative ≤ 1024 := by
    apply le_trans (Nat.card_le_card_of_injective
      (fun g : representative =>
        (⟨representation g.val,
          InnerNormalizer.normalizer_mem_evenColoredGraphGroup
            InnerNormalizer.orbitSizeLabel_eq_card_orbit g.val
            (representative.le_normalizer g.property)⟩ : InnerNormalizer.evenColoredGraphGroup))
      (fun g h he => Subtype.ext
        (representation_injective (congrArg (fun z : InnerNormalizer.evenColoredGraphGroup => z.val) he))))
    exact InnerNormalizer.evenColoredGraphGroup_card_le
  obtain ⟨R,hR⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  rw [Nat.card_congr (S.equiv R).toEquiv]
  exact (Nat.card_congr (MulEquiv.subgroupCongr hR).toEquiv).le.trans hrep

/-- The two-part obstruction needed by the even-degree local comparison. -/
theorem not_two_pow_twelve_dvd_card : ¬ 2 ^ 12 ∣ Nat.card He := by
  intro hd
  let S : Sylow 2 He := Classical.choice inferInstance
  have hS := S.pow_dvd_card_of_pow_dvd_card (n := 12) hd
  have hl := Nat.le_of_dvd Nat.card_pos hS
  have hu := sylow_card_le_1024 S
  norm_num at hl
  omega
end Held
