module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction.Image

/-!
# The cyclic core in the terminal A₆ shadow

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.569–570, immediately after Lemma 2.5.27.

The normal cyclic four-group is inverted via its faithful conjugate image.
The transposition-centralizer geometry embeds the core in `C₂ × D₈`, excluding
`C₈` and `Q₈`. Equality of orders identifies the core with the normal four-group;
the action kernel and its Sylow image then give `|S| = 128`.

This is the conditional quotient-geometry reduction. Its additional hypotheses
are exactly `CoreReduction.ModelGeometry` for the actual image Sylow subgroup.
The finite A₆ model owner and the shadow assembly must discharge those identities.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The core is cyclic four once the concrete A₆ model identities are supplied. -/
public theorem Setup.core_cyclicFour_of_model (d : Setup G)
    (m : CoreReduction.ModelGeometry (CoreReduction.imageSylow d)) :
    Nonempty (d.core ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨j, hj⟩ := CoreReduction.exists_core_embedding d m
  exact cyclicFour_of_shadow_alternatives_of_embedding d.alternatives j hj

/-- Every normal cyclic four-group extracted from the core is the entire core. -/
public theorem Setup.core_eq_cyclicFour_of_model (d : Setup G)
    (m : CoreReduction.ModelGeometry (CoreReduction.imageSylow d))
    (V : Subgroup G) (hV : V ≤ d.core)
    (hfour : Nonempty (V ≃* Multiplicative (ZMod 4))) : d.core = V := by
  obtain ⟨f⟩ := d.core_cyclicFour_of_model m
  obtain ⟨g⟩ := hfour
  apply (eq_of_le_of_card_ge hV ?_).symm
  rw [Nat.card_congr f.toEquiv, Nat.card_congr g.toEquiv]

/-- Construct the intermediate reduction from the compatible action and the
explicit finite-model identities. No embedding, ambient inversion, core
isomorphism, or ambient order is assumed. -/
public theorem Setup.coreReduction_of_model (d : Setup G)
    (m : CoreReduction.ModelGeometry (CoreReduction.imageSylow d)) : CoreReduction d := by
  obtain ⟨V, hVC, hn, hfour⟩ := d.exists_normal_cyclicFour
  have hCV : d.core = V := d.core_eq_cyclicFour_of_model m V hVC hfour
  have hcyclic := d.core_cyclicFour_of_model m
  refine ⟨hcyclic, ?_, ?_⟩
  · obtain ⟨f⟩ := hcyclic
    have hker : Nat.card (CoreReduction.action d).ker = 4 := by
      rw [CoreReduction.action_kernel,
        Nat.card_congr (subgroupOfEquivOfLe (show d.core ≤ d.S from inf_le_left)).toEquiv,
        Nat.card_congr f.toEquiv]
      norm_num
    have hrange : Nat.card (CoreReduction.action d).range = 32 := by
      rw [← CoreReduction.imageSylow_eq_range]
      exact m.card
    have hcard := (CoreReduction.action d).ker.card_mul_index
    rw [index_ker, hker, hrange] at hcard
    exact hcard.symm
  · intro E hE hEfour e he hne v hv
    let : IsKleinFour E := hEfour
    have he2 : e ^ 2 = 1 := by
      simpa only [pow_two, coe_mul, coe_one] using congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
    exact CoreReduction.inverts_normal_cyclicFour d m V hVC hn hfour
      (hE he) he2 hne v (hCV ▸ hv)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
