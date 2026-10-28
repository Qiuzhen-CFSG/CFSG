module

public import Theory.GroupAction.CentralElementaryQuotientOrbit

/-!
# Fusion inside a four-group with symmetric-four normalizer

If the normalizer of a Klein four subgroup is isomorphic to S₄, it
conjugates any nonidentity element of the four-group to any other.
The four-group is normal in its normalizer and is a two-group, so it lies
in the normalizer's two-core. The existing symmetric-four core action
supplies transitivity, retaining the original elements and conjugation.

The relative form works with the actual subgroup `E.subgroupOf K` and
returns a conjugating element of `K ∩ N_G(E)`.

Source: Aschbacher–Smith, quasithin classification, Lemma 2.5.21, the
prime-linear component branch and its symmetric-four normalizer action.
-/

open Subgroup

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- An S₄ normalizer fuses the three nonidentity elements of a four-group. -/
public theorem four_normalizer_fusion (E : Subgroup G) [IsKleinFour E]
    (eN : normalizer (E : Set G) ≃* Equiv.Perm (Fin 4))
    (a b : G) (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n : normalizer (E : Set G), (n : G) * a * (n : G)⁻¹ = b := by
  let N := normalizer (E : Set G)
  let U := E.subgroupOf N
  have hU : U.Normal :=
    (normal_subgroupOf_iff_le_normalizer E.le_normalizer).mpr le_rfl
  have hUtwo : IsPGroup 2 U := by
    apply IsPGroup.iff_card.mpr
    refine ⟨2, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe E.le_normalizer).toEquiv,
      IsKleinFour.card_four]
    decide
  have hUcore : U ≤ pCore 2 N := le_sSup ⟨hU, hUtwo⟩
  let aN : N := ⟨a, E.le_normalizer ha⟩
  let bN : N := ⟨b, E.le_normalizer hb⟩
  obtain ⟨n, hn⟩ := Matrix.PSL3Two.ParabolicCoreModel.core_transitive eN aN bN
    (hUcore ha) (hUcore hb)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
  exact ⟨n, congrArg Subtype.val hn⟩

/-- Fusion on the literal four-group inside an overgroup, with its ambient conjugator. -/
public theorem four_normalizer_fusion_in (K E : Subgroup G) (hEK : E ≤ K)
    [IsKleinFour E]
    (eN : normalizer (E.subgroupOf K : Set K) ≃* Equiv.Perm (Fin 4))
    (a b : G) (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ K ⊓ normalizer (E : Set G), n * a * n⁻¹ = b := by
  let eE := subgroupOfEquivOfLe hEK
  let : IsKleinFour (E.subgroupOf K) := {
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  obtain ⟨n, hn⟩ := four_normalizer_fusion (E.subgroupOf K) eN
    (⟨a, hEK ha⟩ : K) (⟨b, hEK hb⟩ : K) ha hb
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
  refine ⟨((n : K) : G), ⟨(n : K).property, ?_⟩, congrArg Subtype.val hn⟩
  exact (subgroupOf_normalizer_eq hEK).ge n.property

end Theory.GroupTheory
