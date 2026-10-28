module

public import BenderSuzuki.External.Hall.theorem_14_4_2
import Mathlib.Tactic.Group

/-!
# Transferring an index-four normal subgroup

If a subgroup of the center of a Sylow two-subgroup is weakly closed, a normal
index-four subgroup of its normalizer gives a normal index-four subgroup
of the ambient finite group. Hall–Wielandt identifies the maximal two-group
quotients of the normalizer and the group. The normalizer's order-four
quotient factors through this identification, and the resulting surjection
has the required kernel.

Source: Hall, *The Theory of Groups*, Theorem 14.4.2. This is the quotient
consequence used in Suzuki (1965), Section II, Lemmas 3 and 6 at q = 3.
-/

namespace BenderSuzuki.External

/-- An index-four normal subgroup of the normalizer transfers across an
central weakly closed subgroup of a Sylow two-subgroup. -/
public theorem exists_normal_index_four_of_weaklyClosed_central
    {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (Z : Subgroup G)
    (hweak : WeaklyClosedIn (P : Subgroup G) Z)
    (hcentral : ∀ u z : G, u ∈ (P : Subgroup G) → z ∈ Z → Commute u z)
    (L : Subgroup (Subgroup.normalizer (Z : Set G))) [L.Normal]
    (hL : L.index = 4) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := Subgroup.normalizer (Z : Set G)
  let : (hallPResidual 2 G).Normal := hallPResidual_normal 2 G
  let : (hallPResidual 2 H).Normal := hallPResidual_normal 2 H
  have hengel (u z : G) (hu : u ∈ (P : Subgroup G)) (hz : z ∈ Z) :
      engelSymbol 2 u z = 1 := by
    change u⁻¹ * z⁻¹ * u * z = 1
    have hc := hcentral u z hu hz
    calc
      _ = u⁻¹ * (z⁻¹ * u) * z := by group
      _ = u⁻¹ * (u * z⁻¹) * z := by rw [hc.inv_right.symm.eq]
      _ = 1 := by group
  obtain ⟨e⟩ := (hallWielandt_residual_intersection 2 P Z H rfl hweak
    (Or.inl hengel)).2
  have hcard : Nat.card (H ⧸ L) = 4 := hL
  have hp : IsPGroup 2 (H ⧸ L) :=
    IsPGroup.of_card (show Nat.card (H ⧸ L) = 2 ^ 2 from hcard)
  let pi : H →* H ⧸ L := QuotientGroup.mk' L
  have hker : hallPResidual 2 H ≤ pi.ker :=
    hallPResidual_le_ker_of_isPGroup pi hp
  let lifted : (H ⧸ hallPResidual 2 H) →* H ⧸ L :=
    QuotientGroup.lift (hallPResidual 2 H) pi hker
  have hsurj : Function.Surjective lifted :=
    QuotientGroup.lift_surjective_of_surjective _ pi (QuotientGroup.mk'_surjective L) hker
  let f : G →* H ⧸ L :=
    lifted.comp (e.toMonoidHom.comp (QuotientGroup.mk' (hallPResidual 2 G)))
  have hf : Function.Surjective f :=
    hsurj.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨f.ker, inferInstance, ?_⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
  exact hcard

end BenderSuzuki.External
