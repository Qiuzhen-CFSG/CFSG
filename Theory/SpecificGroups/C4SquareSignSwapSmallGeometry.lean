module

public import Theory.SpecificGroups.C4SquareSignSwapCentricData
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Small centric normalizers and their central quotient actions

For candidate 28, the involutions in the transfer subgroup are exactly the
central involutions. Hence every automorphism of this candidate preserves
transfer membership on involutions. This argument applies to this marked
intersection, without claiming that the transfer intersection is characteristic
in every subgroup isomorphic to C₄ * Q₈.

For candidates 17 and 26, the extraspecial core normalizes the candidate
and acts trivially on its quotient by its center. The normalizer statement
uses the marked subgroup geometry, and the central displacement identities
are finite calculations checked by the kernel.

Source: the explicit sign-and-swap model for Stellmacher (8.6)(a).
-/

namespace C4SquareSignSwap

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Four small candidates have precisely the second vertex core as
normalizer in the Sylow model. -/
public theorem smallCandidate_normalizer_extraspecial (i : Fin 32)
    (hi : i = 26 ∨ i = 28 ∨ i = 29 ∨ i = 30) :
    Subgroup.normalizer (centricCandidate i : Set Model) = extraspecialCore := by
  have h : ∀ i : Fin 32, (i = 26 ∨ i = 28 ∨ i = 29 ∨ i = 30) →
      ∀ g : Model,
        (∀ x : Model, x ∈ centricCandidate i ↔ g * x * g⁻¹ ∈ centricCandidate i) ↔
          g ∈ extraspecialCore := by decide +kernel
  ext g
  rw [Subgroup.mem_normalizer_iff]
  exact h i hi g

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Candidate 19 has precisely the first vertex core as normalizer. -/
public theorem candidate19_normalizer :
    Subgroup.normalizer (centricCandidate 19 : Set Model) = inverterCore := by
  have h : ∀ g : Model,
      (∀ x : Model, x ∈ centricCandidate 19 ↔ g * x * g⁻¹ ∈ centricCandidate 19) ↔
        g ∈ inverterCore := by decide +kernel
  ext g
  rw [Subgroup.mem_normalizer_iff]
  exact h g

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The other three small candidates are normal in the whole Sylow model. -/
public theorem smallCandidate_normalizer_top (i : Fin 32)
    (hi : i = 17 ∨ i = 18 ∨ i = 20) :
    Subgroup.normalizer (centricCandidate i : Set Model) = ⊤ := by
  have h : ∀ i : Fin 32, (i = 17 ∨ i = 18 ∨ i = 20) →
      ∀ g x : Model,
        x ∈ centricCandidate i ↔ g * x * g⁻¹ ∈ centricCandidate i := by decide +kernel
  apply top_unique
  intro g _
  exact Subgroup.mem_normalizer_iff.mpr (h i hi g)

/-- The eight small exceptions have Sylow normalizers of order at least 32. -/
public theorem smallCandidate_normalizer_card (i : Fin 32)
    (hi : i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 26 ∨ i = 28 ∨
      i = 29 ∨ i = 30) :
    32 ≤ Nat.card (Subgroup.normalizer (centricCandidate i : Set Model)) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [smallCandidate_normalizer_top 17 (by simp), Nat.card_congr Subgroup.topEquiv.toEquiv,
      card_model]
    decide
  · rw [smallCandidate_normalizer_top 18 (by simp), Nat.card_congr Subgroup.topEquiv.toEquiv,
      card_model]
    decide
  · rw [candidate19_normalizer, card_inverterCore]
  · rw [smallCandidate_normalizer_top 20 (by simp), Nat.card_congr Subgroup.topEquiv.toEquiv,
      card_model]
    decide
  all_goals rw [smallCandidate_normalizer_extraspecial _ (by simp), card_extraspecialCore]

private theorem candidate28_involution_central :
    ∀ x : Model, x ∈ centricCandidate 28 → x ^ 2 = 1 →
      (x ∈ transfer ↔ ∀ y : Model, y ∈ centricCandidate 28 → y * x = x * y) := by
  decide +kernel

/-- On candidate 28, transfer membership of an involution is intrinsic. -/
public theorem candidate28_involution_mem_transfer_iff_center
    (x : centricCandidate 28) (hx : x ^ 2 = 1) :
    (x : Model) ∈ transfer ↔ x ∈ Subgroup.center (centricCandidate 28) := by
  rw [Subgroup.mem_center_iff]
  have hx' : (x : Model) ^ 2 = 1 := congrArg Subtype.val hx
  constructor
  · intro h y
    exact Subtype.ext ((candidate28_involution_central x x.property hx').mp h y y.property)
  · intro h
    apply (candidate28_involution_central x x.property hx').mpr
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)

/-- Every abstract automorphism preserves this candidate's marked
involution partition. -/
public theorem candidate28_automorphism_preserves_transfer
    (e : MulAut (centricCandidate 28)) (x : centricCandidate 28)
    (hx : x ^ 2 = 1) :
    (e x : Model) ∈ transfer ↔ (x : Model) ∈ transfer := by
  have hex : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  rw [candidate28_involution_mem_transfer_iff_center _ hex,
    candidate28_involution_mem_transfer_iff_center _ hx]
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply e.injective
    simpa only [map_mul] using h (e y)
  · intro h y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (h z)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The order-32 extraspecial core acts trivially on the central quotients
of the other two central-product candidates. -/
public theorem smallCentralProduct_extraspecialCore_action (i : Fin 32)
    (hi : i = 17 ∨ i = 26) :
    extraspecialCore ≤ Subgroup.normalizer (centricCandidate i : Set Model) ∧
      ∀ g : Model, g ∈ extraspecialCore →
        ∀ x : Model, x ∈ centricCandidate i →
          ∀ y : Model, y ∈ centricCandidate i →
            y * (x⁻¹ * (g * x * g⁻¹)) = (x⁻¹ * (g * x * g⁻¹)) * y := by
  constructor
  · rcases hi with rfl | rfl
    · rw [smallCandidate_normalizer_top 17 (by simp)]
      exact le_top
    · rw [smallCandidate_normalizer_extraspecial 26 (by simp)]
  · have h : ∀ i : Fin 32, (i = 17 ∨ i = 26) →
        ∀ g : Model, g ∈ extraspecialCore →
          ∀ x : Model, x ∈ centricCandidate i →
            ∀ y : Model, y ∈ centricCandidate i →
              y * (x⁻¹ * (g * x * g⁻¹)) = (x⁻¹ * (g * x * g⁻¹)) * y := by
      decide +kernel
    exact h i hi

end C4SquareSignSwap
