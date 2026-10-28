module

public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic

/-!
# The local cubic extension of E₄ × Sz(8)

This input records actual commuting normal subgroups, their matrix-model
isomorphism, and a cubic supplement acting without nonidentity fixed points
on the four-group and by outer automorphisms on the Suzuki factor. It does
not assume torus centralizers or automizers.

Disjoint subgroup products give order 349440. Decomposing an element into
base and cubic factors computes each nonidentity four-group centralizer.
The parent module constructs this input on the literal N_G(S₀).

Source: Aschbacher–Smith, J.2.9–10, printed p.438 (PDF p.449),
refs/quasithin.pdf. The full-automorphism torus calculations are separate.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition

/-- Actual subgroup and action data for the local cubic extension. -/
structure CubicProduct (K : Type*) [Group K] where
  E : Subgroup K
  L : Subgroup K
  B : Subgroup K
  normal_E : E.Normal
  normal_L : L.Normal
  elementary_E : IsElementaryAbelian 2 E
  card_E : Nat.card E = 4
  model : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1
  central : E ≤ centralizer (L : Set K)
  disjoint : Disjoint E L
  card_B : Nat.card B = 3
  generate : (E ⊔ L) ⊔ B = ⊤
  fixedPointFree : ∀ b ∈ B, b ≠ 1 → ∀ s ∈ E, s ≠ 1 → b * s * b⁻¹ ≠ s
  outer : ∀ b ∈ B, b ≠ 1 →
    ¬ ∃ l ∈ L, ∀ x ∈ L, b * x * b⁻¹ = l * x * l⁻¹

namespace CubicProduct
variable {K : Type*} [Group K] (c : CubicProduct K)

/-- The commuting base has order four times the order of Sz(8). -/
theorem card_base : Nat.card (c.E ⊔ c.L : Subgroup K) = 116480 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint c.E c.L
    ((le_centralizer_iff.mp c.central).trans (Subgroup.centralizer_le_normalizer _)) c.disjoint,
    c.card_E, Nat.card_congr c.model.toEquiv,
    BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
  norm_num

include c in
/-- The cubic extension has the exact order required by J.2.10. -/
theorem card : Nat.card K = 349440 := by
  let := c.normal_E
  let := c.normal_L
  have hd : Disjoint (c.E ⊔ c.L) c.B := disjoint_of_coprime_natCard (by
    rw [c.card_base, c.card_B]
    decide)
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint (c.E ⊔ c.L) c.B
    (by rw [normalizer_eq_top]; exact le_top) hd
  rw [c.generate, Nat.card_congr (topEquiv : (⊤ : Subgroup K) ≃* K).toEquiv,
    c.card_base, c.card_B] at hc
  exact hc

/-- A nonidentity member of the four-group has precisely the base as centralizer. -/
theorem centralizer_nonidentity (s : K) (hs : s ∈ c.E) (hne : s ≠ 1) :
    centralizer ({s} : Set K) = c.E ⊔ c.L := by
  let := c.normal_E
  let := c.normal_L
  let := c.elementary_E
  have hbase : c.E ⊔ c.L ≤ centralizer ({s} : Set K) := by
    apply sup_le
    · exact (le_centralizer c.E).trans
        (centralizer_le (Set.singleton_subset_iff.mpr hs))
    · exact (le_centralizer_iff.mp c.central).trans
        (centralizer_le (Set.singleton_subset_iff.mpr hs))
  apply le_antisymm ?_ hbase
  intro x hx
  have hxgen : x ∈ (c.E ⊔ c.L) ⊔ c.B := by rw [c.generate]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hxgen
  have hbC : b ∈ centralizer ({s} : Set K) :=
    (mul_mem_cancel_left (hbase ha)).mp hx
  have hb1 : b = 1 := by
    by_contra hb1
    apply c.fixedPointFree b hb hb1 s hs hne
    rw [mem_centralizer_singleton_iff.mp hbC, mul_inv_cancel_right]
  simpa only [hb1, mul_one] using ha

end CubicProduct
end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition
