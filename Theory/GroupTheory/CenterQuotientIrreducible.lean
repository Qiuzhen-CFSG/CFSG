module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Centers of central quotients under an irreducible local action

Write `Z = Z(G)` and `Q/Z = Z(G/Z)`. If automorphisms are transitive on
`Z - {1}`, then a nontrivial characteristic subgroup of `Z` is all of `Z`.
In particular, `Q > Z` implies `[Q,G] = Z`.

For a proper subgroup `A < Z`, the preimage of `Z(G/A)` lies between `Z`
and `Q`. It is invariant under every automorphism fixing `Z` pointwise.
An irreducible action on `Q/Z` therefore makes that preimage `Z` or `Q`;
the latter contradicts `[Q,G] = Z`, since its commutators would lie in `A`.

This is the quotient argument in GLS, Volume 4, Chapter 4, Lemma 2.8(c).
For its double Suzuki application, `G` is a Sylow subgroup of the universal
fourfold cover. The application must prove both action hypotheses from that
actual cover; no model calculation is asserted here.
-/

open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A nontrivial characteristic subgroup of a center with a single nonidentity
orbit is the whole center. -/
public theorem characteristic_eq_center_of_transitive
    (C : Subgroup G) [C.Characteristic] (hC : C ≤ center G) (hne : C ≠ ⊥)
    (htrans : ∀ x ∈ center G, x ≠ 1 → ∀ y ∈ center G, y ≠ 1 →
      ∃ α : MulAut G, α x = y) : C = center G := by
  apply le_antisymm hC
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hx' : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  intro y hy
  by_cases hy' : y = 1
  · simp [hy']
  obtain ⟨α, hα⟩ := htrans x (hC x.property) hx' y hy hy'
  have hm := characteristic_iff_map_eq.mp (inferInstance : C.Characteristic) α
  rw [← hm]
  exact ⟨x, x.property, hα⟩

/-- Transitivity on the nonidentity central elements forces the second-center
commutators to fill the center. -/
public theorem commutator_second_center_eq_of_transitive
    (hne : ¬ upperCentralSeriesStep (center G) ≤ center G)
    (htrans : ∀ x ∈ center G, x ≠ 1 → ∀ y ∈ center G, y ≠ 1 →
      ∃ α : MulAut G, α x = y) :
    ⁅upperCentralSeriesStep (center G), (⊤ : Subgroup G)⁆ = center G := by
  apply characteristic_eq_center_of_transitive _ _ _ htrans
  · apply commutator_le.mpr
    intro x hx y _
    exact (mem_upperCentralSeriesStep _ _).mp hx y
  · intro he
    exact hne (commutator_top_right_eq_bot_iff_le_center.mp he)

/-- The center of a proper central quotient acquires no additional elements
when the second-center factor has an irreducible center-fixing action and its
commutators fill the center. -/
public theorem center_quotient_eq_image_of_irreducible
    (A : Subgroup G) [A.Normal] (hA : A < center G)
    (hcomm : ⁅upperCentralSeriesStep (center G), (⊤ : Subgroup G)⁆ = center G)
    (hirred : ∀ H : Subgroup G, center G ≤ H → H ≤ upperCentralSeriesStep (center G) →
      (∀ α : MulAut G, (∀ z ∈ center G, α z = z) → H.map α.toMonoidHom = H) →
      H = center G ∨ H = upperCentralSeriesStep (center G)) :
    center (G ⧸ A) = (center G).map (QuotientGroup.mk' A) := by
  have hC : center G ≤ upperCentralSeriesStep A := by
    intro z hz
    rw [mem_upperCentralSeriesStep]
    intro g
    have hc : Commute z g := (Subgroup.mem_center_iff.mp hz g).symm
    rw [hc.commutator_eq]
    exact A.one_mem
  have hCQ : upperCentralSeriesStep A ≤ upperCentralSeriesStep (center G) := by
    intro x hx
    exact fun g => hA.le (hx g)
  have hstable : ∀ α : MulAut G, (∀ z ∈ center G, α z = z) →
      (upperCentralSeriesStep A).map α.toMonoidHom = upperCentralSeriesStep A := by
    intro α hα
    have hmap (β : MulAut G) (hβ : ∀ z ∈ center G, β z = z) :
        (upperCentralSeriesStep A).map β.toMonoidHom ≤ upperCentralSeriesStep A := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_upperCentralSeriesStep]
      intro y
      change ⁅β x, y⁆ ∈ A
      have hm : ⁅x, β.symm y⁆ ∈ A := hx (β.symm y)
      have he : β ⁅x, β.symm y⁆ = ⁅x, β.symm y⁆ := hβ _ (hA.le hm)
      have hm' : β ⁅x, β.symm y⁆ ∈ A := by rwa [he]
      simpa only [map_commutatorElement, MulEquiv.apply_symm_apply] using hm'
    apply le_antisymm (hmap α hα)
    intro x hx
    have hs : ∀ z ∈ center G, α.symm z = z := by
      intro z hz
      apply α.injective
      simp only [MulEquiv.apply_symm_apply, hα z hz]
    have hm := hmap α.symm hs (mem_map_of_mem α.symm.toMonoidHom hx)
    exact ⟨α.symm x, hm, α.apply_symm_apply x⟩
  have he : upperCentralSeriesStep A = center G := by
    rcases hirred _ hC hCQ hstable with he | he
    · exact he
    · exfalso
      apply hA.not_ge
      rw [← hcomm, ← he]
      exact commutator_le.mpr (fun x hx y _ => hx y)
  apply comap_injective (QuotientGroup.mk'_surjective A)
  rw [← upperCentralSeriesStep_eq_comap_center, he, comap_map_eq_self]
  simpa only [QuotientGroup.ker_mk'] using hA.le
end Subgroup
