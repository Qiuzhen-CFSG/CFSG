module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Coordinates

/-!
# Centralizer indices from the natural plane action

A nonzero upper-unipotent parameter fixes precisely the first coordinate
line. If fixed points lift through the central quotient, C_U(B) is therefore
the kernel of the surjective second-coordinate homomorphism for every
noncentralizing B ≤ S. The kernel-index theorem gives its index |F|. The
parameter homomorphism independently gives |S:C_S(U)| = |F|.

These computations concern the full embedded U and S. The central layer
of U is retained in the projection kernel; its triviality is not assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.6 (*),
printed p.156 (PDF p.167).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
open Subgroup
universe u
variable {G : Type u} [Group G] {R L : Subgroup G}
variable {F : Type*} [Field F] (c : ActionCoordinates R L F)

private theorem conj_eq_iff (s : S R) (v : U L) :
    moduleConjugate c.normalizes s v = v ↔ (s : G) * (v : G) = (v : G) * s := by
  rw [Subtype.ext_iff]
  change (s : G) * (v : G) * (s : G)⁻¹ = (v : G) ↔ _
  exact mul_inv_eq_iff_eq_mul

private theorem projection_fixed_iff (s : S R) (v : U L) :
    c.projection (moduleConjugate c.normalizes s v) = c.projection v ↔
      (c.parameter s).toAdd * (c.projection v).toAdd 1 = 0 := by
  rw [← Multiplicative.toAdd.injective.eq_iff, c.equivariant]
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa using h0
  · intro h
    ext i
    fin_cases i <;> simp [h]

include c in
/-- The order of the actual Baumann action is the order of the field. -/
theorem actor_index :
    (centralizer (U L : Set G)).relIndex (S R) = Nat.card F := by
  have hk : (centralizer (U L : Set G)).subgroupOf (S R) = c.parameter.ker := by
    ext s
    exact (c.parameter_kernel s).symm
  change ((centralizer (U L : Set G)).subgroupOf (S R)).index = _
  rw [hk, index_ker, c.parameter.range_eq_top_of_surjective c.parameter_surjective]
  exact Nat.card_congr (topEquiv.toEquiv.trans Multiplicative.toAdd)

private def secondCoordinate : U L →* Multiplicative F where
  toFun v := Multiplicative.ofAdd ((c.projection v).toAdd 1)
  map_one' := by simp
  map_mul' a b := by simp

private theorem secondCoordinate_surjective : Function.Surjective (secondCoordinate c) := by
  intro a
  obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd ![0, a.toAdd])
  refine ⟨v, ?_⟩
  change Multiplicative.ofAdd ((c.projection v).toAdd 1) = a
  rw [hv]
  rfl

/-- Every nontrivial subgroup of the natural actor has the same fixed line.
The fixed-lifting premise retains the central layer of the full U. -/
theorem module_index_of_fixedLift (hlift : c.FixedLift)
    (B : Subgroup G) (hB : B ≤ S R) (hnc : ¬ B ≤ centralizer (U L : Set G)) :
    (centralizer (B : Set G)).relIndex (U L) = Nat.card F := by
  obtain ⟨b, hb, hbnc⟩ := SetLike.not_le_iff_exists.mp hnc
  let s : S R := ⟨b, hB hb⟩
  have hs : (c.parameter s).toAdd ≠ 0 := by
    intro hz
    apply hbnc
    apply (c.parameter_kernel s).mp
    exact Multiplicative.toAdd.injective hz
  have hk : (centralizer (B : Set G)).subgroupOf (U L) = (secondCoordinate c).ker := by
    ext v
    change (∀ y ∈ B, y * (v : G) = (v : G) * y) ↔
      (c.projection v).toAdd 1 = 0
    constructor
    · intro hv
      have hfix := (conj_eq_iff c s v).mpr (hv b hb)
      have hh := (projection_fixed_iff c s v).mp (congrArg c.projection hfix)
      exact (mul_eq_zero.mp hh).resolve_left hs
    · intro hv y hy
      apply (conj_eq_iff c ⟨y, hB hy⟩ v).mp
      apply hlift
      exact (projection_fixed_iff c ⟨y, hB hy⟩ v).mpr (by rw [hv, mul_zero])
  change ((centralizer (B : Set G)).subgroupOf (U L)).index = _
  rw [hk, index_ker,
    (secondCoordinate c).range_eq_top_of_surjective (secondCoordinate_surjective c)]
  exact Nat.card_congr (topEquiv.toEquiv.trans Multiplicative.toAdd)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
end
