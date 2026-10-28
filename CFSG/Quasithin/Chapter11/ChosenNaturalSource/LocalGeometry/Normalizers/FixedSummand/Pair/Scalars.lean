module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand

/-!
# Scalar coordinates for the actual point-radical action

A binary splitting of the original omega center into a field line and its
literal fixed subspace, together with a surjective scalar character, gives
a faithful cyclic Cartan image. Its order is q-1. Every displacement has
zero fixed coordinate, so field multiplication is regular on nonzero
moved vectors. A nonidentity scalar identifies the entire fixed space.

This module proves consequences of concrete coordinates; their construction
from the chosen block remains a separate obligation. No GO hypothesis or
fixed-summand normalization is built into the marking. The argument includes
q=4 and uses the quotient projection defined in FixedSummand.Action.
Source: Aschbacher--Smith, 11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] {R L X : Subgroup G} {F : BinaryField}

/-- A scalar marking on the actual omega center. Its second coordinate is
literally the specified fixed subspace, with its original inclusion. -/
structure ScalarDecomposition (R L X : Subgroup G) (F : BinaryField) where
  equiv : Additive (radicalOmegaCenter R) ≃ₗ[ZMod 2]
    F.Carrier × fixedSubspace R L
  character : cartanImage R X →* F.Carrierˣ
  onto : Function.Surjective character
  intertwines : ∀ (x : cartanImage R X) (z : Additive (radicalOmegaCenter R)),
    equiv (representation R x z) = ((character x : F.Carrier) * (equiv z).1, (equiv z).2)
  fixed : ∀ z : fixedSubspace R L, equiv z = (0, z)

namespace ScalarDecomposition
variable (m : ScalarDecomposition R L X F)
include m

theorem character_injective : Function.Injective m.character := by
  intro a b hab
  apply Subtype.ext
  apply representation_injective R
  apply LinearMap.ext
  intro z
  apply m.equiv.injective
  rw [m.intertwines, m.intertwines, hab]

def actorEquiv : cartanImage R X ≃* F.Carrierˣ :=
  MulEquiv.ofBijective m.character ⟨m.character_injective, m.onto⟩

theorem cyclic : IsCyclic (cartanImage R X) := (actorEquiv m).isCyclic.mpr inferInstance

theorem card : Nat.card (cartanImage R X) = 2 ^ F.degree - 1 := by
  rw [Nat.card_congr (actorEquiv m).toEquiv, Nat.card_units, F.card_eq]

omit m in
private theorem units_nontrivial (hF : 1 < F.degree) : Nontrivial F.Carrierˣ := by
  apply (Finite.one_lt_card_iff_nontrivial).mp
  rw [Nat.card_units, F.card_eq]
  have hh : 2 ^ 2 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide) hF
  omega

theorem nontrivial (hF : 1 < F.degree) : cartanImage R X ≠ ⊥ := by
  intro he
  have hh := m.card
  rw [he, Subgroup.card_bot] at hh
  have hp : 2 ^ 2 ≤ 2 ^ F.degree := Nat.pow_le_pow_right (by decide) hF
  omega

theorem fixedSpace_eq (hF : 1 < F.degree) :
    fixedSpace (representation R) (cartanImage R X) = fixedSubspace R L := by
  have := units_nontrivial (F := F) hF
  obtain ⟨a, ha⟩ := exists_ne (1 : F.Carrierˣ)
  obtain ⟨x, hx⟩ := m.onto a
  ext z
  constructor
  · intro hz
    have hh := congrArg Prod.fst ((m.intertwines x z).symm.trans (congrArg m.equiv (hz x)))
    change (m.character x : F.Carrier) * (m.equiv z).1 = (m.equiv z).1 at hh
    rw [hx] at hh
    have hz0 : (m.equiv z).1 = 0 := by
      by_contra hn
      apply ha
      apply Units.ext
      exact (mul_right_cancel₀ hn) (hh.trans (one_mul _).symm)
    have he : z = ((m.equiv z).2 : Additive (radicalOmegaCenter R)) := by
      apply m.equiv.injective
      rw [m.fixed]
      exact Prod.ext hz0 rfl
    rw [he]
    exact (m.equiv z).2.property
  · intro hz x
    apply m.equiv.injective
    change m.equiv (representation R x z) = m.equiv z
    rw [m.intertwines, m.fixed ⟨z, hz⟩, mul_zero]

theorem moved_second_zero {z : Additive (radicalOmegaCenter R)}
    (hz : z ∈ RegularCyclicNormalClosure.displacementSpan (representation R) (cartanImage R X) ⊤) :
    (m.equiv z).2 = 0 := by
  let p : Additive (radicalOmegaCenter R) →ₗ[ZMod 2] fixedSubspace R L :=
    (LinearMap.snd (ZMod 2) F.Carrier (fixedSubspace R L)).comp m.equiv.toLinearMap
  have hle : RegularCyclicNormalClosure.displacementSpan (representation R) (cartanImage R X) ⊤ ≤
      p.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    change (m.equiv (representation R x v - v)).2 = 0
    rw [map_sub, m.intertwines ⟨x, hx⟩ v]
    exact sub_self _
  exact hle hz

theorem transitive :
    ∀ v ∈ RegularCyclicNormalClosure.displacementSpan (representation R) (cartanImage R X) ⊤,
      v ≠ 0 → ∀ w ∈ RegularCyclicNormalClosure.displacementSpan
        (representation R) (cartanImage R X) ⊤, w ≠ 0 →
      ∃ x : cartanImage R X, representation R x v = w := by
  intro v hv hv0 w hw hw0
  have hev : (m.equiv v).1 ≠ 0 := by
    intro hh
    apply hv0
    apply m.equiv.injective
    rw [map_zero]
    exact Prod.ext hh (m.moved_second_zero hv)
  have hew : (m.equiv w).1 ≠ 0 := by
    intro hh
    apply hw0
    apply m.equiv.injective
    rw [map_zero]
    exact Prod.ext hh (m.moved_second_zero hw)
  obtain ⟨x, hx⟩ := m.onto (Units.mk0 ((m.equiv w).1 / (m.equiv v).1) (div_ne_zero hew hev))
  refine ⟨x, m.equiv.injective ?_⟩
  rw [m.intertwines, hx]
  apply Prod.ext
  · exact div_mul_cancel₀ _ hev
  · exact (m.moved_second_zero hv).trans (m.moved_second_zero hw).symm

/-- The scalar marking proves regularity, including uniqueness, on the
nonzero vectors of the literal displacement span. -/
theorem regular :
    ∀ v ∈ RegularCyclicNormalClosure.displacementSpan (representation R) (cartanImage R X) ⊤,
      v ≠ 0 → ∀ w ∈ RegularCyclicNormalClosure.displacementSpan
        (representation R) (cartanImage R X) ⊤, w ≠ 0 →
      ∃! x : cartanImage R X, representation R x v = w := by
  intro v hv hv0 w hw hw0
  obtain ⟨x, hx⟩ := m.transitive v hv hv0 w hw hw0
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply m.character_injective
  apply Units.ext
  have hev : (m.equiv v).1 ≠ 0 := by
    intro hh
    apply hv0
    apply m.equiv.injective
    rw [map_zero]
    exact Prod.ext hh (m.moved_second_zero hv)
  apply mul_right_cancel₀ hev
  have hh := congrArg (fun z => (m.equiv z).1) (hy.trans hx.symm)
  simpa only [m.intertwines] using hh

end ScalarDecomposition
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
