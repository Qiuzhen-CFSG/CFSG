module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Centralizers
public import Theory.Representation.BinaryPermutation.FiveOddInvolution
/-!
# Even actors from the original A₅ singular line

The Sylow-fixed source line is singular. An odd involution of S₅ is a
transposition, whose nonzero displacements on the deleted module are
nonsingular. Thus mixed commutators into the source line force every actor
on the original rank-three subgroup to be even.

Source: Aschbacher–Smith, 13.5.7, verification of F.9.1(e), printed p.918.
-/

@[expose] public section
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator
open Section06.CentralizerReduction A5Module A5Module.FlagCoordinates
open A5Module.FlagCoordinates.SylowCalculation
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- Every vector in the original invariant line is singular. -/
theorem source_line_singular (d : FlagSource T L V V₁ V₂)
    (x : Space) (hx : d.module.map (Multiplicative.ofAdd x) ∈ V₁) :
    FiveGeometry.form x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hc : Nat.card (d.preimage V₁) = 2 :=
    (d.preimage_card V₁ (d.one_le_two.trans d.two_le_V)).trans d.one_card
  obtain ⟨a,ha,hunique⟩ := (Nat.card_eq_two_iff' (1 : d.preimage V₁)).mp hc
  have hxu : (⟨Multiplicative.ofAdd x,hx⟩ : d.preimage V₁) ≠ 1 := by
    intro he
    exact hx0 (congrArg (fun u : d.preimage V₁ => u.val.toAdd) he)
  apply sylow_fixed_singular d.image d.alternating_le_image d.imageSylow x
  intro p hp
  have hym := d.preimage_invariant V₁ d.one_invariant p hp (Multiplicative.ofAdd x) hx
  have hyu : (⟨Multiplicative.ofAdd (rho p.val x),hym⟩ : d.preimage V₁) ≠ 1 := by
    intro he
    have h : coordinateEquiv p.val (Multiplicative.ofAdd x) = 1 := congrArg Subtype.val he
    have hz := (coordinateEquiv p.val).injective (h.trans (map_one _).symm)
    exact hx0 hz
  exact congrArg (fun u : d.preimage V₁ => u.val.toAdd)
    ((hunique _ hyu).trans (hunique _ hxu).symm)

/-- The literal permutation action of a subgroup normalizing the chosen V. -/
def actor (d : FlagSource T L V V₁ V₂) (A : Subgroup G)
    (hAN : A ≤ normalizer (V : Set G)) : A →* Equiv.Perm (Fin 5) :=
  d.normalizerAction.comp (inclusion hAN)

/-- Mixed commutators into the source singular line exclude odd involutions
from the actual permutation image. -/
theorem actor_even (d : FlagSource T L V V₁ V₂)
    (W A : Subgroup G) [IsElementaryAbelian 2 A]
    (hWV : W ≤ V) (hW : Nat.card W = 8)
    (hTW : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hAN : A ≤ normalizer (V : Set G)) (hAW : ⁅W,A⁆ ≤ V₁) :
    (actor d A hAN).range ≤ alternatingGroup (Fin 5) := by
  rintro p ⟨a,rfl⟩
  let n : normalizer (V : Set G) := inclusion hAN a
  have ha2 : n ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
  apply FiveOddInvolution.even_of_singular_displacements (d.preimage W)
    (fun p hp => fixer_third d W hWV hW hTW p hp)
  · change (d.normalizerAction n) ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  · intro x hx
    apply source_line_singular d
    have hAW' : ⁅A,W⁆ ≤ V₁ := by rwa [commutator_comm]
    have hc := hAW' (commutator_mem_commutator a.property hx)
    convert hc using 1
    rw [ofAdd_sub,map_div,div_eq_mul_inv]
    change d.module.map (Multiplicative.ofAdd (rho (d.normalizerAction n) x.toAdd)) *
      (d.module.map x)⁻¹ = _
    rw [← d.normalizer_equivariant n x.toAdd]
    rfl
end CFSG.Quasithin.Chapter13.Section05.A5Source.Commutator
