module
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Linear
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# Restricting binary A₇ blocks to a normalized A₅

The placed A₅ fixes two letters. Its Sylow four-groups therefore fix three
letters and centralize a genuine three-cycle. The fixed-space calculation for a
faithful binary four-dimensional A₇ module forces the Sylow action to be
quadratic. This is the exact four-space side of the C.5.13 matching.

Source: Aschbacher–Smith, C.5.13, printed p.163; the fixed-space input is
proved in `AlternatingSevenConjugatePair.Model.InnerElements`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingSevenFiveRestriction
open AlternatingSevenConjugatePair.FixedFamily
open Theory.SpecificGroups.Alternating.SevenFivePlacement
local notation "A7" => alternatingGroup (Fin 7)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The commuting cubic forces every involution displacement into the common
fixed plane, hence the whole two-group is quadratic. -/
theorem quadratic_of_centralizing_three
    (ρ : Representation (ZMod 2) A7 V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (P : Subgroup A7) (hP : IsPGroup 2 P) (hsq : ∀ a ∈ P, a ^ 2 = 1)
    (c : A7) (hc : orderOf c = 3) (hcomm : ∀ a ∈ P, Commute a c) :
    IsQuadratic ρ P := by
  have hf := cubic_centralizer_fixed_dimension ρ hρ P hP c
    (by simpa only [hc] using pow_orderOf_eq_one c)
    (by intro h; simp [h] at hc) (fun a ha => (hcomm a ha).eq)
  intro a ha b hb v
  by_cases hb1 : b = 1
  · simp [hb1]
  have ho : orderOf b = 2 := orderOf_eq_prime (hsq b hb) hb1
  have hc2 := AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hρ hdim b ho
  have hdimB : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers b)) = 2 := by
    have hh := fixedCodim_add_finrank ρ (zpowers b)
    omega
  have hle := fixedSpace_antitone ρ (zpowers_le.mpr hb)
  have he : fixedSpace ρ P = fixedSpace ρ (zpowers b) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      have hh := Submodule.finrank_mono hle
      omega)
  have hv : ρ b v - v ∈ fixedSpace ρ (zpowers b) :=
    involution_range_le_fixed ρ b (hsq b hb) ⟨v, rfl⟩
  rw [← he] at hv
  exact hv ⟨a, ha⟩

private theorem alternating_five_fourth_power :
    ∀ a : alternatingGroup (Fin 5), a ^ 4 = 1 → a ^ 2 = 1 := by
  decide +kernel

/-- Every actual Sylow two-subgroup of the normalized A₅ is quadratic on any
faithful binary four-dimensional A₇ module. -/
theorem sylow_quadratic
    (ρ : Representation (ZMod 2) A7 V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (P : Sylow 2 B) : IsQuadratic ρ ((P : Subgroup B).map B.subtype) := by
  let Q := (P : Subgroup B).map B.subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map B.subtype
  obtain ⟨c, hc, hcomm⟩ := exists_centralizing_three B e S hSN Q hQ (map_subtype_le _)
  apply quadratic_of_centralizing_three ρ hρ hdim Q hQ ?_ c hc hcomm
  rintro a ⟨b, hb, rfl⟩
  have hcard : Nat.card P = 4 := by
    have hh := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    change Nat.card ((P : Subgroup B).map e.toMonoidHom) = 4 at hh
    rwa [card_map_of_injective e.injective] at hh
  have hp : b ^ 4 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨b, hb⟩ : P))
    change (⟨b, hb⟩ : (P : Subgroup B)) ^ Nat.card (P : Subgroup B) = 1 at hh
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have h2 : b ^ 2 = 1 := e.injective (by
    rw [map_pow, map_one]
    exact alternating_five_fourth_power (e b) (by rw [← map_pow, hp, map_one]))
  exact congrArg B.subtype h2
end Representation.AlternatingSevenFiveRestriction
