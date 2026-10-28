module

public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.Representation.BinaryOffender.Defs
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Gaschütz fixed-vector detection for the marked `SL₂(4)` Borel

This is the reusable first Gaschütz step from Aschbacher--Smith 14.7.74.
The displacement hypothesis says that the quotient by the displayed natural
(or contragredient natural) section is trivial. The literal upper Borel has
no fixed vectors in the natural and dual natural sections. A fixed lift
modulo that section therefore detects fixed vectors on any subgroup mapping
onto the Borel and containing a Sylow two subgroup.

The legacy `fixed_of_marked_borel` below uses averaging and asks a Sylow
two subgroup to map onto the entire Borel. That hypothesis cannot occur:
the Borel has order twelve. It is preserved as an existing conditional API,
not used as the source application. The `of_fixed_lift` theorems expose the
correct subgroup contract and leave the independent splitting input explicit.

The subgroup and representation maps in this file are the actual maps used by
source applications; no permutation-module replacement is involved.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix.SpecialLinearGroup
namespace Representation.SL2FourNaturalBorelFixedLifting

abbrev F := SL2FourNatural.F
abbrev SL := SL2FourNatural.SL
abbrev V := SL2FourNatural.V

/-- The concrete natural Borel has no binary fixed vector. -/
theorem natural_borel_fixedSpace_eq_bot :
    fixedSpace SL2FourNatural.naturalRepresentation (rankOneBorel F) = ⊥ := by
  have he : SL2FourNatural.naturalRepresentation =
      HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2 := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    rfl
  rw [he]
  exact HigherFieldBorelFixedSpaces.sl2_borel_fixedSpace
    (by rw [Nat.card_eq_fintype_card, SL2FourNatural.card_field]; decide)

/-- The same calculation for the actual binary contragredient module. -/
theorem dual_borel_fixedSpace_eq_bot :
    fixedSpace SL2FourNatural.naturalRepresentation.dual (rankOneBorel F) = ⊥ := by
  have he : SL2FourNatural.naturalRepresentation =
      HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2 := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    rfl
  rw [he]
  exact HigherFieldBorelFixedSpaces.sl2_borel_dual_fixedSpace
    (by rw [Nat.card_eq_fintype_card, SL2FourNatural.card_field]; decide)

/-- Legacy averaging interface, with its original (unrealizable) Sylow-image
hypothesis preserved. Use the subgroup-containing-Sylow interface below for
the source application. -/
theorem fixed_of_marked_borel
    {A Y : Type*} [Group A] [Finite A]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A Y)
    (q : A →* SL) (_hq : Function.Surjective q)
    (i : IntertwiningMap (SL2FourNatural.naturalRepresentation.dual.comp q) ρ)
    (hi : Function.Injective i)
    (S : Sylow 2 A)
    (hmark : (q.comp (S : Subgroup A).subtype).range = rankOneBorel F)
    (hdisp : ∀ a y, ρ a y - y ∈ i.toLinearMap.range) :
    ∀ y ∈ fixedSpace ρ (S : Subgroup A), ∀ a, ρ a y = y := by
  intro y hy a
  have hzero : ∀ v : Module.Dual (ZMod 2) V,
      v ∈ fixedSpace (SL2FourNatural.naturalRepresentation.dual.comp q) S → v = 0 := by
    intro v hv
    have hm : v ∈ fixedSpace SL2FourNatural.naturalRepresentation.dual (rankOneBorel F) := by
      intro b
      have hb : b.val ∈ (q.comp (S : Subgroup A).subtype).range := hmark.symm ▸ b.property
      obtain ⟨s, hs⟩ := hb
      change SL2FourNatural.naturalRepresentation.dual b v = v
      rw [← hs]
      exact hv s
    rw [dual_borel_fixedSpace_eq_bot, Submodule.mem_bot] at hm
    exact hm
  have hfixed : ∀ (a : A) (v : Module.Dual (ZMod 2) V),
      v ∈ fixedSpace (SL2FourNatural.naturalRepresentation.dual.comp q) (S : Subgroup A) →
      (SL2FourNatural.naturalRepresentation.dual.comp q) a v = v := by
    intro a v hv
    simp [hzero v hv]
  exact (BinarySylowFixedSpace.fixes_of_trivial_quotient
    ρ (SL2FourNatural.naturalRepresentation.dual.comp q) i hi hdisp S
    (fun v hv => hfixed a v hv)) y hy

/-- Fixed-lift detection on a subgroup containing an actual Sylow subgroup.
The independent lifting premise is the output required from Gaschütz
splitting; it concerns a trivial quotient, not Borel detection. -/
theorem fixed_of_subgroup_of_fixed_lift
    {A Y N : Type*} [Group A]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) A Y) (σ : Representation (ZMod 2) A N)
    (i : IntertwiningMap σ ρ) (hi : Function.Injective i)
    (B : Subgroup A) (S : Sylow 2 A) (hSB : (S : Subgroup A) ≤ B)
    (hzero : fixedSpace σ B = ⊥)
    (hlift : ∀ y ∈ fixedSpace ρ (S : Subgroup A),
      ∃ w, (∀ a, ρ a w = w) ∧ y - w ∈ i.toLinearMap.range) :
    ∀ y ∈ fixedSpace ρ B, ∀ a, ρ a y = y := by
  intro y hy a
  obtain ⟨w, hw, v, hv⟩ := hlift y (fun s => hy ⟨s, hSB s.property⟩)
  change i v = y - w at hv
  have hfix : v ∈ fixedSpace σ B := by
    intro b
    apply hi
    change i (σ (b : A) v) = i v
    rw [i.isIntertwining, hv, map_sub, hw]
    exact congrArg (fun z => z - w) (hy b)
  have hv0 : v = 0 := by simpa only [hzero, Submodule.mem_bot] using hfix
  have hyw : y = w := sub_eq_zero.mp (by simpa only [hv0, map_zero] using hv.symm)
  simpa only [hyw] using hw a

/-- The correct marked natural-module detector, conditional on a genuine
fixed-lift theorem for the displayed representation and section. -/
theorem natural_fixed_of_borel_of_fixed_lift
    {A Y : Type*} [Group A]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A Y) (q : A →* SL)
    (i : IntertwiningMap (SL2FourNatural.naturalRepresentation.comp q) ρ)
    (hi : Function.Injective i) (B : Subgroup A) (S : Sylow 2 A)
    (hSB : (S : Subgroup A) ≤ B) (hmark : B.map q = rankOneBorel F)
    (hlift : ∀ y ∈ fixedSpace ρ (S : Subgroup A),
      ∃ w, (∀ a, ρ a w = w) ∧ y - w ∈ i.toLinearMap.range) :
    ∀ y ∈ fixedSpace ρ B, ∀ a, ρ a y = y := by
  apply fixed_of_subgroup_of_fixed_lift ρ _ i hi B S hSB _ hlift
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hf : v ∈ fixedSpace SL2FourNatural.naturalRepresentation (rankOneBorel F) := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha, rfl⟩ := hmark.symm ▸ hb
    exact hv ⟨a, ha⟩
  simpa only [natural_borel_fixedSpace_eq_bot, Submodule.mem_bot] using hf

/-- The same detector for the actual binary dual of the natural module. -/
theorem dual_fixed_of_borel_of_fixed_lift
    {A Y : Type*} [Group A]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) A Y) (q : A →* SL)
    (i : IntertwiningMap (SL2FourNatural.naturalRepresentation.dual.comp q) ρ)
    (hi : Function.Injective i) (B : Subgroup A) (S : Sylow 2 A)
    (hSB : (S : Subgroup A) ≤ B) (hmark : B.map q = rankOneBorel F)
    (hlift : ∀ y ∈ fixedSpace ρ (S : Subgroup A),
      ∃ w, (∀ a, ρ a w = w) ∧ y - w ∈ i.toLinearMap.range) :
    ∀ y ∈ fixedSpace ρ B, ∀ a, ρ a y = y := by
  apply fixed_of_subgroup_of_fixed_lift ρ _ i hi B S hSB _ hlift
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hf : v ∈ fixedSpace SL2FourNatural.naturalRepresentation.dual (rankOneBorel F) := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha, rfl⟩ := hmark.symm ▸ hb
    exact hv ⟨a, ha⟩
  simpa only [dual_borel_fixedSpace_eq_bot, Submodule.mem_bot] using hf

end Representation.SL2FourNaturalBorelFixedLifting
