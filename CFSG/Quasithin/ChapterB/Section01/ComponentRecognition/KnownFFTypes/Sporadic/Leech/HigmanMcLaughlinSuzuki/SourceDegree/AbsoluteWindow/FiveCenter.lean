module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.SplitMultiplicity

/-!+# Exact five-center multiplicity in the Higman--Sims degree window

The center of the certified extraspecial subgroup of order 125 is a literal
subgroup of the degree-100 HS carrier. Its four nontrivial central characters
are fused, and their constituents have degree five. Consequently every faithful
characteristic-two representation has dimension f + 20a, where f is the
dimension fixed by this center and a is positive. Scalar extension and descent
in the reusable extraspecial theorem keep the original coefficient field.

In the window at most fifty, a is one or two. This reduces degree recognition
to a fixed-space calculation and exclusion of absolute degree forty; it does
not assert either of these remaining calculations. At degree twenty the same
formula already proves that this actual center is fixed-point-free.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16; Aschbacher--Smith K.4, printed p.457.
The generic theorem has a unitary namespace but its statement concerns an
arbitrary extraspecial five-subgroup; no unitary model is used here.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow

open Subgroup

local notation "P₅" => _root_.Sporadic.LeechRelated.HS.FiveSubgroup.subgroup

/-- The image in HS of the center of its certified order-125 subgroup. -/
noncomputable def fiveCenter : Subgroup KnownSimple.SporadicName.hs.Carrier :=
  (center P₅).map (P₅).subtype

variable {K W : Type*} [Field K] [CharP K 2]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (τ : Representation K KnownSimple.SporadicName.hs.Carrier W)

/-- The fixed dimension uses the actual subgroup inclusion on the original
coefficient field, rather than a character value or an abstract group tag. -/
noncomputable def fiveCenterFixedDimension : ℕ :=
  Module.finrank K (Representation.invariants (τ.comp fiveCenter.subtype))

/-- The nonlinear central part is a positive multiple of twenty. -/
theorem finrank_eq_fixed_add_twenty_mul (hf : Function.Injective τ) :
    ∃ a : ℕ, 0 < a ∧ Module.finrank K W = fiveCenterFixedDimension τ + 20 * a := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  let : IsExtraspecial 5 P₅ :=
    IsExtraspecial.of_noncommutative_card_prime_cube
      _root_.Sporadic.LeechRelated.HS.FiveSubgroup.card_subgroup
      _root_.Sporadic.LeechRelated.HS.FiveSubgroup.subgroup_not_commutative
  obtain ⟨z, hz, hz1, g, hg⟩ :=
    _root_.Sporadic.LeechRelated.HS.FiveSubgroup.RationalFusion.central_fusion
  have hne : τ z.val ≠ 1 := by
    intro he
    exact hz1 (Subtype.ext (hf (he.trans (map_one τ).symm)))
  exact Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.multiplicity
    (G := _root_.Sporadic.LeechRelated.HS.Carrier)
    τ P₅ _root_.Sporadic.LeechRelated.HS.FiveSubgroup.card_subgroup z hz hz1 hne g hg

/-- Only one or two copies of each degree-five central constituent can occur
below degree fifty-one. No irreducibility premise is needed for this step. -/
theorem finrank_eq_fixed_add_twenty_or_forty (hf : Function.Injective τ)
    (hd : Module.finrank K W ≤ 50) :
    Module.finrank K W = fiveCenterFixedDimension τ + 20 ∨
      Module.finrank K W = fiveCenterFixedDimension τ + 40 := by
  obtain ⟨a, ha, he⟩ := finrank_eq_fixed_add_twenty_mul τ hf
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with rfl | rfl
  · left
    omega
  · right
    omega

/-- At degree twenty the literal five-center already acts without fixed
vectors, for every faithful representation over a characteristic-two field. -/
theorem fiveCenter_fixed_eq_bot_of_finrank_twenty (hf : Function.Injective τ)
    (hd : Module.finrank K W = 20) :
    Representation.invariants (τ.comp fiveCenter.subtype) = ⊥ := by
  obtain ⟨a, ha, he⟩ := finrank_eq_fixed_add_twenty_mul τ hf
  have hz : fiveCenterFixedDimension τ = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hz

/-- The missing fixed-space calculation would leave only absolute degrees
twenty and forty in the source window. -/
theorem finrank_eq_twenty_or_forty_of_fiveCenter_fixed_eq_bot
    (hf : Function.Injective τ) (hd : Module.finrank K W ≤ 50)
    (hfix : Representation.invariants (τ.comp fiveCenter.subtype) = ⊥) :
    Module.finrank K W = 20 ∨ Module.finrank K W = 40 := by
  have hz : fiveCenterFixedDimension τ = 0 := by
    exact Submodule.finrank_eq_zero.mpr hfix
  simpa only [hz, zero_add] using finrank_eq_fixed_add_twenty_or_forty τ hf hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow
