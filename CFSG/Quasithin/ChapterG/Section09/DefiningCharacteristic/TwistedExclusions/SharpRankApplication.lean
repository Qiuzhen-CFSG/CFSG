module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.ComponentRank
public import Theory.SpecificGroups.Triality.StandardTwoRank.Automorphisms

/-!
# The sharp triality rank application at exponent two

The original component and its literal model isomorphism supply the
simplicity and perfectness used by the all-exponent automorphism bound.
The source actor therefore has rank at most 5n. At n = 2 the same faithful
representation has degree at least 24, whereas the source degree bound is
at most 22, a contradiction. No additional model or geometric premise
remains in these applications of the sharp bound.

The older fixed-group and normalization/descent adapters retain their
interfaces as alternative conditional routes. The Q8/Frobenius argument
at exponent two gives only degree 24, not a strict bound beyond 24; the
sharp rank resolves that case.

Source: Aschbacher--Smith, G.9.3, printed p.356 (`refs/quasithin.pdf`),
and GLS3 §2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
open Triality.Standard Triality.Standard.OuterOdd Triality.Standard.EvenField
open Triality.Standard.TwoRank.Automorphisms
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The actual source component supplies the model instances, so its actor
satisfies the sharp bound at every positive binary exponent. -/
theorem triality_actor_rank_le_five_mul
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (e : L ≃* BinaryCarrier n hn) : m ≤ 5 * n := by
  apply actor_rank_le_of_inherited_model_estimate h e
  intro hs hp
  let := hs
  let := hp
  exact automorphism_twoRank_le_five_mul n hn

/-- Apply the all-exponent sharp estimate to the original exponent-two
component: its faithful module would have degree at least 24 and at most 22. -/
theorem not_triality_four_of_sharp_rank
    (h : ComponentHypothesis K ρ A L L m)
    (model : IsTrialityGroupAt (2 ^ 2) L) : False := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L 2 (by decide)).mp model
  have hm := triality_actor_rank_le_five_mul h (by decide) e
  have hd := Triality.PrimitiveDegree.finrank_ge 2 (by decide)
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

/-- The source actor has rank at most ten once its model's outer involution
fixed groups have been identified. The component supplies both model instances. -/
theorem triality_four_actor_rank_le_of_fixed_models
    (h : ComponentHypothesis K ρ A L L m)
    (e : L ≃* BinaryCarrier 2 (by decide))
    (hmodels : ∀ a : MulAut (BinaryCarrier 2 (by decide)), a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier 2 (by decide)) →
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier 1 Nat.zero_lt_one)) : m ≤ 10 := by
  apply actor_rank_le_of_inherited_model_estimate h e
  intro hs hp
  let := hs
  let := hp
  apply automorphism_twoRank_le_of_fixed_models 2 (Nat.zero_lt_succ 1)
  intro a ha hi
  exact ⟨1, Nat.zero_lt_one, rfl, hmodels a ha hi⟩

/-- At n = 2, sharp actor rank contradicts the proved primitive degree bound
for the original action. Only the geometric fixed-group premise remains. -/
theorem not_triality_four_of_fixed_models
    (h : ComponentHypothesis K ρ A L L m)
    (model : IsTrialityGroupAt (2 ^ 2) L)
    (hmodels : ∀ a : MulAut (BinaryCarrier 2 (by decide)), a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier 2 (by decide)) →
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier 1 Nat.zero_lt_one)) : False := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L 2 (by decide)).mp model
  have hm := triality_four_actor_rank_le_of_fixed_models h e hmodels
  have hd := Triality.PrimitiveDegree.finrank_ge 2 (by decide)
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

/-- Apply the two separately owned field inputs at the exact canonical
coefficient involution Frobenius³ on GF(64). Coverage is already proved,
and the source component supplies its required instances. -/
theorem not_triality_four_of_normalization_descent
    (h : ComponentHypothesis K ρ A L L m)
    (model : IsTrialityGroupAt (2 ^ 2) L)
    (hnormalize : ∀ (a : MulAut (BinaryCarrier 2 (by decide))), a ^ 2 = 1 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier 2 (by decide)) →
      ∀ (g : BinaryCarrier 2 (by decide))
        (e : CoefficientAut (binaryParameters 2 (by decide))),
      a = MulAut.conj g * coefficientAction (binaryParameters 2 (by decide)) e →
      ∃ b : MulAut (BinaryCarrier 2 (by decide)), ∀ x, b (a x) =
        coefficientAction (binaryParameters 2 (by decide))
          (coefficientFrobenius 2 (by decide) 3) (b x))
    (hdescent : Nonempty ((coefficientAction (binaryParameters 2 (by decide))
      (coefficientFrobenius 2 (by decide) 3)).fixedSubgroup ≃*
        BinaryCarrier 1 Nat.zero_lt_one)) : False := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L 2 (by decide)).mp model
  obtain ⟨_, hp, hs⟩ := inherited_model_hypotheses h e
  let := hp
  let := hs
  apply not_triality_four_of_fixed_models h model
  intro a ha hi
  obtain ⟨g, f, hf⟩ := OuterOdd.Coverage.binary_inner_coefficient 2 (Nat.zero_lt_succ 1) a
  obtain ⟨b, hb⟩ := hnormalize a ha hi g f hf
  obtain ⟨d⟩ := hdescent
  exact ⟨(MulAut.fixedSubgroupEquivOfCompatible b a _ hb).trans d⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
