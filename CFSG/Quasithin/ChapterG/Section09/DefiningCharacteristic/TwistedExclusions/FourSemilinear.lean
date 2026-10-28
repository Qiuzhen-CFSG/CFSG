module

public import Theory.SpecificGroups.Triality.StandardTwoRank.FourSemilinear
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.TrialityReduction

/-!
# Completing the binary triality exclusion in the original G.9 component

At exponent two, the genuine semilinear automorphism bound gives actor rank
at most ten, hence degree at most 22. The existing primitive-prime bound on
the same faithful representation gives degree at least 24. The original
component and its actual triality isomorphism supply every simplicity and
perfectness instance needed by automorphism coverage. Combining this case
with `TrialityReduction` excludes all positive binary exponents.

Source: Aschbacher--Smith, G.9.3, printed p.356 (`refs/quasithin.pdf`).
This proof needs only the proved weaker primitive-prime degree bound, not
the separate general 24*n representation-theory assertion.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Triality.Standard

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : CFSG.Quasithin.GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The original source component cannot be the genuine triality group over GF(4). -/
theorem not_triality_four_of_source_component
    (h : ComponentHypothesis K ρ A L L m)
    (model : IsTrialityGroupAt (2 ^ 2) L) : False := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L 2 (Nat.succ_pos 1)).mp model
  have hm : m ≤ 10 := actor_rank_le_of_inherited_model_estimate h e
    (fun hsimple hperfect => @TwoRank.FourSemilinear.automorphism_twoRank_le_ten hsimple hperfect)
  have hd := Triality.PrimitiveDegree.finrank_ge 2 (Nat.succ_pos 1)
    ((ρ.comp L.subtype).comp e.symm.toMonoidHom)
    ((h.faithful.comp L.subtype_injective).comp e.symm.injective)
  have hu := h.degree_le
  omega

/-- All positive binary triality parameters are excluded from the original component. -/
theorem not_triality_binary_of_source_component
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (model : IsTrialityGroupAt (2 ^ n) L) : False := by
  have he := triality_parameter_eq_two_of_source_component h hn model
  subst n
  exact not_triality_four_of_source_component h model

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
