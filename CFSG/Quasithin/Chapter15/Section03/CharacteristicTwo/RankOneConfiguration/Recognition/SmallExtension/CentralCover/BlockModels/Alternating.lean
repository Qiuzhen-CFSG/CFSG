module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Models
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Even
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Cocycle tests for the binary A₆ natural module

Every cocycle is the displacement of a full six-letter permutation vector,
by the checked normalization theorem. Two concrete cubic elements generate
a transitive action on the six letters. Constant displacement under a cubic
is zero, so their common displacement kernel consists exactly of constants.
This proves detection of actual cocycles, including principal cocycles.
Cubic order also puts the tests in the source O^{3′} residual.

Source: Aschbacher--Smith, I.1.6(1), printed p.408, and the A₆-block branch
of 15.3.31, printed p.1132, combined manuscript (1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
namespace Alternating

abbrev Actor := alternatingGroup (Fin 6)
abbrev Coefficients := natural (Fin 6)
abbrev action : Representation (ZMod 2) Actor Coefficients :=
  alternatingNaturalRepresentation (Fin 6)

/-- A cubic cycling the three pairs of the standard partition. -/
def cubicOne : Actor :=
  ⟨Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 3 * Equiv.swap 3 5, by
    change Equiv.Perm.sign _ = 1
    decide +kernel⟩

/-- Its conjugate by an even interchange within two of the pairs. -/
def cubicTwo : Actor :=
  ⟨(Equiv.swap 0 1 * Equiv.swap 2 3) * cubicOne.val *
    (Equiv.swap 0 1 * Equiv.swap 2 3)⁻¹, by
    change Equiv.Perm.sign _ = 1
    decide +kernel⟩

theorem cubicOne_cube : cubicOne ^ 3 = 1 := by decide +kernel
theorem cubicTwo_cube : cubicTwo ^ 3 = 1 := by decide +kernel

private theorem cubic_fixed_vectors : ∀ w : Full (Fin 6),
    representation (Fin 6) cubicOne.val w = w →
    representation (Fin 6) cubicTwo.val w = w →
    ∃ c : ZMod 2, c • allOne (Fin 6) = w := by decide +kernel

/-- The actual cocycle space, including its principal part, is the image of
the full permutation module under displacement. -/
theorem naturalDisplacement_surjective :
    Function.Surjective (naturalDisplacement (Fin 6)) := by
  intro f
  obtain ⟨v, hv⟩ := alternatingNatural_normalize_pointStabilizer 6 (Or.inl rfl) 0 f
  obtain ⟨a, ha⟩ := alternatingNatural_normalized_eq_coordinate 6 (Or.inl rfl) 0
    (f - principal action v) (by
      intro g hg
      change f.val g - (action g v - v) = 0
      exact sub_eq_zero.mpr (hv g hg))
  obtain ⟨w, hw, hwv⟩ := v.property
  let u : core (Fin 6) := ⟨w, hw⟩
  have hu : coreToNatural (Fin 6) u = v := Subtype.ext hwv
  refine ⟨a • Pi.single 0 1 + u.val, ?_⟩
  rw [map_add, map_smul, show naturalDisplacement (Fin 6) u.val =
    principal action (coreToNatural (Fin 6) u) from naturalDisplacement_core _ u, hu]
  change a • naturalCoordinateCocycle (Fin 6) 0 + principal action v = f
  rw [← ha]
  apply Subtype.ext
  funext g
  exact sub_add_cancel _ _

private theorem cubic_fixes_of_constant_displacement (g : Actor) (hg : g ^ 3 = 1)
    (w : Full (Fin 6)) (hw : representation (Fin 6) g.val w - w ∈ constants (Fin 6)) :
    representation (Fin 6) g.val w = w := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  have he : representation (Fin 6) g.val w = c • allOne (Fin 6) + w :=
    sub_eq_iff_eq_add.mp hc.symm
  have hs : representation (Fin 6) g.val (representation (Fin 6) g.val w) = w := by
    rw [he, map_add, map_smul, permute_allOne, he]
    simp [← add_assoc, ← add_smul, CharTwo.add_self_eq_zero]
  have hcube : g.val * (g.val * g.val) = 1 := by
    have ht := congrArg Subtype.val hg
    simpa only [coe_pow, coe_mul, coe_one, pow_succ, pow_zero, one_mul, mul_assoc] using ht
  calc
    representation (Fin 6) g.val w =
        representation (Fin 6) g.val (representation (Fin 6) g.val
          (representation (Fin 6) g.val w)) := by rw [hs]
    _ = representation (Fin 6) (g.val * (g.val * g.val)) w := by
      simp only [map_mul, Module.End.mul_apply]
    _ = w := by rw [hcube, map_one]; rfl

/-- Two concrete cubic elements detect all natural A₆ cocycles. Their
parabolic membership, rather than a cover-rigidity premise, is the marking
obligation of a geometric application. -/
theorem detectedOn_of_cubics (B : Subgroup Actor)
    (h₁ : cubicOne ∈ B) (h₂ : cubicTwo ∈ B) : DetectedOn action B := by
  intro f hf
  obtain ⟨w, rfl⟩ := naturalDisplacement_surjective f
  have hc (g : Actor) (hg : g ∈ B) :
      representation (Fin 6) g.val w - w ∈ constants (Fin 6) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact congrArg (fun v : Coefficients => (v : Deleted (Fin 6))) (hf g hg)
  exact (naturalDisplacement_eq_zero_iff _ (by simp) w).mpr
    (Submodule.mem_span_singleton.mpr (cubic_fixed_vectors w
      (cubic_fixes_of_constant_displacement _ cubicOne_cube w (hc _ h₁))
      (cubic_fixes_of_constant_displacement _ cubicTwo_cube w (hc _ h₂))))

/-- For a parabolic containing the two cubics, their membership in O^{3′}
is proved from their orders. -/
theorem detectedOn_residual_of_cubics (P : Subgroup Actor)
    (h₁ : cubicOne ∈ P) (h₂ : cubicTwo ∈ P) :
    DetectedOn action ((primeToResidual 3 P).map P.subtype) := by
  apply detectedOn_of_cubics
  · refine ⟨⟨cubicOne,h₁⟩, mem_primeToResidual_of_pow (n := 1) ?_, rfl⟩
    apply Subtype.ext
    simpa using cubicOne_cube
  · refine ⟨⟨cubicTwo,h₂⟩, mem_primeToResidual_of_pow (n := 1) ?_, rfl⟩
    apply Subtype.ext
    simpa using cubicTwo_cube

private def pairVector : core (Fin 6) := ⟨![1,1,0,0,0,0], by
  change augmentation (Fin 6) _ = 0
  decide +kernel⟩

private theorem cubicOne_moves : action cubicOne (coreToNatural (Fin 6) pairVector) ≠
    coreToNatural (Fin 6) pairVector := by
  intro h
  have he := congrArg (fun v : Coefficients => (v : Deleted (Fin 6))) h
  change (constants (Fin 6)).mkQ (representation (Fin 6) cubicOne.val pairVector.val) =
    (constants (Fin 6)).mkQ pairVector.val at he
  have hm : representation (Fin 6) cubicOne.val pairVector.val - pairVector.val ∈
      constants (Fin 6) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (constants (Fin 6)).mkQ _ = 0
    rw [map_sub, he, sub_self]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have hn : ∀ c : ZMod 2, c • allOne (Fin 6) ≠
      representation (Fin 6) cubicOne.val pairVector.val - pairVector.val := by decide +kernel
  exact hn c hc

/-- Faithfulness for the actual A₆ natural-module representation. -/
theorem faithful : Function.Injective action := by
  let : IsSimpleGroup Actor := alternatingGroup.isSimpleGroup (by simp)
  apply (MonoidHom.ker_eq_bot_iff action).mp
  rcases (inferInstance : action.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hc : action cubicOne = 1 := show cubicOne ∈ action.ker by rw [h]; trivial
    exact (cubicOne_moves (by rw [hc]; rfl)).elim

end Alternating
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
