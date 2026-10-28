module

public import Theory.Representation.G2BinaryPointMovement
public import Theory.Representation.G2NaturalOffenders

/-!
# The four-group actor in the marked G₂ point parabolic

Relative normalization by the derived point parabolic puts a nontrivial
elementary actor over the long-root four-group. Rank less than three forces
it to equal that four-group. Its displacement on the literal natural module
is the marked three-space. A surjective equivariant projection transfers
this lower bound to the original module, including a central Weyl cover.

Source: Aschbacher–Smith, 13.8.27, printed p.963, and B.4.6(3).
The finite root calculations used here retain the attribution of the
ATLAS port in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
open Atlas.G2

/-- Normality is required only in the derived point parabolic. -/
theorem point_actor_eq_natural
    (A : Subgroup (Model (ZMod 2))) [IsElementaryAbelian 2 A]
    (hA : A ≤ unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A : Set _))
    (hne : A ≠ ⊥) (hr : rank A < 3) :
    A = BinaryCore.natural ∧ rank A = 2 := by
  have hAB := Natural.BinaryPointFlag.natural_le_normalized_elementary A hA hn hne
  have hcard := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAB)
  rw [BinaryCore.card_natural] at hcard
  have hl := Nat.log_mono_right (b := 2) hcard
  change 2 ≤ rank A at hl
  have heq : rank A = 2 := by omega
  refine ⟨(Subgroup.eq_of_le_of_card_ge hAB ?_).symm, heq⟩
  rw [BinaryCore.card_natural, (show IsElementaryTwo A from ⟨hne, inferInstance⟩).card_eq_two_pow_rank]
  rw [heq]
  decide

/-- The literal natural action has a three-dimensional displacement. -/
theorem point_actor_displacement
    (A : Subgroup (Model (ZMod 2))) [IsElementaryAbelian 2 A]
    (hA : A ≤ unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A : Set _))
    (hne : A ≠ ⊥) :
    Module.finrank (ZMod 2)
      (subspaceCommutator (Restricted.NaturalCoordinates.action (ZMod 2)) ⊤ A) = 3 := by
  rw [Natural.BinaryPointFlag.normal_elementary_displacement_eq_seed A hA hn hne]
  have hs : Natural.BinaryPointFlag.seed = NaturalOffenders.upper (F := ZMod 2) := by
    ext v
    exact Natural.BinaryPointFlag.mem_seed v
  rw [hs]
  exact NaturalOffenders.upper_finrank

variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A compatible natural projection transfers the point-parabolic displacement
bound to the original module; no marking on a different module is used. -/
theorem displacement_ge_three_of_natural_projection
    (ρ : Representation (ZMod 2) J W)
    (f : J →* Model (ZMod 2))
    (p : W →ₗ[ZMod 2] Natural.Space (ZMod 2)) (hp : Function.Surjective p)
    (he : ∀ a v, p (ρ a v) = Natural.action (ZMod 2) (f a) (p v))
    (A : Subgroup J) [IsElementaryAbelian 2 A]
    (hA : A.map f ≤ unipotent)
    (hn : BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A.map f : Set _))
    (hne : A.map f ≠ ⊥) :
    3 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  let τ := Restricted.NaturalCoordinates.action (ZMod 2)
  let E := Restricted.NaturalCoordinates.equiv (ZMod 2)
  let q := E.toLinearMap.comp p
  have hq : Function.Surjective q := E.surjective.comp hp
  have heq (a : J) (v : W) : q (ρ a v) = τ (f a) (q v) := by
    change E (p (ρ a v)) = τ (f a) (E (p v))
    rw [he]
    exact LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining' (f a)) (p v)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hm : subspaceCommutator τ ⊤ (A.map f) ≤ (subspaceCommutator ρ ⊤ A).map q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, rfl⟩, v, _, rfl⟩
    obtain ⟨w, rfl⟩ := hq v
    refine ⟨ρ a w - w, Submodule.subset_span ⟨a, ha, w, Submodule.mem_top, rfl⟩, ?_⟩
    rw [map_sub, heq]
  have hdim := (Submodule.finrank_mono hm).trans (Submodule.finrank_map_le _ _)
  rw [point_actor_displacement (A.map f) hA hn hne] at hdim
  exact hdim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Parabolic
end
