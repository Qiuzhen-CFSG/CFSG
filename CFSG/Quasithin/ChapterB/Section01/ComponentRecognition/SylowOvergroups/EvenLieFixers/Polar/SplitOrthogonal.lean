module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.LowRank
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar.SplitOrthogonal.LocalReduction

/-!
# Local assembly for the split orthogonal Sylow fixer

Two geometric inputs suffice on the actual scalar quotient of the elementary
Siegel-generated group: the proper Sylow-overgroup Fitting bound and two
proper overgroups of each Sylow subgroup that generate the whole group.
The local-normalizer argument bounds the full automorphism fixer, including
diagram automorphisms, uniformly for ranks at least three and the binary field.
Simplicity and perfectness are transported from the given simple group.

This module supplies conditional assembly and its application to the literal
component central quotient in B.1.13. It does not assert the unconditional
split orthogonal fixer theorem: both local inputs must still be discharged.
The proper-overgroup input has its existing independent producer; the separate
generating-overgroup construction needs no automorphism classification.

Source: Aschbacher–Smith B.1.13, printed pp.73–74 of `refs/quasithin.pdf`;
GLS3 §§2.6–2.7 for Sylow overgroups and classical carrier conventions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar

section Assembly
variable
    (hbound : ∀ (F : Type) [Field F] [Finite F] (r f : ℕ)
      [IsSimpleGroup (ClassicalOrthogonal.POmegaPlus r F)]
      [Group.IsPerfect (ClassicalOrthogonal.POmegaPlus r F)],
      3 ≤ r → 0 < f → Nat.card F = 2 ^ f →
      ProperSylowFittingBound (ClassicalOrthogonal.POmegaPlus r F))
    (hpair : ∀ (F : Type) [Field F] [Finite F] (r f : ℕ)
      [IsSimpleGroup (ClassicalOrthogonal.POmegaPlus r F)]
      [Group.IsPerfect (ClassicalOrthogonal.POmegaPlus r F)],
      3 ≤ r → 0 < f → Nat.card F = 2 ^ f →
      ∀ S : Sylow 2 (ClassicalOrthogonal.POmegaPlus r F),
      ∃ P R : Subgroup (ClassicalOrthogonal.POmegaPlus r F),
        (S : Subgroup _) ≤ P ∧ (S : Subgroup _) ≤ R ∧
        P ≠ ⊤ ∧ R ≠ ⊤ ∧ P ⊔ R = ⊤)

include hbound hpair

/-- The concrete local inputs, once proved, give the full fixer of every
split orthogonal model. The inputs contain no automorphism-fixer assertion. -/
theorem splitOrthogonal_model_fixer_of_local_data
    {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] [Group.IsPerfect X]
    {r f : ℕ} (hr : 3 ≤ r) (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPOmegaPlus X r (2 ^ f)) : SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup (ClassicalOrthogonal.POmegaPlus r F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (ClassicalOrthogonal.POmegaPlus r F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact fixer_of_equiv e (fixer_of_properSylowFittingBound_of_generating_pairs
    (hbound F r f hr hf hF) (hpair F r f hr hf hF))

/-- Conditional local assembly discharges B.1.13's fixer premise on the
literal component quotient. The independent local dichotomy remains explicit. -/
theorem splitOrthogonal_le_component_of_local_data
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)
    {r f : ℕ} (hr : 3 ≤ r) (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPOmegaPlus (L ⧸ center L) r (2 ^ f)) : K ≤ L := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (splitOrthogonal_model_fixer_of_local_data hbound hpair hr hf hmodel) hd

end Assembly
end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers.Polar
