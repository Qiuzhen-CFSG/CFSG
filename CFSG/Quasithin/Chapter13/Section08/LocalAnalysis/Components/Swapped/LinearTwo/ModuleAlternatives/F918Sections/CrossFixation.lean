module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FactorSpaces

/-!
# Cross-factor fixation under the actual exchange operator

F.9.18(5iii) gives [I_H,K] = C_{I_H}(K^t). Its fixation conclusion for
one canonical factor space transfers to the other using the operator
induced by the moving element. The same operator exchanges the canonical
commutator spaces. Their sum is the whole commutator-generated module;
no direct sum before taking a central quotient is asserted.

The classification still has to supply the first centralizer identity and
its natural-module identification. The lemmas here only perform the marked
linear transport, so they also apply before that classification is proved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.18(5iii), printed p.325, and 13.8.16(1), p.952.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- An intertwiner carries vectors fixed by A to vectors fixed by the
specified image of A under the same group automorphism. -/
theorem fixedSpace_map_automorphism_le (α : D ≃* D) (s : V ≃ₗ[ZMod 2] V)
    (hs : ∀ g v, s (ρ g v) = ρ (α g) (s v)) (A : Subgroup D) :
    (fixedSpace ρ A).map s.toLinearMap ≤ fixedSpace ρ (A.map α.toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ ⟨_, a, ha, rfl⟩
  change ρ (α a) (s v) = s v
  exact (hs a v).symm.trans (congrArg s (hv ⟨a, ha⟩))

/-- The single centralizer equality in F.9.18(5iii) yields fixation in
both directions for the literal canonical factor spaces. -/
theorem canonical_cross_fixation (A B : Subgroup D)
    (α : D ≃* D) (s : V ≃ₗ[ZMod 2] V)
    (hs : ∀ g v, s (ρ g v) = ρ (α g) (s v))
    (hAB : A.map α.toMonoidHom = B) (hBA : B.map α.toMonoidHom = A)
    (hfirst : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B) :
    subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A := by
  refine ⟨hfirst, ?_⟩
  have he := moved_map_automorphism ρ α s hs A
  rw [hAB] at he
  rw [← he]
  have hf := fixedSpace_map_automorphism_le ρ α s hs B
  rw [hBA] at hf
  exact (Submodule.map_mono hfirst).trans hf

/-- Canonical sum, exchange, and both fixation assertions use a single
intertwiner. The source natural/orthogonal central-section data is retained
separately by the classification owner. -/
theorem canonical_factor_sum_of_centralizer_identity (A B : Subgroup D)
    [A.Normal] [B.Normal] (hgen : A ⊔ B = ⊤)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (α : D ≃* D) (s : V ≃ₗ[ZMod 2] V)
    (hs : ∀ g v, s (ρ g v) = ρ (α g) (s v))
    (hAB : A.map α.toMonoidHom = B) (hBA : B.map α.toMonoidHom = A)
    (hfirst : subspaceCommutator ρ ⊤ A = fixedSpace ρ B) :
    subspaceCommutator ρ ⊤ A ⊔ subspaceCommutator ρ ⊤ B = ⊤ ∧
      (subspaceCommutator ρ ⊤ A).map s.toLinearMap = subspaceCommutator ρ ⊤ B ∧
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A := by
  refine ⟨factor_spaces_sum ρ A B hgen hfull, ?_,
    canonical_cross_fixation ρ A B α s hs hAB hBA hfirst.le⟩
  rw [moved_map_automorphism ρ α s hs A, hAB]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
