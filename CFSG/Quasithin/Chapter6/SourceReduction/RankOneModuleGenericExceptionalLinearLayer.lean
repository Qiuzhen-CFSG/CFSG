module
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.GroupTheory.PGroup.OmegaCentralizerDetection
public import Mathlib.LinearAlgebra.Pi

/-!
# Whole-layer interfaces for the field-four exceptional branch

The centralizer test applies to any elementary subgroup normalized by the
ambient Sylow group. A nontrivial fixed subgroup would meet its center and
produce a point in C_{Ω₁(Z(T))}(L). The second interface retains an actual
common quotient marking on an arbitrary finite number of orthogonal A₅
copies. A positive multiplicity at most two gives the required source model.

These are preparation and transport results, not the decomposition or its
numerical bound. Source: Aschbacher--Smith 5.1.3 and 5.1.14(3--4), printed
pp.630--631,638--639, and the field-four step of 5.1.19, pp.643--644.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

/-- Pointwise action on k copies; every coordinate has the same A₅ actor. -/
def a5Copies (k : ℕ) : Representation (ZMod 2) (alternatingGroup (Fin 5))
    (Fin k → BinaryPermutation.natural (Fin 5)) where
  toFun g := {
    toFun v i := a5Module g (v i)
    map_add' v w := by funext i; exact map_add (a5Module g) (v i) (w i)
    map_smul' c v := by funext i; exact (a5Module g).map_smul c (v i) }
  map_one' := by apply LinearMap.ext; intro v; funext i; exact DFunLike.congr_fun a5Module.map_one (v i)
  map_mul' g h := by apply LinearMap.ext; intro v; funext i; exact DFunLike.congr_fun (a5Module.map_mul g h) (v i)

@[simp] theorem a5Copies_apply (k : ℕ) (g : alternatingGroup (Fin 5))
    (v : Fin k → BinaryPermutation.natural (Fin 5)) (i : Fin k) :
    a5Copies k g v i = a5Module g (v i) := rfl

/-- Change vector coordinates while retaining the literal L/O₂(L) marking. -/
theorem IsConjugationModel.of_linearEquiv
    {L W : Subgroup G} {A X Y : Type*} [Group A]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) A X} {σ : Representation (ZMod 2) A Y}
    (hm : IsConjugationModel L W ρ) (c : X ≃ₗ[ZMod 2] Y)
    (hc : ∀ g x, c (ρ g x) = σ g (c x)) : IsConjugationModel L W σ := by
  obtain ⟨e, f, hf⟩ := hm
  refine ⟨e, f.trans c.toAddEquiv.toMultiplicative, ?_⟩
  intro l w
  change ((f.symm (Multiplicative.ofAdd
    (c.symm (σ (e (QuotientGroup.mk' (pCore 2 L) l)) (c (f w).toAdd))))) : G) = _
  rw [← hc, c.symm_apply_apply]
  exact hf l w

/-- A positive number of copies bounded by two is precisely the required
one-or-two-module conclusion, with a single common quotient marking. -/
theorem oneOrTwoA5Modules_of_copies {L W : Subgroup G} {k : ℕ}
    (hk : 0 < k) (hk2 : k ≤ 2) (hm : IsConjugationModel L W (a5Copies k)) :
    IsOneOrTwoA5Modules L W := by
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · let c : (Fin 1 → BinaryPermutation.natural (Fin 5)) ≃ₗ[ZMod 2]
        BinaryPermutation.natural (Fin 5) := {
      toFun v := v 0
      invFun v := fun _ => v
      left_inv v := by funext i; exact congrArg v (Subsingleton.elim _ _)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    exact Or.inl (hm.of_linearEquiv c (fun _ _ => rfl))
  · exact Or.inr (hm.of_linearEquiv
      (LinearEquiv.finTwoArrow (ZMod 2) (BinaryPermutation.natural (Fin 5)))
      (fun _ _ => rfl))

end CFSG.Quasithin.Chapter6.Source
