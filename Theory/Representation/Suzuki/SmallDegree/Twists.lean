module

public import Theory.Representation.Suzuki.NaturalMatrix
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Removing automorphism twists from the binary Suzuki natural module

A defining-field automorphism acts coordinatewise and is linear over F₂.
An inner automorphism is implemented by multiplication by its defining matrix.
Their composite gives the actual intertwiner for every inner–field twist.
The proved inner–field coverage then removes any automorphism of Sz(2^(2m+1)),
including Sz(8), without changing the marking of the original representation.

Sources: GLS3, Theorem 2.5.12(b–f); Guralnick–Malle, *Classification of
2F-modules, II*, §3.1 and Lemma 8.3; Aschbacher–Smith, printed p.457.
-/

@[expose] public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- Apply a defining-field automorphism to each of the four coordinates. -/
def fieldCoordinates (m : ℕ) (s : F m ≃ₐ[ZMod 2] F m) :
    W m ≃ₗ[ZMod 2] W m := LinearEquiv.piCongrRight (fun _ => s.toLinearEquiv)

@[simp] theorem fieldCoordinates_apply (m : ℕ) (s : F m ≃ₐ[ZMod 2] F m)
    (v : W m) (i : Fin 4) : fieldCoordinates m s v i = s (v i) := rfl

/-- The same field map acts on matrix entries and on vector coordinates. -/
theorem fieldCoordinates_intertwines (m : ℕ) (s : F m ≃ₐ[ZMod 2] F m)
    (g : SuzukiMatrixGroup m) (v : W m) :
    fieldCoordinates m s (natural m g v) =
      natural m (suzukiFieldAut m s g) (fieldCoordinates m s v) := by
  ext i
  simp [fieldCoordinates, natural_apply, Matrix.mulVec, dotProduct,
    suzukiFieldAut_apply_entry, map_sum, map_mul]

/-- Multiplication by a Suzuki matrix, viewed as a binary linear equivalence. -/
def matrixCoordinates (m : ℕ) (g : SuzukiMatrixGroup m) : W m ≃ₗ[ZMod 2] W m where
  toLinearMap := natural m g
  invFun := natural m g⁻¹
  left_inv v := by
    change natural m g⁻¹ (natural m g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change natural m g (natural m g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[simp] theorem matrixCoordinates_apply (m : ℕ) (g : SuzukiMatrixGroup m) (v : W m) :
    matrixCoordinates m g v = natural m g v := rfl

/-- Explicit coordinates implement an inner–field automorphism on the natural action. -/
def innerFieldEquiv (m : ℕ) (g : SuzukiMatrixGroup m) (s : F m ≃ₐ[ZMod 2] F m) :
    (natural m).Equiv
      ((natural m).comp (MulAut.conj g * suzukiFieldAut m s).toMonoidHom) := by
  refine .mk ((fieldCoordinates m s).trans (matrixCoordinates m g)) ?_
  intro x
  apply LinearMap.ext
  intro v
  change natural m g (fieldCoordinates m s (natural m x v)) =
    natural m ((MulAut.conj g * suzukiFieldAut m s) x)
      (natural m g (fieldCoordinates m s v))
  rw [fieldCoordinates_intertwines]
  change natural m g (natural m (suzukiFieldAut m s x) _) =
    natural m (g * suzukiFieldAut m s x * g⁻¹) (natural m g _)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- Every automorphism twist of the natural module is binary-equivalent to it. -/
theorem natural_comp_aut_equiv {m : ℕ} (hm : 1 ≤ m)
    (a : MulAut (SuzukiMatrixGroup m)) :
    Nonempty (Representation.Equiv ((natural m).comp a.toMonoidHom) (natural m)) := by
  obtain ⟨g, s, rfl⟩ := suzukiAut_eq_inner_mul_field m hm a
  exact ⟨(innerFieldEquiv m g s).symm⟩

/-- Recognition up to an actor automorphism gives the originally marked module.
This discharges the automorphism-twist clause in small-degree recognition. -/
theorem equiv_of_aut_twist {m : ℕ} (hm : 1 ≤ m)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (a : MulAut (SuzukiMatrixGroup m))
    (e : ρ.Equiv ((natural m).comp a.toMonoidHom)) :
    Nonempty (ρ.Equiv (natural m)) := by
  obtain ⟨f⟩ := natural_comp_aut_equiv hm a
  exact ⟨e.trans f⟩

end Representation.SuzukiSmallDegree
