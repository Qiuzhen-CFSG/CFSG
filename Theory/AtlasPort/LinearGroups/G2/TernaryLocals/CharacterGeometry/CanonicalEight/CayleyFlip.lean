module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyProducts
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyFlip.Table

/-!
# The first-generator sign automorphism of a Cayley frame

An independent orthogonal frame `(1,a,b,ab,c,ac,bc,(ab)c)` is a basis of
the actual ternary split octonions. Negating its odd-indexed vectors defines
an involutive linear equivalence. The concrete Cayley multiplication rules
proved in `CayleyFlip.Table` show that this equivalence preserves octonion
multiplication, so it belongs to `Atlas.G2.Model (ZMod 3)`.

`exists_cayley_frame_flip` supplies precisely the automorphism required by
`extension_of_cayley_frame_flip`. Constructing the frame and applying that
extension remain with the canonical-eight assembly. This module does not
assert the unconditional four-group extension or the classification theorem.

Coordinate conventions: the ATLAS split-octonion port, Copyright (c) 2026
Gerald Höhn and the ATLAS contributors, under the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 (Theorem 0.1.1 on pp.481–482).
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight

noncomputable def cayleyFlipBasis (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) :
    Module.Basis (Fin 8) (ZMod 3) V :=
  Module.Basis.mk hlin (by rw [cayleyProducts_span a b c hlin])

@[simp] theorem cayleyFlipBasis_apply (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) (i : Fin 8) :
    cayleyFlipBasis a b c hlin i = cayleyProducts a b c i :=
  Module.Basis.mk_apply _ _ i

noncomputable def cayleyFlipLinear (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) : V →ₗ[ZMod 3] V :=
  (cayleyFlipBasis a b c hlin).constr (ZMod 3)
    (fun i => firstSign i • cayleyProducts a b c i)

@[simp] theorem cayleyFlipLinear_apply (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) (i : Fin 8) :
    cayleyFlipLinear a b c hlin (cayleyProducts a b c i) =
      firstSign i • cayleyProducts a b c i := by
  simpa only [cayleyFlipLinear, cayleyFlipBasis_apply] using
    (cayleyFlipBasis a b c hlin).constr_basis (ZMod 3)
      (fun k => firstSign k • cayleyProducts a b c k) i

theorem firstSign_mul_self (i : Fin 8) : firstSign i * firstSign i = 1 := by
  rcases firstSign_cases i with h | h <;> rw [h] <;> ring

theorem cayleyFlipLinear_involutive (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) :
    Function.Involutive (cayleyFlipLinear a b c hlin) := by
  have h : (cayleyFlipLinear a b c hlin).comp (cayleyFlipLinear a b c hlin) =
      LinearMap.id := by
    apply (cayleyFlipBasis a b c hlin).ext
    intro i
    simp only [LinearMap.comp_apply, LinearMap.id_apply, cayleyFlipBasis_apply,
      cayleyFlipLinear_apply, map_smul, smul_smul, firstSign_mul_self, one_smul]
  intro x
  exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) h

noncomputable def cayleyFlipEquiv (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) : V ≃ₗ[ZMod 3] V where
  toLinearMap := cayleyFlipLinear a b c hlin
  invFun := cayleyFlipLinear a b c hlin
  left_inv := cayleyFlipLinear_involutive a b c hlin
  right_inv := cayleyFlipLinear_involutive a b c hlin

@[simp] theorem cayleyFlipEquiv_apply (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c)) (i : Fin 8) :
    cayleyFlipEquiv a b c hlin (cayleyProducts a b c i) =
      firstSign i • cayleyProducts a b c i :=
  cayleyFlipLinear_apply a b c hlin i

theorem cayleyFlipEquiv_mul (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0) (x y : V) :
    cayleyFlipEquiv a b c hlin (mul x y) =
      mul (cayleyFlipEquiv a b c hlin x) (cayleyFlipEquiv a b c hlin y) := by
  have he : multiplication.compr₂ (cayleyFlipEquiv a b c hlin).toLinearMap =
      multiplication.compl₁₂ (cayleyFlipEquiv a b c hlin).toLinearMap
        (cayleyFlipEquiv a b c hlin).toLinearMap := by
    apply (cayleyFlipBasis a b c hlin).ext
    intro i
    apply (cayleyFlipBasis a b c hlin).ext
    intro j
    change cayleyFlipEquiv a b c hlin (mul (cayleyFlipBasis a b c hlin i)
      (cayleyFlipBasis a b c hlin j)) =
      mul (cayleyFlipEquiv a b c hlin (cayleyFlipBasis a b c hlin i))
        (cayleyFlipEquiv a b c hlin (cayleyFlipBasis a b c hlin j))
    simp only [cayleyFlipBasis_apply]
    obtain ⟨r, hr⟩ := cayleyProducts_mul_line a b c ho i j
    rw [hr, map_smul, cayleyFlipEquiv_apply, cayleyFlipEquiv_apply,
      cayleyFlipEquiv_apply, smul_mul, SplitOctonion.mul_smul, hr]
    simp only [smul_smul, firstSign_flipIndex]
    congr 1
    ring
  exact congrArg (fun f : V →ₗ[ZMod 3] V →ₗ[ZMod 3] V => f x y) he

/-- The first-generator sign change as an actual octonion automorphism. -/
noncomputable def cayleyFlip (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0) : Atlas.G2.Model (ZMod 3) :=
  ⟨cayleyFlipEquiv a b c hlin, cayleyFlipEquiv_mul a b c hlin ho⟩

@[simp] theorem cayleyFlip_apply (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0) (i : Fin 8) :
    (cayleyFlip a b c hlin ho).val (cayleyProducts a b c i) =
      firstSign i • cayleyProducts a b c i :=
  cayleyFlipEquiv_apply a b c hlin i

/-- Every independent orthogonal Cayley frame with nonzero axis norms admits
its first-generator sign change. The construction in fact needs only
independence and orthogonality; the extra norm premise matches the frame
supplied by the canonical-eight assembly. -/
theorem exists_cayley_frame_flip (a b c : V)
    (hlin : LinearIndependent (ZMod 3) (cayleyProducts a b c))
    (_hnorm : ∀ i, norm (cayleyProducts a b c i) ≠ 0)
    (ho : ∀ i j, i ≠ j → normPolar (cayleyProducts a b c i)
      (cayleyProducts a b c j) = 0) :
    ∃ g : Atlas.G2.Model (ZMod 3), ∀ i,
      g.val (cayleyProducts a b c i) = firstSign i • cayleyProducts a b c i :=
  ⟨cayleyFlip a b c hlin ho, cayleyFlip_apply a b c hlin ho⟩

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
