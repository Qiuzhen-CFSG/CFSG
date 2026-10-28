module
public import Theory.Representation.BinaryParabolicExteriorSquare.Simplicity
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Singular lines present the binary exterior six-space

Split a bivector into its first and last three coordinates. Both halves
are totally singular, so the three-point singular line relations express
every singular vector in the six coordinate points. Thus a map on singular
vectors respecting these relations extends uniquely to a linear map.
Covariance extends on the coordinate basis; simplicity of the exterior
action makes every nonzero such intertwiner injective.

This supplies the presentation step in the B.4.13 recognition used by
Aschbacher--Smith, The Classification of Quasithin Groups, 13.8.29(5),
printed p.964. It requires neither an assumed presentation kernel nor
an enumeration of pairs of singular points. The exterior model retains
the ATLAS attribution and license of its imported construction.
-/

@[expose] public noncomputable section
open Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.SingularPresentation
open Representation.BinaryParabolicExteriorSquare
variable {W : Type*} [AddCommGroup W] [Module Bit W]

noncomputable def extension (f : Six → W) : Six →ₗ[Bit] W :=
  ∑ i : Fin 6, (LinearMap.proj i).smulRight (f (Pi.single i 1))

theorem extension_apply (f : Six → W) (x : Six) :
    extension f x = ∑ i : Fin 6, x i • f (Pi.single i 1) := by
  simp [extension]

private theorem scalar_value (f : Six → W) (hzero : f 0 = 0)
    (c : Bit) (v : Six) : f (c • v) = c • f v := by
  rcases (by decide : ∀ c : Bit, c = 0 ∨ c = 1) c with rfl | rfl <;> simp [hzero]

/-- Singular line relations present the actual exterior six-space. -/
theorem extension_singular (f : Six → W) (hzero : f 0 = 0)
    (hline : ∀ u v : Six, pfaffian u = 0 → pfaffian v = 0 →
      pfaffian (u + v) = 0 → f (u + v) = f u + f v)
    (x : Six) (hx : pfaffian x = 0) : extension f x = f x := by
  let a : Six := ![x 0,x 1,x 2,0,0,0]
  let b : Six := ![0,0,0,x 3,x 4,x 5]
  have hab : a + b = x := by ext i; fin_cases i <;> simp [a,b]
  have ha : pfaffian a = 0 := by simp [a]
  have hb : pfaffian b = 0 := by simp [b]
  have hsum := hline a b ha hb (by rwa [hab])
  rw [hab] at hsum
  have hfirst : f a = x 0 • f (Pi.single 0 1) + x 1 • f (Pi.single 1 1) +
      x 2 • f (Pi.single 2 1) := by
    have he : a = (x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 : Six) +
        x 2 • Pi.single 2 1 := by ext i; fin_cases i <;> simp [a]
    rw [he,hline,hline,scalar_value f hzero,scalar_value f hzero,scalar_value f hzero]
    all_goals simp [pfaffian_apply]
  have hsecond : f b = x 3 • f (Pi.single 3 1) + x 4 • f (Pi.single 4 1) +
      x 5 • f (Pi.single 5 1) := by
    have he : b = (x 3 • Pi.single 3 1 + x 4 • Pi.single 4 1 : Six) +
        x 5 • Pi.single 5 1 := by ext i; fin_cases i <;> simp [b]
    rw [he,hline,hline,scalar_value f hzero,scalar_value f hzero,scalar_value f hzero]
    all_goals simp [pfaffian_apply]
  rw [extension_apply,hsum,hfirst,hsecond]
  simp [Fin.sum_univ_succ, add_assoc]

/-- The extension is uniquely determined by its singular values. -/
theorem extension_unique (f : Six → W) (F : Six →ₗ[Bit] W)
    (hF : ∀ x, pfaffian x = 0 → F x = f x) : F = extension f := by
  apply (Pi.basisFun Bit (Fin 6)).ext
  intro i
  simp only [Pi.basisFun_apply]
  rw [extension_apply]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  apply hF
  fin_cases i <;> simp

variable {J : Type*} [Group J]

/-- The exterior action retains the supplied natural four-space marking. -/
noncomputable def action (π : J →* SL(4,Bit)) : Representation Bit J Six where
  toFun g := exteriorMap (π g).val
  map_one' := by rw [map_one,Matrix.SpecialLinearGroup.coe_one,exteriorMap_one]; rfl
  map_mul' g h := by rw [map_mul,Matrix.SpecialLinearGroup.coe_mul,exteriorMap_mul]; rfl

/-- Singular covariance extends to covariance on the whole six-space. -/
theorem extension_equivariant
    (π : J →* SL(4,Bit)) (ρ : Representation Bit J W)
    (f : Six → W) (hzero : f 0 = 0)
    (hline : ∀ u v : Six, pfaffian u = 0 → pfaffian v = 0 →
      pfaffian (u + v) = 0 → f (u + v) = f u + f v)
    (hcov : ∀ g x, pfaffian x = 0 → f (exteriorMap (π g).val x) = ρ g (f x))
    (g : J) (x : Six) :
    extension f (exteriorMap (π g).val x) = ρ g (extension f x) := by
  have he : (extension f).comp (exteriorMap (π g).val) = (ρ g).comp (extension f) := by
    apply (Pi.basisFun Bit (Fin 6)).ext
    intro i
    simp only [Pi.basisFun_apply,LinearMap.comp_apply]
    have hi : pfaffian (Pi.single i (1:Bit)) = 0 := by fin_cases i <;> simp
    rw [extension_singular f hzero hline _ (by rw [pfaffian_exteriorMap,hi,mul_zero]),
      extension_singular f hzero hline _ hi,hcov g _ hi]
  exact LinearMap.congr_fun he x

/-- Nonzero singular data yield an injective marked exterior intertwiner.
No dimension or simplicity hypothesis is imposed on the target. -/
theorem exists_injective_intertwiner
    (π : J →* SL(4,Bit)) (hπ : Function.Surjective π)
    (ρ : Representation Bit J W) (f : Six → W) (hzero : f 0 = 0)
    (hline : ∀ u v : Six, pfaffian u = 0 → pfaffian v = 0 →
      pfaffian (u + v) = 0 → f (u + v) = f u + f v)
    (hcov : ∀ g x, pfaffian x = 0 → f (exteriorMap (π g).val x) = ρ g (f x))
    (hne : ∃ x : Six, pfaffian x = 0 ∧ f x ≠ 0) :
    ∃ F : (action π).IntertwiningMap ρ, Function.Injective F ∧
      ∀ x, pfaffian x = 0 → F x = f x := by
  let F : (action π).IntertwiningMap ρ := {
    toLinearMap := extension f
    isIntertwining' := fun g => LinearMap.ext (extension_equivariant π ρ f hzero hline hcov g) }
  refine ⟨F,?_,extension_singular f hzero hline⟩
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  have ht : (extension f).ker = ⊤ := by
    apply six_simple _ _ hk
    intro g x hx
    obtain ⟨j,rfl⟩ := hπ g
    change extension f (exteriorMap (π j).val x) = 0
    rw [extension_equivariant π ρ f hzero hline hcov,show extension f x = 0 from hx,map_zero]
  obtain ⟨x,hx,hfx⟩ := hne
  apply hfx
  rw [←extension_singular f hzero hline x hx]
  exact (show x ∈ (extension f).ker by rw [ht]; trivial)

end Representation.BinaryParabolicExteriorSquare.SingularPresentation
