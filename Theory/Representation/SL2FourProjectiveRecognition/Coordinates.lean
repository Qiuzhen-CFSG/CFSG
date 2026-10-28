module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Coordinates from complementary root spaces for SL₂(4)

A Weyl element exchanges two complementary root spaces. Their coordinates
make every upper root a shear. The braid relation forces the unit shear
coefficient to be the identity; the diagonal word with field parameter ω
forces its coefficient to satisfy θ² = 1 + θ. These are the algebraic steps
in the field-four case of projective natural-module recognition.

Source: Aschbacher–Smith, G.1.3 and G.1.7, printed pp.327–329.
-/

@[expose] public noncomputable section
open Representation
namespace Representation.SL2FourNatural.ProjectiveRecognition
universe u
variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
variable (σ : Representation (ZMod 2) SL M) (w : SL)

structure RootPair (A : Submodule (ZMod 2) M) : Prop where
  complement : IsCompl A (A.map (σ w))
  fixed : ∀ t x, x ∈ A → σ (upper t) x = x
  moved : ∀ t x, σ (upper t) x - x ∈ A

variable {σ w} {A : Submodule (ZMod 2) M}

noncomputable def pairCoordinates (h : RootPair σ w A) : M ≃ₗ[ZMod 2] A × A :=
  (A.prodEquivOfIsCompl (A.map (σ w)) h.complement).symm.trans
    ((LinearEquiv.refl (ZMod 2) A).prodCongr
      (A.equivMapOfInjective (σ w) (fun x y he => by simpa only [σ.inv_self_apply] using congrArg (σ w⁻¹) he)).symm)

theorem pairCoordinates_symm_apply (h : RootPair σ w A) (x y : A) :
    (pairCoordinates h).symm (x,y) = (x : M) + σ w y := rfl

theorem pairCoordinates_self (h : RootPair σ w A) (x : A) :
    pairCoordinates h x = (x,0) := by
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply, pairCoordinates_symm_apply,
    ZeroMemClass.coe_zero, map_zero, add_zero]

theorem pairCoordinates_weyl (h : RootPair σ w A) (hw : w*w=1) (x : M) :
    pairCoordinates h (σ w x) = ((pairCoordinates h x).2,(pairCoordinates h x).1) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (pairCoordinates h).symm.surjective x
  simp only [LinearEquiv.apply_symm_apply]
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply,
    pairCoordinates_symm_apply, map_add]
  have hs (y : M) : σ w (σ w y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, hw, map_one, Module.End.one_apply]
  rw [hs, add_comm]

def coefficient (h : RootPair σ w A) (t : F) : Module.End (ZMod 2) A :=
  (((σ (upper t) - 1).comp (σ w)).comp A.subtype).codRestrict A
    (fun x => h.moved t (σ w x))

theorem coefficient_val (h : RootPair σ w A) (t : F) (x : A) :
    (coefficient h t x : M) = σ (upper t) (σ w x) - σ w x := rfl

theorem pairCoordinates_upper (h : RootPair σ w A) (t : F) (x : M) :
    pairCoordinates h (σ (upper t) x) =
      ((pairCoordinates h x).1 + coefficient h t (pairCoordinates h x).2,
       (pairCoordinates h x).2) := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (pairCoordinates h).symm.surjective x
  simp only [LinearEquiv.apply_symm_apply]
  apply (pairCoordinates h).symm.injective
  simp only [LinearEquiv.symm_apply_apply,
    pairCoordinates_symm_apply, map_add, Submodule.coe_add, coefficient_val, h.fixed t a a.property]
  abel

theorem coefficient_one (h : RootPair σ w A) (hw : w*w=1)
    (hbraid : upper 1 * w * upper 1 = w * upper 1 * w) : coefficient h 1 = 1 := by
  apply LinearMap.ext
  intro x
  have he := congrArg (fun g => pairCoordinates h (σ g (x : M))) hbraid
  simp only [map_mul, Module.End.mul_apply, pairCoordinates_upper,
    pairCoordinates_weyl h hw, pairCoordinates_self, map_zero, add_zero, zero_add] at he
  exact congrArg Prod.fst he

theorem coefficient_add (h : RootPair σ w A) (t s : F)
    (hadd : upper (t+s) = upper t * upper s) :
    coefficient h (t+s) = coefficient h t + coefficient h s := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.add_apply, Submodule.coe_add, coefficient_val]
  rw [hadd, map_mul, Module.End.mul_apply]
  have hf := h.fixed t _ (h.moved s (σ w x))
  simp only [map_sub] at hf
  rw [sub_eq_iff_eq_add] at hf
  rw [hf]
  abel

theorem coefficient_quadratic (h : RootPair σ w A) (hw : w*w=1)
    (hbraid : upper 1 * w * upper 1 = w * upper 1 * w)
    (hadd : upper (QuadraticAlgebra.omega + 1) =
      upper QuadraticAlgebra.omega * upper 1)
    (hdiag : ∀ x ∈ A,
      σ (upper QuadraticAlgebra.omega * w * upper (QuadraticAlgebra.omega + 1) *
        w * upper QuadraticAlgebra.omega * w) x ∈ A) :
    coefficient h QuadraticAlgebra.omega * coefficient h QuadraticAlgebra.omega =
      1 + coefficient h QuadraticAlgebra.omega := by
  apply LinearMap.ext
  intro x
  have hm := hdiag x x.property
  have he := congrArg Prod.snd (pairCoordinates_self h ⟨_, hm⟩)
  simp only [map_mul, Module.End.mul_apply, pairCoordinates_upper,
    pairCoordinates_weyl h hw, pairCoordinates_self, zero_add,
    coefficient_add h _ _ hadd, coefficient_one h hw hbraid,
    LinearMap.add_apply, Module.End.one_apply] at he
  change coefficient h QuadraticAlgebra.omega (coefficient h QuadraticAlgebra.omega x) =
    x + coefficient h QuadraticAlgebra.omega x
  have hz (y : A) : y + y = 0 := by
    simpa only [one_smul, show (1:ZMod 2)+1=0 from rfl, zero_smul] using
      (add_smul (1:ZMod 2) 1 y).symm
  have hn (y : A) : -y = y := neg_eq_of_add_eq_zero_left (hz y)
  rw [← neg_eq_iff_add_eq_zero] at he
  have he' : coefficient h QuadraticAlgebra.omega (coefficient h QuadraticAlgebra.omega x) +
      coefficient h QuadraticAlgebra.omega x = x := by
    simpa only [hn] using he.symm
  calc
    _ = x - coefficient h QuadraticAlgebra.omega x := (eq_sub_iff_add_eq).mpr he'
    _ = _ := by rw [sub_eq_add_neg, hn]

end Representation.SL2FourNatural.ProjectiveRecognition
