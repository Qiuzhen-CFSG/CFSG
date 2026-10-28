module
public import Theory.Representation.InvertedCubicTensor.NaturalFactors
public import Mathlib.Tactic

/-!
# Nondegeneracy of a cubic pairing between natural binary planes

A cubic-equivariant biadditive map from two natural planes to a fixed-free
binary module either vanishes everywhere or is nonzero on every pair of
nonzero vectors. If one value vanishes, its two cubic translates vanish;
the binary sum identities make the two remaining cross values equal and
cubic-fixed. This gives the cross-commutator step in 14.3.18(4), p.996.
-/

public section
namespace InvertedCubicTensor
private instance : Fintype NaturalPlane :=
  @Subtype.fintype _ _
    (fun x => inferInstanceAs (Decidable (∑ i : Fin 3, x i = 0)))
    (inferInstance : Fintype (Fin 3 → ZMod 2))
local notation "C" => BinaryPermutation.coreRepresentation (Fin 3) cubic
private theorem cubic_square (u : NaturalPlane) : C (C u)=u+C u := by
  have ht : ∀ u : NaturalPlane, C (C u)=u+C u := by decide +kernel
  exact ht u
private theorem plane_cases (u : NaturalPlane) (hu : u≠0) (v : NaturalPlane) :
    v=0 ∨ v=u ∨ v=C u ∨ v=u+C u := by
  have ht : ∀ u : NaturalPlane, u≠0 → ∀ v : NaturalPlane,
      v=0 ∨ v=u ∨ v=C u ∨ v=u+C u := by decide +kernel
  exact ht u hu v

/-- A cubic-equivariant biadditive pairing with fixed-free target has no
zero value on nonzero vectors unless the entire pairing vanishes. -/
theorem natural_cubic_pairing_zero_of_zero
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (b : NaturalPlane → NaturalPlane → Z) (α : Z → Z)
    (hleft : ∀ x y z, b (x+y) z=b x z+b y z)
    (hright : ∀ x y z, b x (y+z)=b x y+b x z)
    (hzero : (∀ x, b 0 x=0) ∧ (∀ x, b x 0=0))
    (hαzero : α 0=0) (hfree : ∀z,α z=z→z=0)
    (heq : ∀x y,b (C x) (C y)=α (b x y))
    (u v : NaturalPlane) (hu : u≠0) (hv : v≠0) (h : b u v=0) :
    ∀x y,b x y=0 := by
  have h11 : b (C u) (C v)=0 := by rw [heq,h,hαzero]
  have h22 : b (C (C u)) (C (C v))=0 := by rw [heq,h11,hαzero]
  have hsum : b u (C v)+b (C u) v=0 := by
    rw [cubic_square,cubic_square,hleft,hright,hright,h,h11] at h22
    simpa using h22
  have htwo (z : Z) : z+z=0 := by
    have hh := (show (2:ZMod 2) • z=0 by rw [show (2:ZMod 2)=0 by decide,zero_smul])
    simpa [two_smul] using hh
  have hcross : b u (C v)=b (C u) v := by
    calc
      b u (C v) = b u (C v)+(b (C u) v+b (C u) v) := by rw [htwo,add_zero]
      _ = (b u (C v)+b (C u) v)+b (C u) v := by rw [add_assoc]
      _ = b (C u) v := by rw [hsum,zero_add]
  have hfixed : α (b u (C v))=b u (C v) := by
    rw [←heq,cubic_square,hright,h11,add_zero,hcross]
  have h01 : b u (C v)=0 := hfree _ hfixed
  have h10 : b (C u) v=0 := hcross ▸ h01
  intro x y
  rcases plane_cases u hu x with rfl | rfl | rfl | rfl <;>
    rcases plane_cases v hv y with rfl | rfl | rfl | rfl <;>
    simp only [hzero.1,hzero.2,hleft,hright,h,h11,h01,h10,add_zero]
end InvertedCubicTensor
