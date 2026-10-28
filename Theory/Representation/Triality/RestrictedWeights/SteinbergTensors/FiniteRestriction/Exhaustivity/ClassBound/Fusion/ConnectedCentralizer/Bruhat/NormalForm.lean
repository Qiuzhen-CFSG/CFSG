module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Conjugation of unique Bruhat factors

For two unipotent subgroups `U` and `V` and a normalizer subgroup `N`, a
Bruhat form consists of `u * n * v` with `u, v ∈ U`, `n ∈ N`, and
`n * v * n⁻¹ ∈ V`. A conjugation preserving `U`, `V`, and `N` preserves
this form. If multiplication is injective, a fixed product has fixed factors.

This group-theoretic step uses neither existence of forms nor connectedness.
The opposite subgroup in the right-factor condition is essential: with `V = U`
the claimed uniqueness already fails in the identity cell.

Source: Steinberg 6.3(b) and its use in 8.3(c),
`refs/KGroup/GLS3/Chapter2St2.tex`; GLS3 1.11.5 for the inversion-root convention.
-/

@[expose] public section

namespace Theory.AlgebraicGroup

variable {G : Type*} [Group G]

/-- The right factor uses the opposite unipotent subgroup: it belongs to
`U ∩ n⁻¹ V n`. The middle factor retains its entire torus component. -/
structure ToralBruhatForm (U V N : Subgroup G) where
  left : G
  middle : G
  right : G
  left_mem : left ∈ U
  middle_mem : middle ∈ N
  right_mem : right ∈ U
  opposite_mem : middle * right * middle⁻¹ ∈ V

namespace ToralBruhatForm

variable {U V N : Subgroup G}

def value (f : ToralBruhatForm U V N) : G := f.left * f.middle * f.right

/-- Conjugation preserving both unipotent subgroups preserves the actual
Bruhat form, with its conjugated middle factor. -/
def conjugate (f : ToralBruhatForm U V N) (s : G) (hs : s ∈ N)
    (hU : s ∈ Subgroup.normalizer (U : Set G)) (hV : s ∈ Subgroup.normalizer (V : Set G)) :
    ToralBruhatForm U V N where
  left := s⁻¹ * f.left * s
  middle := s⁻¹ * f.middle * s
  right := s⁻¹ * f.right * s
  left_mem := by
    have hUi : s⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).inv_mem hU
    simpa only [inv_inv] using
      ((Subgroup.mem_normalizer_iff (H := U)).mp hUi f.left).mp f.left_mem
  middle_mem := N.mul_mem (N.mul_mem (N.inv_mem hs) f.middle_mem) hs
  right_mem := by
    have hUi : s⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).inv_mem hU
    simpa only [inv_inv] using
      ((Subgroup.mem_normalizer_iff (H := U)).mp hUi f.right).mp f.right_mem
  opposite_mem := by
    have hVi : s⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).inv_mem hV
    have h := ((Subgroup.mem_normalizer_iff (H := V)).mp
      hVi (f.middle * f.right * f.middle⁻¹)).mp f.opposite_mem
    convert h using 1
    group

theorem value_conjugate (f : ToralBruhatForm U V N) (s : G) (hs : s ∈ N)
    (hU : s ∈ Subgroup.normalizer (U : Set G)) (hV : s ∈ Subgroup.normalizer (V : Set G)) :
    (f.conjugate s hs hU hV).value = s⁻¹ * f.value * s := by
  dsimp [value, conjugate]
  group

private theorem centralizes_of_conj_eq (s x : G) (h : s⁻¹ * x * s = x) :
    x ∈ Subgroup.centralizer {s} := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    x * s = s * (s⁻¹ * x * s) := by group
    _ = s * x := congrArg (s * ·) h

/-- Uniqueness forces every factor of a centralizing element to centralize.
This does not require surjectivity of the Bruhat parametrization. -/
theorem factors_centralize
    (hinj : Function.Injective (value (U := U) (V := V) (N := N)))
    (f : ToralBruhatForm U V N) (s : G) (hs : s ∈ N)
    (hU : s ∈ Subgroup.normalizer (U : Set G)) (hV : s ∈ Subgroup.normalizer (V : Set G))
    (hf : f.value ∈ Subgroup.centralizer {s}) :
    f.left ∈ Subgroup.centralizer {s} ∧
      f.middle ∈ Subgroup.centralizer {s} ∧
      f.right ∈ Subgroup.centralizer {s} := by
  have h : f.conjugate s hs hU hV = f := by
    apply hinj
    rw [value_conjugate, mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp hf]
    group
  exact ⟨centralizes_of_conj_eq s f.left (congrArg left h),
    centralizes_of_conj_eq s f.middle (congrArg middle h),
    centralizes_of_conj_eq s f.right (congrArg right h)⟩

end ToralBruhatForm
end Theory.AlgebraicGroup
