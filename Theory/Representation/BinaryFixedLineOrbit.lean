module

public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Recovering a binary plane from a fixed line

Let a finite two-group fix exactly one dimension in a binary representation.
Every invariant plane contains that fixed line. If another subgroup preserves
the plane and fixes no vector in the whole module, the orbit of a nonzero
fixed vector spans the plane: a proper orbit span would be a binary
line, on which every invertible operator is the identity.

The proof first finds a nonzero two-group fixed vector in the plane, then
compares dimensions. This is the linear comparison used in Aschbacher–Smith,
14.7.36, printed p.1059, to identify the scalar plane with the literal seed
section before applying the solvable-overgroup contradiction.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender

/-- A fixed-free subgroup generates an invariant binary plane from the
unique fixed line of a finite two-subgroup. -/
theorem orbit_span_eq_binary_plane_of_fixed_line
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (S X : Subgroup A) [Finite S]
    (hS : IsPGroup 2 S)
    (Q : Submodule (ZMod 2) W) (hQ : Module.finrank (ZMod 2) Q = 2)
    (hQS : ∀ s : S, ∀ w ∈ Q, ρ s w ∈ Q)
    (hQX : ∀ x : X, ∀ w ∈ Q, ρ x w ∈ Q)
    (hline : Module.finrank (ZMod 2) (fixedSpace ρ S) = 1)
    (hfree : fixedSpace ρ X = ⊥)
    (v : W) (hv : v ≠ 0) (hfix : v ∈ fixedSpace ρ S) :
    Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x v)) = Q := by
  let U : Subrepresentation (ρ.comp S.subtype) := {
    toSubmodule := Q
    apply_mem_toSubmodule := hQS }
  let : Nontrivial Q := Module.nontrivial_of_finrank_pos (by rw [hQ]; decide)
  obtain ⟨w,hw,hws⟩ := pGroup_fix_nonzero_vector
    (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 2) ≠ 0)
    (by simpa only [ZMod.ringChar_zmod_n] using hS) U.toRepresentation
  have hwn : (w : W) ≠ 0 := fun hz => hw (Subtype.ext hz)
  have hwfix : (w : W) ∈ fixedSpace ρ S := by
    intro s
    exact congrArg Subtype.val (hws s)
  have heline : Submodule.span (ZMod 2) ({(w : W)} : Set W) = fixedSpace ρ S := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by rintro y rfl; exact hwfix)
    · rw [finrank_span_singleton hwn,hline]
  have hvQ : v ∈ Q := by
    apply (Submodule.span_le.mpr (by rintro y rfl; exact w.property) :
      Submodule.span (ZMod 2) ({(w : W)} : Set W) ≤ Q)
    rwa [heline]
  let Z := Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x v))
  have hZQ : Z ≤ Q := Submodule.span_le.mpr (by rintro y ⟨x,rfl⟩; exact hQX x v hvQ)
  have hvZ : v ∈ Z := by
    apply Submodule.subset_span
    exact ⟨1,by simp⟩
  by_contra hne
  have hzle : Module.finrank (ZMod 2) Z ≤ 2 := (Submodule.finrank_mono hZQ).trans_eq hQ
  have hzne : Module.finrank (ZMod 2) Z ≠ 2 := by
    intro hz
    exact hne (Submodule.eq_of_le_of_finrank_eq hZQ (by rw [hz,hQ]))
  have hLZ : Submodule.span (ZMod 2) ({v} : Set W) ≤ Z :=
    Submodule.span_le.mpr (by rintro y rfl; exact hvZ)
  have hlow := Submodule.finrank_mono hLZ
  rw [finrank_span_singleton hv] at hlow
  have hZdim : Module.finrank (ZMod 2) Z = 1 := by omega
  have hL : Submodule.span (ZMod 2) ({v} : Set W) = Z :=
    Submodule.eq_of_le_of_finrank_eq hLZ (by rw [finrank_span_singleton hv,hZdim])
  have hvX : v ∈ fixedSpace ρ X := by
    intro x
    have hx : ρ x v ∈ Submodule.span (ZMod 2) ({v} : Set W) := by
      rw [hL]
      exact Submodule.subset_span ⟨x,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
    have hc01 : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc01 with rfl | rfl
    · have hz : ρ x v = 0 := by simpa using hc.symm
      have he := congrArg (fun u => ρ (x : A)⁻¹ u) hz
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply,map_zero] at he
      exact (hv he).elim
    · simpa using hc.symm
  rw [hfree] at hvX
  exact hv hvX

end Representation.BinaryOffender
