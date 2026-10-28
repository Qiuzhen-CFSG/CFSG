module
public import Theory.Representation.Suzuki.NaturalCentralizer
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Binary irreducibility of the natural Suzuki module

A nonzero invariant binary subspace has a nonzero vector fixed by the
root two-group. The root equations place it on the first coordinate line.
The Weyl element and central root elements recover the other coordinate
vectors with the same coefficient. Varying a central root parameter then
recovers every coefficient on the first line, and hence all four lines.
This proves irreducibility over F₂, without assuming closure under the
larger defining field or deducing simplicity from the scalar commutant.

Consumer: the original Suzuki row in Aschbacher--Smith10.2.9, printed p.751.
Matrix formulas: Huppert--Blackburn, Finite Groups III, XI.3.1 and XI.3.3.
-/

public noncomputable section
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Subgroup
namespace Representation.SuzukiNatural
namespace BinaryIrreducibility
private def root (m : ℕ) (a b : F m) : SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m a b, subset_closure (Or.inl ⟨a,b,rfl⟩)⟩
private def weyl (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, subset_closure (Or.inr (Or.inr rfl))⟩
private def axis (m : ℕ) (i : Fin 4) (a : F m) : W m := Pi.single i a
private theorem weyl_apply (m : ℕ) (v : W m) :
    natural m (weyl m) v = ![v 3,v 2,v 1,v 0] := by
  ext i
  fin_cases i <;> simp [natural_apply,weyl,SuzukiWeylGL,SuzukiWeylMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four]
private theorem root_apply (m : ℕ) (a b : F m) (v : W m) :
    natural m (root m a b) v =
      ![v 0 + a * v 1 + b * v 2 +
          (a ^ (2 + 2 ^ (m+1)) + a*b + b ^ (2 ^ (m+1))) * v 3,
        v 1 + a ^ (2 ^ (m+1)) * v 2 + (a ^ (1 + 2 ^ (m+1))+b) * v 3,
        v 2 + a * v 3, v 3] := by
  ext i
  fin_cases i <;> simp [natural_apply,root,SuzukiRootGL,SuzukiRootMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four,add_assoc]
private theorem fixed_axis (m : ℕ) (v : W m)
    (h : ∀ a b, natural m (root m a b) v = v) : v = axis m 0 (v 0) := by
  have h01 := h 0 1
  rw [root_apply] at h01
  have h3 : v 3 = 0 := by
    have hh := congrFun h01 1
    simpa using hh
  have h2 : v 2 = 0 := by
    have hh := congrFun h01 0
    simpa [h3] using hh
  have h1 : v 1 = 0 := by
    have hh := congrFun (h 1 0) 0
    rw [root_apply] at hh
    simpa [h2,h3] using hh
  ext i
  fin_cases i <;> simp [axis,h1,h2,h3]
private theorem weyl_axis (m : ℕ) (x : F m) (i : Fin 4) :
    natural m (weyl m) (axis m i x) = axis m (3-i) x := by
  rw [weyl_apply]
  ext j
  fin_cases i <;> fin_cases j <;> simp [axis]
private theorem root_last (m : ℕ) (x : F m) :
    natural m (root m 0 1) (axis m 3 x) =
      axis m 0 x + axis m 1 x + axis m 3 x := by
  rw [root_apply]
  ext i
  fin_cases i <;> simp [axis]
private theorem root_third (m : ℕ) (x b : F m) :
    natural m (root m 0 b) (axis m 2 x) = axis m 0 (b*x) + axis m 2 x := by
  rw [root_apply]
  ext i
  fin_cases i <;> simp [axis]


/-- The natural Suzuki module is irreducible over its binary prime field. -/
theorem natural_irreducible (m : ℕ) (hm : 0 < m) : IsIrreducible (natural m) := by
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  obtain ⟨v,hv,hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := ZMod 2) (G := SuzukiRootSubgroup m) (V := S.toSubmodule)
    (by rw [ringChar.eq (ZMod 2) 2]; decide) (by rw [ringChar.eq (ZMod 2) 2]; exact suzukiRootSubgroup_isPGroup m hm)
    (S.toRepresentation.comp (SuzukiRootSubgroup m).subtype)
  have he : v.val = axis m 0 (v.val 0) := by
    apply fixed_axis
    intro a b
    exact congrArg Subtype.val (hfix ⟨root m a b,
      (mem_suzukiRootSubgroup_iff m _).mpr ⟨a,b,rfl⟩⟩)
  let x := v.val 0
  have hx : x ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    simpa [axis,show v.val 0 = 0 from hz] using he
  have h0 : axis m 0 x ∈ S.toSubmodule := he ▸ v.property
  have axes (y : F m) (hy : axis m 0 y ∈ S.toSubmodule) :
      axis m 3 y ∈ S.toSubmodule ∧ axis m 1 y ∈ S.toSubmodule ∧ axis m 2 y ∈ S.toSubmodule := by
    have h3 : axis m 3 y ∈ S.toSubmodule := by
      simpa only [weyl_axis,show (3-(0:Fin 4)) = 3 from rfl]
        using S.apply_mem_toSubmodule (weyl m) hy
    have h01 : axis m 0 y + axis m 1 y ∈ S.toSubmodule := by
      simpa only [root_last,add_sub_cancel_right] using
        S.toSubmodule.sub_mem (S.apply_mem_toSubmodule (root m 0 1) h3) h3
    have h1 : axis m 1 y ∈ S.toSubmodule := by
      simpa only [add_sub_cancel_left] using S.toSubmodule.sub_mem h01 hy
    have h2 : axis m 2 y ∈ S.toSubmodule := by
      simpa only [weyl_axis,show (3-(1:Fin 4)) = 2 from rfl]
        using S.apply_mem_toSubmodule (weyl m) h1
    exact ⟨h3,h1,h2⟩
  have h2 := (axes x h0).2.2
  have h0all (y : F m) : axis m 0 y ∈ S.toSubmodule := by
    simpa only [root_third,add_sub_cancel_right,div_mul_cancel₀ _ hx] using
      S.toSubmodule.sub_mem (S.apply_mem_toSubmodule (root m 0 (y/x)) h2) h2
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro w _
  have hw : w = axis m 0 (w 0) + axis m 1 (w 1) + axis m 2 (w 2) + axis m 3 (w 3) := by
    ext i
    fin_cases i <;> simp [axis]
  rw [hw]
  exact S.toSubmodule.add_mem
    (S.toSubmodule.add_mem
      (S.toSubmodule.add_mem (h0all _) (axes _ (h0all _)).2.1)
      (axes _ (h0all _)).2.2) (axes _ (h0all _)).1
end BinaryIrreducibility
end Representation.SuzukiNatural
