module
public import Theory.GroupTheory.DoubleCoverCentralizer.ActorPreimage
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Sylow
/-!
# Inner involutions fixing a Sylow subgroup

If the center is a two-group, the preimage of an involutory inner action
under conjugation is a two-group. When the action fixes a Sylow two-subgroup,
this preimage centralizes that Sylow subgroup. Sylow maximality therefore
places every conjugator in its center. Central two-covers are preserved.

Source application: Aschbacher–Smith15.1.20(3), first paragraph, p.1095.
-/

public section
open Subgroup
namespace MulAut
variable {L : Type*} [Group L]

/-- A central Sylow element implements the given inner involution. -/
theorem exists_center_sylow_conjugator_of_inner_involution
    (P : Sylow 2 L) (α : MulAut L) (hα : α ^ 2 = 1)
    (hi : α ∈ (MulAut.conj : L →* MulAut L).range)
    (hfix : ∀ x ∈ P, α x = x) (hZ : IsPGroup 2 (center L)) :
    ∃ a : P, a ∈ center P ∧ MulAut.conj (a : L) = α := by
  let A := zpowers α
  have hA : IsPGroup 2 A :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hα).isPGroup 2 _
  let R := A.comap (MulAut.conj : L →* MulAut L)
  have hR : IsPGroup 2 R := hA.comap_of_ker_isPGroup MulAut.conj (by
    rwa [Theory.GroupTheory.DoubleCoverCentralizer.conj_kernel])
  have hAf : A ≤ fixingSubgroup (MulAut L) (P : Set L) := by
    apply zpowers_le.mpr
    exact (mem_fixingSubgroup_iff (MulAut L)).mpr hfix
  have hRC : R ≤ centralizer (P : Set L) := by
    intro a ha x hx
    have hh := ((mem_fixingSubgroup_iff (MulAut L)).mp (hAf ha)) x hx
    change a*x*a⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hPR : (P : Subgroup L) ≤ normalizer (R : Set L) :=
    (le_centralizer_iff.mp hRC).trans (centralizer_le_normalizer _)
  have he := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' hR hPR) le_sup_left
  have hRP : R ≤ P := by rw [←he]; exact le_sup_right
  obtain ⟨a,ha⟩ := hi
  have haR : a ∈ R := by change MulAut.conj a ∈ zpowers α; rw [ha]; exact mem_zpowers α
  have haP : a ∈ P := hRP haR
  have haZ : (⟨a,haP⟩ : P) ∈ center P := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hRC haR x x.property)
  exact ⟨⟨a,haP⟩,haZ,ha⟩
end MulAut
