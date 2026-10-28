module

public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.NormalInvariants
public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# A two-group normalizing a common-center root group centralizes it

In characteristic two a two-group fixes every module of dimension at most one.
For a normal subgroup A whose moved space and fixed codimension are at most
one, the whole two-group therefore fixes both the moved line and the quotient
by the fixed hyperplane. These two assertions make all displacement operators
of A commute with the ambient action. Faithfulness makes A central.

Source application: the covered-A6 plane exclusion in Aschbacher–Smith
13.7.15(1), printed pp.943–944.
-/

public section
namespace Representation.PlaneRootNormalizer
open Subgroup
variable {F G V : Type*} [Field F] [CharP F 2] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F G V)

/-- A modular two-group acts trivially on a space of dimension at most one. -/
theorem apply_eq_of_finrank_le_one (hp : IsPGroup 2 G)
    (hd : Module.finrank F V ≤ 1) (g : G) (v : V) : ρ g v = v := by
  by_cases hz : Subsingleton V
  · let := hz
    exact Subsingleton.elim _ _
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hz
    have hchar : ringChar F = 2 := ringChar.eq F 2
    obtain ⟨w,hw,hfix⟩ := pGroup_fix_nonzero_vector
      (show ringChar F ≠ 0 by omega) (hchar.symm ▸ hp) ρ
    have hpdim : 0 < Module.finrank F V := Module.finrank_pos
    obtain ⟨c,rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := F) w hw).mp (by omega) v
    rw [map_smul]
    exact congrArg (c • ·) (hfix g)

/-- The displacement span of a normal actor is an ambient subrepresentation. -/
private noncomputable def movedOfNormal (A : Subgroup G) [A.Normal] : Subrepresentation ρ where
  toSubmodule := Coinvariants.ker (ρ.comp A.subtype)
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a,w⟩,rfl⟩ := hv
      have ha : g * (a : G) * g⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a a.property g
      have hm := Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype)
        ⟨g * (a : G) * g⁻¹,ha⟩ (ρ g w)
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_sub, map_mul,
        Module.End.mul_apply, inv_self_apply] using hm
    | zero => simpa only [map_zero] using (Submodule.zero_mem (Coinvariants.ker (ρ.comp A.subtype)))
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- The common-center and common-axis conditions force centrality. -/
theorem le_center_of_moved_and_fixed_codim_le_one
    (hp : IsPGroup 2 G) (hf : Function.Injective ρ)
    (A : Subgroup G) [A.Normal]
    (hm : Module.finrank F (Coinvariants.ker (ρ.comp A.subtype)) ≤ 1)
    (hc : Module.finrank F (V ⧸ Representation.invariants (ρ.comp A.subtype)) ≤ 1) : A ≤ center G := by
  let R := movedOfNormal ρ A
  let C := fixedSubrepresentationOfNormal ρ A
  have hR (g : G) (v : V) (hv : v ∈ R.toSubmodule) : ρ g v = v := by
    exact congrArg Subtype.val
      (apply_eq_of_finrank_le_one R.toRepresentation hp hm g ⟨v,hv⟩)
  have hC (g : G) (v : V) : ρ g v - v ∈ C.toSubmodule := by
    have he := apply_eq_of_finrank_le_one C.quotientRepresentation hp hc g (C.toSubmodule.mkQ v)
    exact (Submodule.Quotient.eq C.toSubmodule).mp he
  intro a ha
  apply mem_center_iff.mpr
  intro g
  apply hf
  apply LinearMap.ext
  intro v
  have h1 := hR g (ρ a v - v) (Coinvariants.sub_mem_ker
    (ρ := ρ.comp A.subtype) ⟨a,ha⟩ v)
  have h2 := hC g v
  change ∀ b : A, ρ b (ρ g v - v) = ρ g v - v at h2
  have h2' := h2 ⟨a,ha⟩
  simp only [map_sub] at h1 h2'
  simp only [map_mul, Module.End.mul_apply]
  exact add_right_cancel (((sub_eq_sub_iff_add_eq_add).mp h1).trans
    ((add_comm _ _).trans ((sub_eq_sub_iff_add_eq_add).mp h2').symm))
end Representation.PlaneRootNormalizer
