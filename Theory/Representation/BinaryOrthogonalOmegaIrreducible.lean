module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega
public import Theory.Representation.SmallBinaryNaturalSimplicity
public import Theory.Representation.SubrepresentationLattice

/-!
# Irreducibility of the marked natural binary omega action

The two cubic coordinate rotations and the interchange belong to the genuine
omega subgroup. A nonzero invariant subspace therefore contains one plane,
then both planes. Compatible coordinates transfer this conclusion to the
actual D.2.17(5) factor action in the proper-span branch of 15.1.2.

Source: Aschbacher--Smith D.2.17(5) and 15.1.2, printed pp.188 and 1085.
-/

public section
namespace OrthogonalFourBinary
open SylowGeometry TerminalLines
private theorem left_unit : ∀ v : Space, v.1 ≠ 0 → ∃ i j : Fin 3,
    eval ((i,0),(0,0),false) v + eval ((j,0),(0,0),false) v = ((1,0),(0,0)) := by
  decide +kernel

/-- Genuine omega acts irreducibly on the specified binary four-space. -/
theorem omega_subspace_eq_bot_or_top (W : Submodule F Space)
    (hW : ∀ g : omega, ∀ v ∈ W, g.val.val v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hzero : W = ⊥
  · exact Or.inl hzero
  right
  have hcode (i : Code) (hi : i.1.2 = i.2.1.2) {v : Space} (hv : v ∈ W) :
      eval i v ∈ W := by
    have h := hW ⟨codeMap i,(codeMap_mem_omega i).mpr hi⟩ v hv
    change candidate i v ∈ W at h
    simpa only [candidate_eval] using h
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
  have hv' : ∃ w ∈ W, w.1 ≠ 0 := by
    by_cases hx : v.1 = 0
    · refine ⟨eval interchange v,hcode interchange rfl hv,?_⟩
      change v.2 ≠ 0
      intro hy
      exact hv0 (Prod.ext hx hy)
    · exact ⟨v,hv,hx⟩
  obtain ⟨w,hw,hw0⟩ := hv'
  obtain ⟨i,j,hij⟩ := left_unit w hw0
  have hunit : ((1,0),(0,0)) ∈ W := hij ▸ W.add_mem
    (hcode ((i,0),(0,0),false) rfl hw) (hcode ((j,0),(0,0),false) rfl hw)
  have hall : ∀ z : Space, z ∈ W := by
    intro z
    have hfirst : ∀ x : Plane, (x,(0,0)) ∈ W := by
      intro x
      have he : x = 0 ∨ ∃ i : Fin 3, eval ((i,0),(0,0),false) ((1,0),(0,0)) = (x,(0,0)) := by
        exact (show ∀ x : Plane, x = 0 ∨ ∃ i : Fin 3,
          eval ((i,0),(0,0),false) ((1,0),(0,0)) = (x,(0,0)) by decide +kernel) x
      rcases he with he | ⟨i,he⟩
      · rw [he]; change (0 : Space) ∈ W; exact W.zero_mem
      · exact he ▸ hcode ((i,0),(0,0),false) rfl hunit
    have hsecond : ((0,0),z.2) ∈ W := by
      have hh := hcode interchange rfl (hfirst z.2)
      change ((0,0),z.2) ∈ W at hh
      exact hh
    have hh := W.add_mem (hfirst z.1) hsecond
    change (z.1 + 0,0 + z.2) ∈ W at hh
    simpa only [add_zero,zero_add,Prod.eta] using hh
  exact top_unique (fun z _ => hall z)

end OrthogonalFourBinary

namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem irreducible_of_binaryOmega_coordinates
    (ρ : Representation (ZMod 2) G V)
    (c : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
    (e : G ≃* OrthogonalFourBinary.omega)
    (hc : ∀ g v, c (ρ g v) = (e g).val.val (c v)) : IsIrreducible ρ := by
  let : Nontrivial V := c.toEquiv.nontrivial
  refine ⟨fun S => ?_⟩
  rcases subspace_simple_of_coordinates ρ (fun g v => g.val.val v) c e hc
    OrthogonalFourBinary.omega_subspace_eq_bot_or_top S.toSubmodule
    (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)
end Representation
