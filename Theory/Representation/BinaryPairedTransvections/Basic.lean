module
public import Theory.Representation.BinaryTransvectionGroups.Duality
public import Mathlib.FieldTheory.Finiteness

/-!
# The full binary transvection groups at an incident point and hyperplane

The point group fixes a nonzero vector and moves only its line; the axis
group fixes a hyperplane pointwise and acts trivially on the quotient.
The existing binary radical descriptions identify the literal transvections.
Functionals vanishing at the center parametrize the point group, giving its
order and elementary structure in the paired action of source 15.3.56.

Source: Aschbacher–Smith, 15.3.56(6–7), printed p.1148.
-/

@[expose] public section
open Subgroup
namespace BinaryPairedTransvections
open BinaryLinear BinaryTransvectionGroups
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

abbrev centerGroup (c : E) : Subgroup (GL E) := rootGroup ⊤ c
abbrev axisGroup (d : Module.Dual (ZMod 2) E) : Subgroup (GL E) := axisRootGroup ⊤ d
abbrev pairGroup (c : E) (d : Module.Dual (ZMod 2) E) : Subgroup (GL E) :=
  centerGroup c ⊔ axisGroup d

@[simp] theorem centerGroup_eq_radical (c : E) :
    centerGroup c = radical (Submodule.span (ZMod 2) {c}) := top_inf_eq _
@[simp] theorem axisGroup_eq_radical (d : Module.Dual (ZMod 2) E) :
    axisGroup d = radical d.ker := top_inf_eq _

theorem mem_centerGroup_iff (c : E) (hc : c ≠ 0) (a : GL E) :
    a ∈ centerGroup c ↔ ∃ f : Module.Dual (ZMod 2) E, ∃ hf : f c = 0,
      a = transvection c f hf := by
  simpa only [Subgroup.mem_top, true_and] using (mem_rootGroup_iff hc (t := a) (G := ⊤))

theorem transvection_mem_axisGroup (d : Module.Dual (ZMod 2) E) (w : E) (hw : d w = 0) :
    transvection w d hw ∈ axisGroup d := by
  rw [axisGroup_eq_radical]
  exact transvection_mem hw le_rfl

theorem centerGroup_elementary (c : E) : IsElementaryAbelian 2 (centerGroup c) :=
  rootGroup_elementaryAbelian ⊤ c

theorem axisGroup_elementary (d : Module.Dual (ZMod 2) E) : IsElementaryAbelian 2 (axisGroup d) :=
  elementaryAbelian_of_le_radical (axisGroup d).subtype Subtype.val_injective d.ker
    (fun g => g.property.2)

abbrev forms (c : E) : Submodule (ZMod 2) (Module.Dual (ZMod 2) E) :=
  (Module.Dual.eval (ZMod 2) E c).ker

/-- The full center group is parametrized by the functionals vanishing at its center. -/
noncomputable def centerEquiv (c : E) (hc : c ≠ 0) : forms c ≃ centerGroup c :=
  Equiv.ofBijective (fun f => ⟨transvection c f.val f.property,
    (mem_centerGroup_iff c hc _).mpr ⟨f.val,f.property,rfl⟩⟩) (by
    constructor
    · intro f g he
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      have hh := congrArg (fun a : centerGroup c => (a : GL E) v) he
      change v + f.val v • c = v + g.val v • c at hh
      exact (smul_left_injective _ hc) (add_left_cancel hh)
    · intro a
      obtain ⟨f,hf,he⟩ := (mem_centerGroup_iff c hc _).mp a.property
      exact ⟨⟨f,hf⟩,Subtype.ext he.symm⟩)

theorem centerGroup_card [FiniteDimensional (ZMod 2) E]
    (c : E) (hc : c ≠ 0) (s : ℕ) (hdim : Module.finrank (ZMod 2) E = s+2) :
    Nat.card (centerGroup c) = 2^(s+1) := by
  have he : Module.Dual.eval (ZMod 2) E c ≠ 0 := by
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hc
    intro hz
    have hh := congrArg (fun l : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) E) => l f) hz
    change f c = 0 at hh
    rw [hf] at hh
    exact one_ne_zero hh
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero he
  rw [Subspace.dual_finrank_eq, hdim] at hr
  have hr' : Module.finrank (ZMod 2) (forms c) = s+1 := by
    change Module.finrank (ZMod 2) (Module.Dual.eval (ZMod 2) E c).ker = s+1
    omega
  rw [← Nat.card_congr (centerEquiv c hc),
    Module.natCard_eq_pow_finrank (K := ZMod 2), hr', Nat.card_zmod]

end BinaryPairedTransvections
