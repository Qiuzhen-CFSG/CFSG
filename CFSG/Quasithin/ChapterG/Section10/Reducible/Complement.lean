module
public import CFSG.Quasithin.ChapterG.Section10.Lagrangian

/-!
# Complementary common-axis actions cannot occur in large degree

For a Lagrangian U and an invariant complement C, the original pairing
embeds C in U*. The source common-axis action fixes a hyperplane in C.
Pairing it against the full axis group on U places it in a one-dimensional
annihilator. Hence dim U is at most two. This is the final contradiction
in G.10.4, with the actual complement and pairing retained.
-/

public section
open Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

theorem false_of_large_submodule_complement (U C : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) (hdim : 3 ≤ finrank (ZMod 2) U.toSubmodule)
    (hcomp : IsCompl U.toSubmodule C.toSubmodule) : False := by
  obtain ⟨horth,hd⟩ := h.lagrangian_of_large_irreducible_submodule U hU0 hUt hdim
  have hC0 : C.toSubmodule ≠ ⊥ := by
    intro hc
    apply hUt
    simpa only [hc,sup_bot_eq] using hcomp.sup_eq_top
  have hCt : C.toSubmodule ≠ ⊤ := by
    intro hc
    apply hU0
    simpa only [hc,inf_top_eq] using hcomp.inf_eq_bot
  let f := (B v).comp U.toSubmodule.subtype
  let k := (B v).comp C.toSubmodule.subtype
  have hf : f ≠ 0 := h.axis_form_ne_zero U hU0
  have hk : k ≠ 0 := h.axis_form_ne_zero C hC0
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  let q : C.toSubmodule →ₗ[ZMod 2] Module.Dual (ZMod 2) U.toSubmodule :=
    U.toSubmodule.subtype.dualMap.comp (LinearMap.comp B C.toSubmodule.subtype)
  have hq : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro c hc
    have hcU : (c : V) ∈ U.toSubmodule := by
      rw [←horth]
      intro u hu
      have hz := congrArg (fun l : Module.Dual (ZMod 2) U.toSubmodule => l ⟨u,hu⟩) hc
      exact h.alternating.eq_iff.mp hz
    have hz : (c : V) ∈ U.toSubmodule ⊓ C.toSubmodule := ⟨hcU,c.property⟩
    rw [hcomp.inf_eq_bot] at hz
    exact Subtype.ext hz
  have hqA (c : k.ker) : q c ∈ f.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro a ha
    obtain ⟨x,hx⟩ := (h.full_axis_on_submodule U hU0 hUt).2.2 ⟨a,ha⟩
    have hxc : ρ (x : G) (c : C.toSubmodule) = (c : C.toSubmodule) :=
      h.fixes_axis C.toSubmodule (fun x _ hc => C.apply_mem_toSubmodule x hc)
        (h.point_not_mem C hCt) x c c.val.property c.property
    have hxb : ρ (x : G) (b : V) = b+a := by
      have he := hx b
      change U.toRepresentation (x : G) b = b + f b • a at he
      rw [hb,one_smul] at he
      exact congrArg Subtype.val he
    have he := h.preserves (x : G) b c
    rw [hxb,hxc,map_add,LinearMap.add_apply] at he
    exact h.alternating.eq_iff.mpr (add_eq_left.mp he)
  let qA : k.ker →ₗ[ZMod 2] f.ker.dualAnnihilator :=
    (q.comp k.ker.subtype).codRestrict _ hqA
  have hqAi : Function.Injective qA := by
    intro c d he
    apply Subtype.ext
    apply hq
    exact congrArg Subtype.val he
  have hineq := LinearMap.finrank_le_finrank_of_injective hqAi
  have hfk := f.finrank_range_add_finrank_ker
  have hkk := k.finrank_range_add_finrank_ker
  rw [Module.Dual.range_eq_top_of_ne_zero hf,finrank_top,Module.finrank_self] at hfk
  rw [Module.Dual.range_eq_top_of_ne_zero hk,finrank_top,Module.finrank_self] at hkk
  have hA := Subspace.finrank_add_finrank_dualAnnihilator_eq f.ker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U.toSubmodule C.toSubmodule
  rw [hcomp.sup_eq_top,hcomp.inf_eq_bot,finrank_top,finrank_bot,add_zero] at hsum
  omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
