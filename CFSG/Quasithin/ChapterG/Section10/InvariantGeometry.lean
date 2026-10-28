module
public import CFSG.Quasithin.ChapterG.Section10.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The invariant-space geometry in G.10.4

Full centered transvections force every X-invariant subspace avoiding the
marked point to be disjoint from W. Consequently X fixes its intersection
with the point's orthogonal hyperplane. These statements apply to the actual
HX-submodule in either branch of G.10.4 and require no recognition conclusion.

Source: Aschbacher--Smith, G.10.4, printed pp.357--358.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The common fixed space in W is exactly the prescribed point. -/
theorem fixedSpace_in_W : W ⊓ fixedSpace ρ X = Submodule.span (ZMod 2) {v} := by
  apply le_antisymm
  · intro w hw
    by_contra hn
    have hnot : (⟨w, hw.1⟩ : W) ∉ Submodule.span (ZMod 2) {⟨v, h.point_mem⟩} := by
      intro hm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      exact hn (Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩)
    obtain ⟨f, hfw, hf⟩ := (Submodule.span (ZMod 2) {(⟨v, h.point_mem⟩ : W)}).exists_le_ker_of_notMem hnot
    obtain ⟨x, hx⟩ := h.full_transvections f (hf (Submodule.mem_span_singleton_self _))
    have he := hx ⟨w, hw.1⟩
    have hfx : ρ x w = w := hw.2 x
    change ρ x w = w + f ⟨w, hw.1⟩ • v at he
    rw [hfx] at he
    exact (smul_ne_zero hfw h.point_ne_zero) (add_eq_left.mp he.symm)
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact ⟨h.point_mem, fun x => h.fixes_point x.property⟩

/-- An invariant space avoiding the center is disjoint from the full
centered-transvection space; irreducibility is not needed for this step. -/
theorem disjoint_W_of_point_not_mem (U : Submodule (ZMod 2) V)
    (hstable : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U) (hvU : v ∉ U) : Disjoint U W := by
  rw [Submodule.disjoint_def]
  intro w hwU hwW
  by_contra hw0
  have hnot : (⟨w, hwW⟩ : W) ∉ Submodule.span (ZMod 2) {⟨v, h.point_mem⟩} := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have hc' : c • v = w := congrArg Subtype.val hc
    have hc0 : c ≠ 0 := by
      intro he
      rw [he, zero_smul] at hc'
      exact hw0 hc'.symm
    exact hvU ((U.smul_mem_iff hc0).mp (hc'.symm ▸ hwU))
  obtain ⟨f, hfw, hf⟩ := (Submodule.span (ZMod 2) {(⟨v, h.point_mem⟩ : W)}).exists_le_ker_of_notMem hnot
  obtain ⟨x, hx⟩ := h.full_transvections f (hf (Submodule.mem_span_singleton_self _))
  have hm := U.sub_mem (hstable x w hwU) hwU
  rw [hx ⟨w, hwW⟩, add_sub_cancel_left] at hm
  exact hvU ((U.smul_mem_iff hfw).mp hm)

/-- X fixes the actual intersection with the point's orthogonal hyperplane. -/
theorem fixes_axis (U : Submodule (ZMod 2) V)
    (hstable : ∀ x : X, ∀ u ∈ U, ρ x u ∈ U) (hvU : v ∉ U)
    (x : X) (u : V) (hu : u ∈ U) (hperp : B v u = 0) : ρ x u = u := by
  have hd := h.disjoint_W_of_point_not_mem U hstable hvU
  apply sub_eq_zero.mp
  exact (Submodule.disjoint_def.mp hd) _ (U.sub_mem (hstable x u hu) hu)
    (h.displacement x u hperp)

/-- For a proper G-submodule the disjointness follows solely from G.10.1. -/
theorem submodule_disjoint_W (U : Subrepresentation ρ) (hU : U.toSubmodule ≠ ⊤) :
    Disjoint U.toSubmodule W :=
  h.disjoint_W_of_point_not_mem U.toSubmodule
    (fun x _ hu => U.apply_mem_toSubmodule x hu) (h.point_not_mem U hU)

/-- On a proper invariant space, the nonidentity relative actors have the
exact fixed hyperplane prescribed by the original bilinear form. -/
theorem fixed_iff_on_submodule (U : Subrepresentation ρ) (hU : U.toSubmodule ≠ ⊤)
    (x : X) (hx : x ∉ X₀) (u : U.toSubmodule) :
    ρ x u = (u : V) ↔ B v u = 0 :=
  ⟨h.fixed_bound x hx u, h.fixes_axis U.toSubmodule
    (fun x _ hu => U.apply_mem_toSubmodule x hu) (h.point_not_mem U hU) x u u.property⟩

/-- The point pairing is nonzero on every nonzero invariant subspace.
This supplies the actual hyperplane, rather than assuming its codimension. -/
theorem axis_form_ne_zero (U : Subrepresentation ρ) (hU : U.toSubmodule ≠ ⊥) :
    (B v).comp U.toSubmodule.subtype ≠ 0 := by
  intro he
  apply hU
  apply bot_unique
  intro u hu
  change u = 0
  apply h.nondegenerate.1 u
  have hle : Submodule.span (ZMod 2) {w | ∃ g : G, ρ g v = w} ≤ (B u).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    have hz : B v (ρ g⁻¹ u) = 0 :=
      LinearMap.congr_fun he ⟨ρ g⁻¹ u, U.apply_mem_toSubmodule g⁻¹ hu⟩
    have hp := h.preserves g (ρ g⁻¹ u) v
    have hi : ρ g (ρ g⁻¹ u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hi, h.alternating.eq_iff.mpr hz] at hp
    exact hp
  rw [h.orbit_span] at hle
  exact fun w => hle (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) V))


end CFSG.Quasithin.ChapterG.Section10.Hypothesis
