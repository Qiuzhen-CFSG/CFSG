module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.Representation.PSL3Two.SmallModules

/-!
# Natural point radicals in SL₃(2)

The literal stabilizer of a nonzero column vector is a conjugate of the
standard point parabolic. Its radical has order four and fixes only that
nonzero vector. An involution having that vector as a displacement belongs
to the radical: after moving the vector to e₀, its matrix is an upper-row
translation. This last assertion uses a small kernel-checked coordinate test.

Source: the binary projective-plane model in Aschbacher–Smith I.5.4,
printed p.420; used in C.1.34(5), printed p.137.
-/

@[expose] public section
open Subgroup
namespace BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

/-- The actual matrix stabilizer of a natural column vector. -/
def naturalPoint (v : Vector) : Subgroup Group := MulAction.stabilizer Group v

@[simp] theorem mem_naturalPoint (g : Group) (v : Vector) :
    g ∈ naturalPoint v ↔ W g v = v := Iff.rfl

private def e0 : Vector := ![1,0,0]

private theorem naturalPoint_e0 : naturalPoint e0 = pointParabolicSL := by
  rw [← Matrix.PSL3Two.Fano.stabilizer_flagPoint_SL]
  ext g
  change g • e0 = e0 ↔ g • flagPoint = flagPoint
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem naturalPoint_action (g : Group) (v : Vector) :
    naturalPoint (W g v) = (naturalPoint v).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

private theorem pointCore_marking (v : Vector) (hv : v ≠ 0) :
    ∃ g : Group, W g e0 = v ∧
      (naturalPoint v).pCoreIn 2 = pointV.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three e0 v (by decide) hv
  change W g e0 = v at hg
  refine ⟨g,hg,?_⟩
  rw [← hg,naturalPoint_action,← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    naturalPoint_e0,MarkedProduct.pointParabolic_core]

/-- Every nonzero natural-point radical has order four. -/
theorem card_naturalPoint_core (v : Vector) (hv : v ≠ 0) :
    Nat.card ((naturalPoint v).pCoreIn 2) = 4 := by
  obtain ⟨g,_,hg⟩ := pointCore_marking v hv
  rw [hg,card_map_of_injective (MulAut.conj g).injective,card_pointV]

private theorem pointV_fixed (w : Vector) (hw : w ≠ 0)
    (hf : ∀ a ∈ pointV, W a w = w) : w = e0 := by
  have h1 : Bruhat.upper 1 ∈ pointV := by decide +kernel
  have h2 : Bruhat.upper 2 ∈ pointV := by decide +kernel
  have he : ∀ w : Vector, w ≠ 0 →
      (Bruhat.upper 1).val.mulVec w = w →
      (Bruhat.upper 2).val.mulVec w = w → w = e0 := by decide +kernel
  exact he w hw (hf _ h1) (hf _ h2)

/-- The point radical fixes exactly one nonzero vector in the natural module. -/
theorem naturalPoint_core_fixed_unique (v w : Vector) (hv : v ≠ 0) (hw : w ≠ 0)
    (hf : ∀ a ∈ (naturalPoint v).pCoreIn 2, W a w = w) : w = v := by
  obtain ⟨g,hg,hcore⟩ := pointCore_marking v hv
  have hn : W g⁻¹ w ≠ 0 := by
    intro hz
    have hh := congrArg (W g) hz
    exact hw (by simpa only [W.self_inv_apply,map_zero] using hh)
  have he : W g⁻¹ w = e0 := pointV_fixed _ hn (by
    intro a ha
    have hh := hf (g*a*g⁻¹) (hcore ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    have ht := congrArg (W g⁻¹) hh
    simpa only [map_mul,Module.End.mul_apply,W.inv_self_apply] using ht)
  have hh := congrArg (W g) he
  simpa only [W.self_inv_apply,hg] using hh

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem displacement_test : ∀ a : Group, a * a = 1 → ∀ w : Vector,
    a.val.mulVec w - w = e0 → a ∈ pointV := by decide +kernel

/-- A nonzero natural displacement determines the point radical containing
its involution. The condition retains the literal natural matrix action. -/
theorem involution_mem_naturalPoint_core (a : Group) (ha : orderOf a = 2)
    (v : Vector) (hv : v ≠ 0) (w : Vector) (hw : W a w - w = v) :
    a ∈ (naturalPoint v).pCoreIn 2 := by
  obtain ⟨g,hg,hcore⟩ := pointCore_marking v hv
  have hs : a*a = 1 := by simpa only [ha,pow_two] using pow_orderOf_eq_one a
  have hb : (g⁻¹*a*g)*(g⁻¹*a*g) = 1 := by
    calc
      _ = g⁻¹*(a*a)*g := by group
      _ = 1 := by rw [hs]; group
  have he : W (g⁻¹*a*g) (W g⁻¹ w) - W g⁻¹ w = e0 := by
    have hh := congrArg (W g⁻¹) hw
    rw [← hg,W.inv_self_apply] at hh
    simpa only [map_sub,map_mul,Module.End.mul_apply,W.self_inv_apply] using hh
  have hm := displacement_test (g⁻¹*a*g) hb (W g⁻¹ w) he
  rw [hcore]
  refine ⟨g⁻¹*a*g,hm,?_⟩
  change g*(g⁻¹*a*g)*g⁻¹ = a
  group

end BinaryLinearThree
