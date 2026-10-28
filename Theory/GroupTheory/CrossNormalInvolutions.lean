module

public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Commutator.Basic


/-!
# Crossed involutions produce a common Frattini displacement

Suppose involutions h and g lie in two two-subgroups W and W′ and each
normalizes the other's subgroup. If h does not commute with its g-conjugate,
put y=(hg)². Then y lies in both groups, [y,g]=y² is nontrivial, and y²
lies in both embedded Frattini subgroups. The word identity supplies the
exact obstruction needed in Campbell II.6.2 without a dihedral recognition
or an unnecessary order calculation.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.6.2, printed p.30.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem exists_cross_frattini_displacement_of_noncommuting_involutions (W W' : Subgroup G)
    (hW : IsPGroup 2 W) (hW' : IsPGroup 2 W')
    (g h : G) (hg2 : g^2=1) (hh2 : h^2=1)
    (hg : g ∈ W') (hh : h ∈ W)
    (hgN : g ∈ normalizer (W : Set G)) (hhN : h ∈ normalizer (W' : Set G))
    (hne : ⁅h,g*h*g⁻¹⁆ ≠ 1) :
    ∃ y ∈ W ⊓ W', y^2 ≠ 1 ∧ ⁅y,g⁆=y^2 ∧
      y^2 ∈ (frattini W).map W.subtype ⊓ (frattini W').map W'.subtype := by
  have hgi : g⁻¹=g := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hg2)
  have hhi : h⁻¹=h := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hh2)
  have hgg : g*g=1 := by simpa only [pow_two] using hg2
  have hhh : h*h=1 := by simpa only [pow_two] using hh2
  let y := h*g*h*g
  have hyW : y ∈ W := by
    have hc : g*h*g⁻¹ ∈ W := (mem_normalizer_iff.mp hgN h).mp hh
    simpa only [hgi,mul_assoc,y] using W.mul_mem hh hc
  have hyW' : y ∈ W' := by
    have hc : h*g*h⁻¹ ∈ W' := (mem_normalizer_iff.mp hhN g).mp hg
    simpa only [hhi,y] using W'.mul_mem hc hg
  have hy2 : y^2 = ⁅h,g*h*g⁻¹⁆ := by
    simp only [commutatorElement_def,mul_inv_rev,hgi,hhi,pow_two,y,mul_assoc]
  have hcomm : ⁅y,g⁆=y^2 := by
    simp only [commutatorElement_def,mul_inv_rev,hgi,hhi,pow_two,y,mul_assoc]
    simp only [←mul_assoc,hgg,one_mul]
  refine ⟨y,⟨hyW,hyW'⟩,fun hz => hne (hy2.symm.trans hz),hcomm,?_,?_⟩
  · let : Fact (IsPGroup 2 W) := ⟨hW⟩
    exact mem_map_of_mem W.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨y,hyW⟩ : W))
  · let : Fact (IsPGroup 2 W') := ⟨hW'⟩
    exact mem_map_of_mem W'.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨y,hyW'⟩ : W'))
end Subgroup
