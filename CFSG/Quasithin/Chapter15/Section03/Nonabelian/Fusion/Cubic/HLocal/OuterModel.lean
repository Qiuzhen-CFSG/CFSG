module

public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import GorensteinWalter.PGL2OuterInvolutionFusion

/-!
# Cubic subgroups centralized by outer automorphisms of PSL₃(2)

Transport through the checked PGL₂(7) isomorphism proves that every outer
involution is conjugate to inverse transpose. The permutation matrix of a
three-cycle is fixed by inverse transpose and gives a cubic inner subgroup;
conjugation transports that subgroup into the required centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the model
calculation in the proof of 15.3.61(1), printed p.1150.
-/

public section
open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.OuterModel
open BinaryLinearThree.AutomorphismAction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def pglEquiv : GorensteinWalter.PGL2 (ZMod 7) ≃* MulAut Matrix.PSL3Two.SL :=
  Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.trans
    (MulAut.congr Matrix.PSL3Two.equiv.symm)

attribute [local irreducible] pglEquiv

private lemma commutator_le_inner : commutator (MulAut Matrix.PSL3Two.SL) ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
  apply Normal.quotient_commutative_iff_commutator_le.mp
  exact (isCyclic_of_prime_card Matrix.PSL3Two.Automorphisms.card_outer_sl).isMulCommutative

private lemma outer_not_commutator (x : MulAut Matrix.PSL3Two.SL) (hx : x ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    pglEquiv.symm x ∉ commutator (GorensteinWalter.PGL2 (ZMod 7)) := by
  intro hh
  apply hx
  apply commutator_le_inner
  have hm := mem_map_of_mem pglEquiv.toMonoidHom hh
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr pglEquiv.surjective] at hm
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, commutator_def] using hm

private lemma outer_involution (x : MulAut Matrix.PSL3Two.SL) (hx : x ^ 2 = 1)
    (ho : x ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    GorensteinWalter.IsInvolution (pglEquiv.symm x) := by
  constructor
  · intro hh
    apply ho
    have he : x = 1 := pglEquiv.symm.injective (hh.trans (map_one _).symm)
    rw [he]
    exact one_mem _
  · rw [← map_pow, hx, map_one]

private lemma seven_prime_power : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) := by
  exact ⟨7, 1, by decide, by decide, by decide, by norm_num⟩

/-- Every noninner involution of the actual automorphism group is conjugate to inverse transpose. -/
lemma outer_conjugate_graph (a : MulAut Matrix.PSL3Two.SL) (ha : a ^ 2 = 1)
    (hout : a ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL) : IsConj graph a := by
  have hc := GorensteinWalter.pgl2_outer_involutions_conjugate (ZMod 7) seven_prime_power
    (a := pglEquiv.symm graph) (b := pglEquiv.symm a)
    (by norm_num) (outer_involution graph (by simpa only [pow_two] using graph_sq) graph_not_inner)
    (outer_involution a ha hout) (outer_not_commutator graph graph_not_inner)
    (outer_not_commutator a hout)
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
    pglEquiv.toMonoidHom.map_isConj hc

private def cycle : Matrix.PSL3Two.SL := ⟨!![0,0,1;1,0,0;0,1,0], by decide⟩
private lemma cycle_cube : cycle ^ 3 = 1 := by decide
private lemma cycle_ne : cycle ≠ 1 := by decide
private lemma cycle_graph : graph cycle = cycle := by
  change cycle⁻¹.transpose = cycle
  have hi : cycle⁻¹ = cycle ^ 2 := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using cycle_cube)
  rw [hi]
  decide

/-- Every noninner involution centralizes an actual subgroup of order three. -/
lemma outer_cubic (a : MulAut Matrix.PSL3Two.SL) (ha : a ^ 2 = 1)
    (hout : a ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    ∃ D : Subgroup (MulAut Matrix.PSL3Two.SL), Nat.card D = 3 ∧ D ≤ centralizer ({a} : Set _) := by
  have ho : orderOf (MulAut.conj cycle) = 3 := by
    rw [orderOf_injective (MulAut.conj : Matrix.PSL3Two.SL →* MulAut Matrix.PSL3Two.SL)
      (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)]
    exact orderOf_eq_prime cycle_cube cycle_ne
  have hc : MulAut.conj cycle ∈ centralizer ({graph} : Set _) := by
    apply mem_centralizer_singleton_iff.mpr
    apply MulEquiv.ext
    intro x
    change cycle * graph x * cycle⁻¹ = graph (cycle * x * cycle⁻¹)
    simp only [map_mul, map_inv, cycle_graph]
  obtain ⟨b, hb⟩ := isConj_iff.mp (outer_conjugate_graph a ha hout)
  let f := (MulAut.conj b).toMonoidHom
  refine ⟨(zpowers (MulAut.conj cycle)).map f, ?_, ?_⟩
  · rw [card_map_of_injective (MulAut.conj b).injective, Nat.card_zpowers, ho]
  · rintro _ ⟨x, hx, rfl⟩
    have hxC := (zpowers_le.mpr hc) hx
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg f (mem_centralizer_singleton_iff.mp hxC)
    simpa only [map_mul, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hb] using he
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.OuterModel
