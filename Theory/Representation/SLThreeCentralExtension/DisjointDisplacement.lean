module
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.Representation.FirstCohomologyDuality.Indecomposable
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# A disjoint involution displacement splits the actual natural cover

A nonzero central kernel of a commutator-generated binary SL₃ natural
cover has dimension one, by the dual first-cohomology bound. The cover
then has dimension four. Every involution displacement equals its fixed
space and contains the central kernel, so disjointness forces that kernel
to vanish. This is used with the actual opposite U_H span in13.7.16.

Source: Aschbacher–Smith B.4.8(2)–(3), printed p.91, and13.7.16(2), p.944.
-/

public section
open Representation Module
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)

theorem cover_bijective_of_disjoint_involution_displacement
    (p : ρ.IntertwiningMap W) (hp : IsCover p)
    (a : BinaryLinearThree.Group) (ha : orderOf a = 2)
    (hdis : Disjoint p.toLinearMap.ker (LinearMap.range (ρ a - LinearMap.id))) :
    Function.Bijective p := by
  refine ⟨?_,hp.1⟩
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  have hlo : 0 < finrank (ZMod 2) p.toLinearMap.ker := by
    have hn : finrank (ZMod 2) p.toLinearMap.ker ≠ 0 :=
      fun he => hker (Submodule.finrank_eq_zero.mp he)
    omega
  have hle := finrank_ker_le_H1_of_cover p hp
  rw [finrank_H1_dual] at hle
  have hdker : finrank (ZMod 2) p.toLinearMap.ker = 1 := by omega
  have hd : finrank (ZMod 2) V = 4 := by
    have he := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1,finrank_top,hdker] at he
    have hw : finrank (ZMod 2) Vector = 3 := Module.finrank_fin_fun (ZMod 2)
    rw [hw] at he
    omega
  have hc := NaturalExtension.involution_codim_of_commutator_top ρ hd hp.2.2 a ha
  have he := (NaturalExtension.involution_range_eq_fixed ρ hd a ha hc).1
  have hk : p.toLinearMap.ker ≤ LinearMap.range (ρ a - LinearMap.id) := by
    rw [he]
    intro v hv k
    exact hp.2.1 hv k.val
  exact hker (le_bot_iff.mp ((le_inf le_rfl hk).trans hdis.le_bot))

end Representation.OneCohomology.SLThreeCentralExtension
