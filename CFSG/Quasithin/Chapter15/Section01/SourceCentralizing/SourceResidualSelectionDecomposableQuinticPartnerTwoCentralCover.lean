module

public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.Representation.BinaryParabolicNatural.CentralCovers

/-!
# A small involution excludes the central natural attachment

Consider a literal central cover of the binary natural SL_n module, with
commutator-generated source, for n at least three. In dimension three the
kernel has dimension at most one. A nonzero kernel would give the exceptional
four-space, where every involution has fixed codimension two. Thus an actual
involution of fixed codimension at most one rules out that kernel. In higher
dimensions the checked dual first-cohomology vanishing already kills it.

The statement assumes neither faithfulness nor a trivial two-core upstairs.
It retains the given special-linear action and the given equivariant covering
map. The planned source application uses an original support involution after
the actual kernel shears have been factored out.
-/

public section
open Representation Representation.OneCohomology Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl

/-- A fully moved central cover of the binary natural module is injective
if an actual involution has fixed codimension at most one. -/
theorem natural_cover_injective_of_small_involution
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (n : ℕ) (hn : 3 ≤ n)
    (τ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) W)
    (p : τ.IntertwiningMap (specialLinearNatural (k := ZMod 2) n)) (hp : IsCover p)
    (a : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) (ha : orderOf a = 2)
    (hc : fixedCodim τ (zpowers a) ≤ 1) : Function.Injective p := by
  by_cases hn3 : n = 3
  · subst n
    have hk := finrank_ker_le_H1_of_cover p hp
    rw [SLThreeCentralExtension.finrank_H1_dual] at hk
    have hd := p.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp.1, finrank_top, Module.finrank_fin_fun] at hd
    have hn4 : Module.finrank (ZMod 2) W ≠ 4 := by
      intro hd4
      have hi := BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top
        τ hd4 hp.2.2 a ha
      omega
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega
  · exact BinaryParabolicNatural.cover_injective_of_H1_zero p hp
      (BinaryParabolicNatural.dualSL_H1_zero (by omega))

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
