module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.Restriction

/-!
# The nine-subspace branch through degree seventeen

A nonzero quotient of dimension less than nine has a simple quotient of
binary dimension one. Pulling its nonzero functional back to the original
module gives a fixed covector. For an M22 restriction containing a
nine-dimensional invariant subspace, this closes dimensions ten through
seventeen, including sixteen, without splitting the restriction.

This is a small-range ingredient for the degree-table step in
Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1, pp.15–16;
see also Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
The degree-thirty branch requires additional representation calculations.
-/

public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule

private theorem binary_line_fixed {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (τ : Representation (ZMod 2) G W)
    (hd : Module.finrank (ZMod 2) W = 1) (g : G) (w : W) : τ g w = w := by
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hw (τ g w)
  have hc0 : c ≠ 0 := by
    intro hz
    have hgw : τ g w = 0 := by simpa [hz] using hc.symm
    apply hw
    simpa only [τ.inv_self_apply, map_zero] using congrArg (τ g⁻¹) hgw
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1, one_smul] using hc.symm

private theorem dual_fixed_of_small_dimension
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) W)
    (hpos : 0 < Module.finrank (ZMod 2) W)
    (hd : Module.finrank (ZMod 2) W < 9) : τ.dual.invariants ≠ ⊥ := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
  let : IsCoatomic (Subrepresentation τ) := SimpleHeadQuotient.subrepresentation_coatomic τ
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation τ)
  let : N.quotientRepresentation.IsIrreducible :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  have hq := point_simple_degree N.quotientRepresentation (by omega)
  have hline : Module.finrank (ZMod 2) (W ⧸ N.toSubmodule) = 1 := by omega
  let : Nontrivial (W ⧸ N.toSubmodule) := Module.nontrivial_of_finrank_eq_succ hline
  obtain ⟨q, hq⟩ := exists_ne (0 : W ⧸ N.toSubmodule)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let l : Module.Dual (ZMod 2) W := f.comp N.toSubmodule.mkQ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨l, ?_, ?_⟩
  · intro g
    ext v
    change f (N.quotientRepresentation g⁻¹ (N.toSubmodule.mkQ v)) =
      f (N.toSubmodule.mkQ v)
    rw [binary_line_fixed N.quotientRepresentation hline]
  · intro hz
    obtain ⟨v, hv⟩ := N.toSubmodule.mkQ_surjective q
    have hl : l v = 1 := by change f (N.toSubmodule.mkQ v) = 1; rw [hv, hf]
    rw [hz] at hl
    exact zero_ne_one hl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- A nine-dimensional invariant subspace in a restriction of degree ten
through seventeen gives an actual fixed covector, even for nonsplit extensions. -/
theorem dual_fixed_of_le_seventeen
    (τ : Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) V)
    (S : Subrepresentation τ) (hS : Module.finrank (ZMod 2) S.toSubmodule = 9)
    (hlo : 10 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 17) : τ.dual.invariants ≠ ⊥ := by
  have hsum := S.toSubmodule.finrank_quotient_add_finrank
  have hfixed := dual_fixed_of_small_dimension S.quotientRepresentation (by omega) (by omega)
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).mp hfixed
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨f.comp S.toSubmodule.mkQ, ?_, ?_⟩
  · intro g
    ext v
    exact congrArg (fun l : Module.Dual (ZMod 2) (V ⧸ S.toSubmodule) =>
      l (S.toSubmodule.mkQ v)) (hf g)
  · intro hz
    apply hf0
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective w
    exact congrArg (fun l : Module.Dual (ZMod 2) V => l v) hz

/-- This point-submodule branch is closed through seventeen, including sixteen. -/
theorem finrank_eq_ten_of_le_seventeen
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 17)
    (S : Subrepresentation (pointRestriction σ))
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 9) :
    Module.finrank (ZMod 2) V = 10 := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  exact (M22Recognition.of_point_fixed_or_dual σ (by omega)
    (Or.inr (dual_fixed_of_le_seventeen (pointRestriction σ) S hS hlo hd))).finrank

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule
