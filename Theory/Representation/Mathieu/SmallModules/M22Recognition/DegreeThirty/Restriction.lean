module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.PointSimpleDegrees

/-!+# The two nontrivial point-restriction branches through degree thirty

Choose a simple submodule of the restriction to the native point stabilizer.
Transport through its actual PSL(3,4) identification. The binary simple-degree
calculation leaves degrees one, nine and sixteen. A one-dimensional binary
submodule is a fixed line, so the permutation-module recognition theorem forces
the original irreducible M22 module to have dimension ten. This leaves the
nine- and sixteen-dimensional submodule branches, with their actual inclusions.
No complete reducibility of the restriction is used.

Source context: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16, and Theorem 6.6/Table 6.7; Aschbacher–Smith, Chapter K, pp.451–452
and 457. This is a reduction of the degree gap, not its final proof.
-/

public noncomputable section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Restriction along the inclusion of the stabilizer of the native point zero. -/
abbrev pointRestriction (σ : Representation (ZMod 2) M22 V) :
    Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) V :=
  σ.comp (MulAction.stabilizer M22 (0 : Fin 22)).subtype

/-- Binary simple degrees through thirty for the literal native stabilizer. -/
theorem point_simple_degree [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) V)
    [τ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 9 ∨
      Module.finrank (ZMod 2) V = 16 := by
  let e := MathieuCode.m22PointStabilizerEquiv 0
  let τ' : Representation (ZMod 2) Matrix.PSL3Four.PSL V := τ.comp e.symm.toMonoidHom
  let : τ'.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  exact PointSimpleDegrees.simple_degree τ' hd

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

/-- Through dimension seventeen, except dimension sixteen itself, a native
point-stabilizer module above degree nine has a fixed vector or covector.
The simple quotient argument retains arbitrary nonsplit extensions. -/
theorem point_fixed_or_dual_of_le_seventeen [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) (MulAction.stabilizer M22 (0 : Fin 22)) V)
    (hlo : 10 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 17)
    (hne : Module.finrank (ZMod 2) V ≠ 16) :
    τ.invariants ≠ ⊥ ∨ τ.dual.invariants ≠ ⊥ := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) V)
  let : IsCoatomic (Subrepresentation τ) := SimpleHeadQuotient.subrepresentation_coatomic τ
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation τ)
  let : N.quotientRepresentation.IsIrreducible :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  have hq := point_simple_degree N.quotientRepresentation (by omega)
  rcases hq with hline | hlarge
  · right
    let : Nontrivial (V ⧸ N.toSubmodule) := Module.nontrivial_of_finrank_eq_succ hline
    obtain ⟨q, hq⟩ := exists_ne (0 : V ⧸ N.toSubmodule)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
    let l : Module.Dual (ZMod 2) V := f.comp N.toSubmodule.mkQ
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
  · left
    have hNpos : 0 < Module.finrank (ZMod 2) N.toSubmodule := by omega
    let : Nontrivial N.toSubmodule := Module.nontrivial_of_finrank_pos hNpos
    obtain ⟨S, hS⟩ :=
      Subrepresentation.irreducible_subrepresentation_of_finite_dimensional N.toRepresentation
    let : S.toRepresentation.IsIrreducible := hS
    have hSle := Submodule.finrank_le S.toSubmodule
    have hdS := point_simple_degree S.toRepresentation (by omega)
    have hSone : Module.finrank (ZMod 2) S.toSubmodule = 1 := by omega
    let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hSone
    obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨v.val.val, ?_, fun hz => hv (Subtype.ext (Subtype.ext hz))⟩
    intro g
    exact congrArg (fun w : S.toSubmodule => w.val.val)
      (binary_line_fixed S.toRepresentation hSone g v)

/-- The M22 degree gap is unconditional through seventeen, with only sixteen
left open in that range. -/
theorem finrank_eq_ten_of_le_seventeen_of_ne_sixteen [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 17)
    (hne : Module.finrank (ZMod 2) V ≠ 16) : Module.finrank (ZMod 2) V = 10 := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  exact (M22Recognition.of_point_fixed_or_dual σ (by omega)
    (point_fixed_or_dual_of_le_seventeen (pointRestriction σ) hlo hd hne)).finrank

/-- Every module in the M22 window is ten-dimensional or has an actual simple
point-stabilizer submodule of dimension nine or sixteen. -/
theorem finrank_eq_ten_or_point_submodule [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30) :
    Module.finrank (ZMod 2) V = 10 ∨
      ∃ S : Subrepresentation (pointRestriction σ), S.toRepresentation.IsIrreducible ∧
        (Module.finrank (ZMod 2) S.toSubmodule = 9 ∨
          Module.finrank (ZMod 2) S.toSubmodule = 16) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨S, hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (pointRestriction σ)
  let : S.toRepresentation.IsIrreducible := hS
  rcases point_simple_degree S.toRepresentation ((Submodule.finrank_le S.toSubmodule).trans hd)
    with hline | hlarge
  · left
    have hfixed : (pointRestriction σ).invariants ≠ ⊥ := by
      let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hline
      obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
      apply (Submodule.ne_bot_iff _).mpr
      refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
      intro g
      exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hline g v)
    have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
      (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
    rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
    exact (M22Recognition.of_point_fixed σ (by omega) hfixed).finrank
  · exact Or.inr ⟨S, hS, hlarge⟩

end Representation.MathieuSmall.M22Recognition.DegreeThirty
