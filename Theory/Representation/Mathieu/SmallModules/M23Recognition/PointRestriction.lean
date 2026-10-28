module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition
public import Theory.Representation.IrreducibleSimpleFaithful

/-!
# Fixed vectors in eleven-dimensional modules of the M23 point stabilizer

The existing native M22 recognition theorem and simplicity imply that every
binary simple M22 module of degree at most eleven has dimension one or ten.
Transport this degree gap along the actual isomorphism from M22 to the
stabilizer of point 9 in the native 23-point action.

A simple quotient of an eleven-dimensional module therefore has dimension
one or ten. In the first case its dual embeds as a fixed line; in the second
case the kernel is itself a fixed line. This retains nonsplit extensions and
requires neither faithfulness nor irreducibility of the restricted module.
The result supplies the local input to `M23Recognition.of_degree_eleven`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.4 opening,
printed p.457 (PDF p.468), and H.13.1--2, printed p.395. The small M22
completeness theorem used here is the James input to G.7.3(2), printed p.348;
see G. D. James, J. Algebra 27 (1973), 57--111.
-/

public section
open Representation Sporadic.Mathieu

namespace Representation.MathieuSmall.M23Recognition.PointRestriction
variable {G : Type*} [Group G]

private theorem binary_line_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (hd : Module.finrank (ZMod 2) W = 1)
    (g : G) (w : W) : σ g w = w := by
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hw (σ g w)
  have hc0 : c ≠ 0 := by
    intro hz
    have hgw : σ g w = 0 := by simpa [hz] using hc.symm
    apply hw
    simpa only [σ.inv_self_apply, map_zero] using congrArg (σ g⁻¹) hgw
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1, one_smul] using hc.symm

private theorem fixed_of_line_subrepresentation {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (S : Subrepresentation ρ) (hd : Module.finrank (ZMod 2) S.toSubmodule = 1) :
    ρ.invariants ≠ ⊥ := by
  let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
  intro g
  exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hd g v)

private theorem dual_fixed_of_line_quotient {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (N : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) = 1) :
    ρ.dual.invariants ≠ ⊥ := by
  let : Nontrivial (V ⧸ N.toSubmodule) := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨q, hq⟩ := exists_ne (0 : V ⧸ N.toSubmodule)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let l : Module.Dual (ZMod 2) V := f.comp N.toSubmodule.mkQ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨l, ?_, ?_⟩
  · intro g
    ext v
    change f (N.quotientRepresentation g⁻¹ (N.toSubmodule.mkQ v)) =
      f (N.toSubmodule.mkQ v)
    rw [binary_line_fixed N.quotientRepresentation hd]
  · intro hz
    obtain ⟨v, hv⟩ := N.toSubmodule.mkQ_surjective q
    have hl : l v = 1 := by change f (N.toSubmodule.mkQ v) = 1; rw [hv, hf]
    rw [hz] at hl
    exact zero_ne_one hl

/-- The binary simple degrees at most eleven for the actual M22 are one and ten. -/
theorem simple_degree {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) M22 W)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) W ≤ 11) :
    Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 10 := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  have hp : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos
  by_cases h : Module.finrank (ZMod 2) W = 1
  · exact Or.inl h
  right
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank σ (by omega)
  exact (M22Recognition.of_small_degree σ hf (by omega)).finrank

/-- Every eleven-dimensional module of the native M23 point stabilizer has a
fixed vector or fixed covector, including nonsplit extensions. -/
theorem fixed_or_dual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (MulAction.stabilizer M23 (9 : Fin 23)) V)
    (hd : Module.finrank (ZMod 2) V = 11) :
    ρ.invariants ≠ ⊥ ∨ ρ.dual.invariants ≠ ⊥ := by
  have hdegrees (W : Type _) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W]
      (σ : Representation (ZMod 2) (MulAction.stabilizer M23 (9 : Fin 23)) W)
      (hσ : σ.IsIrreducible) (hW : Module.finrank (ZMod 2) W ≤ 11) :
      Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 10 := by
    let e := m23EquivM22PointStabilizer
    let σ' : Representation (ZMod 2) M22 W := σ.comp e.toMonoidHom
    let : σ'.IsIrreducible :=
      (irreducible_comp_surjective_iff e.toMonoidHom e.surjective σ).mpr hσ
    exact simple_degree σ' hW
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) V)
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  have hq := hdegrees _ N.quotientRepresentation
    (SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN) (by omega)
  rcases hq with hq | hq
  · exact Or.inr (dual_fixed_of_line_quotient ρ N hq)
  exact Or.inl (fixed_of_line_subrepresentation ρ N (by omega))

end Representation.MathieuSmall.M23Recognition.PointRestriction
