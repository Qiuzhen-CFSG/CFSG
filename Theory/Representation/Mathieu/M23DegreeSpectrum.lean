module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.Induction
public import Theory.Representation.Mathieu.SmallModules.M23Recognition

/-!
# Reducing the binary M23 spectrum to concrete induced modules

Choose a simple submodule of the restriction to the actual M22 point
stabilizer. The M22 small-degree gap leaves dimensions one and ten. A fixed
line gives a quotient of the permutation module, whose Golay filtration
identifies an eleven-dimensional code or cocode. In dimension ten, native
M22 recognition and Frobenius reciprocity give a quotient of one of the
explicit induced point modules, with the original marking retained.

The M22 gap and the simple quotients of these inductions remain explicit
inputs. This reduction does not assert the unconditional M23 spectrum.
All dimensions are over F2, and no absolute irreducibility or semisimplicity
of a restricted representation is assumed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
M23 paragraph on manuscript p.16; Aschbacher--Smith H.13.1 and K.4.
-/

@[expose] public noncomputable section
open Representation Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M23DegreeSpectrum
universe v

/-- The exact part of the independently owned M22 degree gap needed here.
The degree-thirty result supplies this by weakening the input bound. -/
def M22SmallDegree : Prop :=
  ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) M22 W),
    Function.Injective τ → τ.IsIrreducible →
    Module.finrank (ZMod 2) W ≤ 24 → Module.finrank (ZMod 2) W ≤ 12

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The independent M22 gap controls the simple modules of the literal
point stabilizer, retaining binary dimension. -/
theorem point_simple_degree (hgap : M22SmallDegree.{v})
    (τ : Representation (ZMod 2) Models.pointGroup V) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 10 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
  have hp : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  by_cases h : Module.finrank (ZMod 2) V = 1
  · exact Or.inl h
  let e := m23EquivM22PointStabilizer
  let σ : Representation (ZMod 2) M22 V := τ.comp e.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective τ).mpr inferInstance
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank σ (by omega)
  exact Or.inr (M22Recognition.of_small_degree σ hf (hgap σ hf inferInstance hd)).finrank

/-- Native recognition of a ten-dimensional point module, including the
marking returned by M22 recognition rather than replacing it by identity. -/
theorem point_equiv_of_degree_ten
    (τ : Representation (ZMod 2) Models.pointGroup V) [τ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V = 10) :
    ∃ (a : Models.pointGroup ≃* M22) (b : Bool),
      Nonempty (τ.Equiv (Models.pointAction a b)) := by
  let e := m23EquivM22PointStabilizer
  let σ : Representation (ZMod 2) M22 V := τ.comp e.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective τ).mpr inferInstance
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank σ (by omega)
  rcases M22Recognition.of_small_degree σ hf (by omega) with ⟨a, h | h⟩
  · obtain ⟨E⟩ := h
    refine ⟨e.symm.trans a, false, ⟨Representation.Equiv.mk E.toLinearEquiv ?_⟩⟩
    intro g
    simpa only [σ, Models.pointAction, Models.action, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
      using E.isIntertwining' (e.symm g)
  · obtain ⟨E⟩ := h
    refine ⟨e.symm.trans a, true, ⟨Representation.Equiv.mk E.toLinearEquiv ?_⟩⟩
    intro g
    simpa only [σ, Models.pointAction, Models.action, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
      using E.isIntertwining' (e.symm g)

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

/-- A genuine fixed line in the point restriction already forces degree
 eleven by the native Golay filtration; no degree-table input is used. -/
theorem finrank_eq_eleven_of_point_line (ρ : Representation (ZMod 2) M23 V)
    [ρ.IsIrreducible] (hd : 1 < Module.finrank (ZMod 2) V)
    (S : Subrepresentation (pointRestriction ρ))
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 1) :
    Module.finrank (ZMod 2) V = 11 := by
  have hfixed : (pointRestriction ρ).invariants ≠ ⊥ := by
    let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hS
    obtain ⟨w, hw⟩ := exists_ne (0 : S.toSubmodule)
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨w.val, ?_, fun hz => hw (Subtype.ext hz)⟩
    intro g
    exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hS g w)
  rcases M23Recognition.of_point_fixed ρ hd hfixed with h | h
  · obtain ⟨E⟩ := h
    exact E.toLinearEquiv.finrank_eq.trans finrank_code
  · obtain ⟨E⟩ := h
    exact E.toLinearEquiv.finrank_eq.trans finrank_cocode

/-- The head calculation is applied to the actual surjection constructed
from a ten-dimensional point submodule. -/
theorem finrank_eq_eleven_of_point_ten (hheads : SmallInducedHeads)
    (ρ : Representation (ZMod 2) M23 V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24)
    (S : Subrepresentation (pointRestriction ρ)) [S.toRepresentation.IsIrreducible]
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 10) :
    Module.finrank (ZMod 2) V = 11 := by
  obtain ⟨a, b, ⟨E⟩⟩ := point_equiv_of_degree_ten S.toRepresentation hS
  obtain ⟨f, hf⟩ := exists_surjective_induced_of_equiv ρ S a b E
  have h := hheads a b f.ker (SimpleHeadQuotient.isCoatom_ker_of_surjective f hf)
  have hdim := (f.toLinearMap.quotKerEquivOfSurjective hf).finrank_eq
  change Module.finrank (ZMod 2) (Models.InducedSpace a b ⧸ f.ker.toSubmodule) =
    Module.finrank (ZMod 2) V at hdim
  rw [hdim] at h
  omega

/-- Conditional assembly of the simple-M23 spectrum. Both independent
representation calculations are explicit and must be discharged. -/
theorem finrank_eq_eleven_of_inputs (hgap : M22SmallDegree.{v})
    (hheads : SmallInducedHeads) (ρ : Representation (ZMod 2) M23 V)
    (hf : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) : Module.finrank (ZMod 2) V = 11 := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 23) (by decide : 23 ≠ 2) (by rw [m23_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_twentyThree] at hlo
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨S, hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (pointRestriction ρ)
  let : S.toRepresentation.IsIrreducible := hS
  rcases point_simple_degree hgap S.toRepresentation
    ((Submodule.finrank_le S.toSubmodule).trans hd) with hline | hten
  · exact finrank_eq_eleven_of_point_line ρ (by omega) S hline
  · exact finrank_eq_eleven_of_point_ten hheads ρ hd S hten

end Representation.MathieuSmall.M23DegreeSpectrum
