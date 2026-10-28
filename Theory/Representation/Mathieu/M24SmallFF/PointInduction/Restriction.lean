module
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty

/-!
# Simple constituents of the native M23 point restriction

A simple submodule of the actual restriction of a binary M24 representation
of dimension at most 24 is a line or has dimension eleven. The nonline
case is faithful by simplicity of M23. The unconditional M22 degree-thirty
bound and concrete induced-head calculation give the M23 degree gap, and
whole-action recognition identifies the actual code or cocode with identity
marking. Composing its inverse with the socle inclusion gives a nonzero
intertwiner into the original restriction. No splitting is assumed.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1;
Aschbacher–Smith, H.13.1 and K.4.
-/

public section
open Representation Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M24SmallFF.PointInduction
universe v
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem point_simple_degree (τ : Representation (ZMod 2) M23 V)
    [τ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 11 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
  have hp : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  by_cases hl : Module.finrank (ZMod 2) V = 1
  · exact Or.inl hl
  let : IsSimpleGroup M23 := m23_isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank τ (by omega)
  have hgap : M23DegreeSpectrum.M22SmallDegree.{v} := by
    intro W _ _ _ ρ hρ hi hd
    let := hi
    exact M22Recognition.DegreeThirty.finrank_le_twelve_of_le_thirty ρ hρ (hd.trans (by decide))
  exact Or.inr (M23DegreeSpectrum.finrank_eq_eleven_of_inputs hgap
    M23DegreeSpectrum.smallInducedHeads τ hf hd)

private theorem binary_line_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) M23 W)
    (hd : Module.finrank (ZMod 2) W = 1) (g : M23) (w : W) : τ g w = w := by
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

theorem point_fixed_or_native_map
    (σ : Representation (ZMod 2) M24 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 24) :
    Representation.invariants (σ.comp pointEmbedding) ≠ ⊥ ∨
      (∃ f : m23CodeRepresentation.IntertwiningMap (σ.comp pointEmbedding), f ≠ 0) ∨
      (∃ f : m23CocodeRepresentation.IntertwiningMap (σ.comp pointEmbedding), f ≠ 0) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨S,hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (σ.comp pointEmbedding)
  let : S.toRepresentation.IsIrreducible := hS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
  rcases point_simple_degree S.toRepresentation ((Submodule.finrank_le S.toSubmodule).trans hd)
    with hline | heleven
  · left
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
    intro g
    exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hline g v)
  · right
    let j : S.toRepresentation.IntertwiningMap (σ.comp pointEmbedding) :=
      ⟨S.toSubmodule.subtype,fun _ => rfl⟩
    rcases M23Recognition.equiv_code_or_cocode_of_degree_eleven S.toRepresentation heleven with h | h
    · obtain ⟨e⟩ := h
      left
      refine ⟨j.comp e.symm.toIntertwiningMap,?_⟩
      intro hz
      have he := congrArg (fun k : m23CodeRepresentation.IntertwiningMap (σ.comp pointEmbedding) =>
        k (e v)) hz
      change (e.symm (e v)).val = 0 at he
      exact hv (Subtype.ext (by simpa only [Representation.Equiv.symm_apply_apply, Submodule.coe_zero] using he))
    · obtain ⟨e⟩ := h
      right
      refine ⟨j.comp e.symm.toIntertwiningMap,?_⟩
      intro hz
      have he := congrArg (fun k : m23CocodeRepresentation.IntertwiningMap (σ.comp pointEmbedding) =>
        k (e v)) hz
      change (e.symm (e v)).val = 0 at he
      exact hv (Subtype.ext (by simpa only [Representation.Equiv.symm_apply_apply, Submodule.coe_zero] using he))
end Representation.MathieuSmall.M24SmallFF.PointInduction
