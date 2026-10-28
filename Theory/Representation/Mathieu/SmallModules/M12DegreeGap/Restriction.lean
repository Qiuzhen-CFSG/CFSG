module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.Completeness
public import Theory.Representation.IrreducibleSimpleFaithful

/-!
# Simple submodules of the actual M₁₁ restriction

Choose a simple submodule of the restriction along `pointEmbedding`.
Given the explicit small simple-degree input, a line gives a fixed vector.
A ten-dimensional simple submodule is faithful by simplicity of M₁₁;
the existing classification identifies it with `pointRepresentation`.
Composing that equivalence with its inclusion constructs a nonzero marked
intertwiner. No complete reducibility of the restriction is assumed.

The degree alternatives remain an explicit premise, to be supplied by the
M₁₁ degree-gap proof. The induced-module consumer is in `M12DegreeGap`.
Source context: James, J. Algebra 27 (1973), 57–111; Aschbacher–Smith K.4,
printed p.457. This reduction does not assert the source classification.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap
open Sporadic.Mathieu M12Recognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem binary_line_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) M11 W)
    (hd : Module.finrank (ZMod 2) W = 1) (g : M11) (w : W) : τ g w = w := by
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

theorem point_fixed_or_point_map_of_simple_degrees
    (σ : Representation (ZMod 2) M12 V) [σ.IsIrreducible]
    (hlocal : ∀ S : Subrepresentation (σ.comp pointEmbedding),
      S.toRepresentation.IsIrreducible →
      Module.finrank (ZMod 2) S.toSubmodule = 1 ∨
        Module.finrank (ZMod 2) S.toSubmodule = 10) :
    Representation.invariants (σ.comp pointEmbedding) ≠ ⊥ ∨
      ∃ f : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding), f ≠ 0 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨S, hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (σ.comp pointEmbedding)
  let : S.toRepresentation.IsIrreducible := hS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  rcases hlocal S hS with hline | hten
  · left
    apply (Submodule.ne_bot_iff _).mpr
    refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
    intro g
    exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hline g v)
  · right
    let : IsSimpleGroup M11 := m11_isSimpleGroup
    have hf := injective_of_simple_of_irreducible_of_one_lt_finrank S.toRepresentation
      (by omega)
    obtain ⟨e⟩ := PointClassification.equiv_point_of_faithful_degree_ten S.toRepresentation hf hten
    let j : S.toRepresentation.IntertwiningMap (σ.comp pointEmbedding) :=
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    let f := j.comp e.symm.toIntertwiningMap
    refine ⟨f, ?_⟩
    intro hz
    have he := congrArg (fun k : pointRepresentation.IntertwiningMap (σ.comp pointEmbedding) =>
      k (e v)) hz
    change (e.symm (e v)).val = 0 at he
    have hvz : v.val = 0 := by simpa only [Representation.Equiv.symm_apply_apply] using he
    exact hv (Subtype.ext hvz)

end Representation.MathieuSmall.M12DegreeGap
