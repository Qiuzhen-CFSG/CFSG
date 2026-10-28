module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.SixSpace.Inputs
public import Theory.Representation.SimpleHeadQuotient

/-!
# Fixed vectors or covectors in the restricted six-space

Take a simple quotient of the point-stabilizer module. A quotient of dimension
one gives a fixed covector. A quotient of dimension four leaves a kernel of
dimension two; a simple submodule of that kernel has dimension one and gives
a fixed vector. No semisimplicity of the restriction is assumed.

The actual orbit-map consumer is `sevenSixSpace_of_pointSimpleDegrees`.
Source: the six-dimensional branch of Aschbacher–Smith K.1.2, printed p.452.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
universe v

private theorem binary_line_fixed {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) G W)
    (hd : Module.finrank (ZMod 2) W = 1) (g : G) (w : W) : σ g w = w := by
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

private theorem fixed_of_line_subrepresentation {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (S : Subrepresentation ρ) (hd : Module.finrank (ZMod 2) S.toSubmodule = 1) :
    ρ.invariants ≠ ⊥ := by
  let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
  intro g
  exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hd g v)

private theorem dual_fixed_of_line_quotient {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (N : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) (W ⧸ N.toSubmodule) = 1) :
    ρ.dual.invariants ≠ ⊥ := by
  let : Nontrivial (W ⧸ N.toSubmodule) := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨q, hq⟩ := exists_ne (0 : W ⧸ N.toSubmodule)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let l : Module.Dual (ZMod 2) W := f.comp N.toSubmodule.mkQ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨l, ?_, ?_⟩
  · intro g
    ext w
    change f (N.quotientRepresentation g⁻¹ (N.toSubmodule.mkQ w)) =
      f (N.toSubmodule.mkQ w)
    rw [binary_line_fixed N.quotientRepresentation hd]
  · intro hz
    obtain ⟨w, hw⟩ := N.toSubmodule.mkQ_surjective q
    have hl : l w = 1 := by change f (N.toSubmodule.mkQ w) = 1; rw [hw, hf]
    rw [hz] at hl
    exact zero_ne_one hl

/-- The simple-degree gap supplies a fixed vector or covector in the literal
point-stabilizer restriction, including nonsplit modules. -/
theorem fixed_or_dual (hdegrees : PointSimpleDegrees.{v})
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (τ : Representation (ZMod 2) PointStabilizer V)
    (hd : Module.finrank (ZMod 2) V = 6) :
    τ.invariants ≠ ⊥ ∨ τ.dual.invariants ≠ ⊥ := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) V)
  let : IsCoatomic (Subrepresentation τ) := SimpleHeadQuotient.subrepresentation_coatomic τ
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation τ)
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  have hq := hdegrees N.quotientRepresentation
    (SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN) (by omega)
  rcases hq with hq | hq
  · exact Or.inr (dual_fixed_of_line_quotient τ N hq)
  have hNdim : Module.finrank (ZMod 2) N.toSubmodule = 2 := by omega
  let : Nontrivial N.toSubmodule := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) N.toSubmodule)
  obtain ⟨S, hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional N.toRepresentation
  have hSle : Module.finrank (ZMod 2) S.toSubmodule ≤ 2 := by
    simpa only [hNdim] using Submodule.finrank_le S.toSubmodule
  have hSdim : Module.finrank (ZMod 2) S.toSubmodule = 1 :=
    (hdegrees S.toRepresentation hS (by omega)).resolve_right (by omega)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fixed_of_line_subrepresentation N.toRepresentation S hSdim)
  left
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨w.val, ?_, fun hz => hw0 (Subtype.ext hz)⟩
  intro g
  exact congrArg Subtype.val (hw g)

end CFSG.Quasithin.ChapterK.Alternating.SevenSixSpace
