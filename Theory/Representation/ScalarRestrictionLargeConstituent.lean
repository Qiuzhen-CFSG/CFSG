module
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Large simple constituents under scalar restriction

A simple constituent occupying more than half the restricted space is
stable under every coefficient scalar. Indeed, scalar multiplication
followed by projection to its quotient is an intertwiner from that simple
constituent; injectivity is impossible by dimension, so the map vanishes.
Irreducibility over the larger field then makes the constituent the whole
space. No semisimplicity of the group algebra is assumed.

This is the scalar version of the large-constituent argument in Clifford
theory (Isaacs, Character Theory, Theorem 6.5). The adjoint PSL₃(4) consumer
uses the binary degree gap nine and total binary dimension sixteen.
-/

open Representation
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation
variable {k F H V : Type*} [Field k] [Field F] [Algebra k F] [Group H]
  [AddCommGroup V] [Module F V] [Module k V] [IsScalarTower k F V]
  [FiniteDimensional k V]

/-- A simple constituent of more than half the dimension forces simplicity
after restricting the coefficient field. -/
theorem irreducible_restrictScalars_of_large_constituent
    (ρ : Representation F H V) [ρ.IsIrreducible]
    (W : Subrepresentation (restrictScalars (k := k) ρ))
    [W.toRepresentation.IsIrreducible]
    (hd : Module.finrank k V < 2 * Module.finrank k W.toSubmodule) :
    (restrictScalars (k := k) ρ).IsIrreducible := by
  let τ := restrictScalars (k := k) ρ
  have hsmul (c : F) (v : V) (hv : v ∈ W) : c • v ∈ W := by
    let σ := τ.quotient W.toSubmodule (fun h => W.apply_mem_toSubmodule h)
    let f : W.toRepresentation.IntertwiningMap σ :=
      ⟨W.toSubmodule.mkQ.comp
        (((c • LinearMap.id : V →ₗ[F] V).restrictScalars k).comp W.toSubmodule.subtype), by
        intro h
        apply LinearMap.ext
        intro w
        change W.toSubmodule.mkQ (c • ρ h w.val) =
          W.toSubmodule.mkQ (ρ h (c • w.val))
        rw [(ρ h).map_smul c w.val]⟩
    have hz : f = 0 := (IsIrreducible.injective_or_eq_zero f).resolve_left (by
      intro hi
      have hle := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hi
      have hq := W.toSubmodule.finrank_quotient_add_finrank
      omega)
    have he := congrArg (fun a : W.toRepresentation.IntertwiningMap σ => a ⟨v,hv⟩) hz
    exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp he
  let U : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := W
          zero_mem' := W.toSubmodule.zero_mem
          add_mem' := W.toSubmodule.add_mem
          smul_mem' := hsmul }
      apply_mem_toSubmodule := W.apply_mem_toSubmodule }
  have ha : IsAtom W := (Subrepresentation.irreducible_iff_isAtom W).mp inferInstance
  have hU : U ≠ ⊥ := by
    intro he
    apply ha.ne_bot
    ext v
    exact Iff.of_eq (congrArg (fun A : Subrepresentation ρ => v ∈ A) he)
  have ht : U = ⊤ := (eq_bot_or_eq_top U).resolve_left hU
  have hW : W = ⊤ := by
    ext v
    exact Iff.of_eq (congrArg (fun A : Subrepresentation ρ => v ∈ A) ht)
  exact isSimpleOrder_iff_isAtom_top.mpr (hW ▸ ha)
end Representation
