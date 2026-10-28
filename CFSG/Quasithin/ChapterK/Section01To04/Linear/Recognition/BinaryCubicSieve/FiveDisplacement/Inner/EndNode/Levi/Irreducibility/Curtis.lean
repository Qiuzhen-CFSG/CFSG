module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis.Cyclicity
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.Quotient

/-!
# The binary Curtis fixed-line and opposite-orbit theorem

Every finite-dimensional irreducible representation of SL₅(2) over F₂
has a unique lower-unipotent fixed line, and its upper-unipotent translates
span the module. Graph twisting reverses the previously proved cyclicity.
For uniqueness, apply cyclicity to the contragredient: evaluation on its
cyclic vector injects the original fixed space into the coefficient field.

This proves precisely `CurtisInput` on the subgroups of `GeometryData`,
including the trivial irreducible representation. No algebraic closure,
absolute irreducibility, module list, or degree restriction is needed.

Source: the first assertion of GLS, Volume 3, Theorem 2.8.9, printed p.94,
and its use in Theorem 2.8.11, pp.95–96, `refs/KGroup/GLS3/chapter2.tex`.
See `Curtis/Source.md` for the distinction from the source's coefficient
field and the proof over the original binary field.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility
open Representation BinaryLinear.OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
namespace Curtis

/-- Graph twisting gives cyclicity in the orientation used by the parabolic consumer. -/
theorem exists_lower_fixed_upper_cyclic [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) [IsIrreducible σ] :
    ∃ z : V, z ≠ 0 ∧ z ∈ invariants (σ.comp lower.subtype) ∧
      Submodule.span (ZMod 2) (Set.range fun u : upper => σ u z) = ⊤ := by
  let τ := σ.comp (graphSL 5).toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff (graphSL 5).toMonoidHom (graphSL 5).surjective σ).mpr
      inferInstance
  obtain ⟨z,hz0,hz,hspan⟩ := exists_upper_fixed_lower_cyclic τ
  refine ⟨z,hz0,?_,?_⟩
  · intro u
    obtain ⟨a,ha,he⟩ := u.property
    change σ u.val z = z
    rw [← he]
    exact hz ⟨a,ha⟩
  · apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨u,rfl⟩
    obtain ⟨a,ha,he⟩ := u.property
    change σ (graphSL 5 u.val) z ∈ _
    change graphSL 5 a = u.val at he
    rw [← he, graph_involution]
    exact Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩

/-- Evaluation on a cyclic dual vector separates fixed vectors. -/
theorem fixed_eq_zero_of_eval_eq_zero
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (φ : Module.Dual (ZMod 2) V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun u : lower => σ.dual u φ) = ⊤)
    {x : V} (hx : x ∈ invariants (σ.comp lower.subtype)) (heval : φ x = 0) : x = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp
  intro f
  have hf : f ∈ Submodule.span (ZMod 2) (Set.range fun u : lower => σ.dual u φ) := by
    rw [hspan]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u,rfl⟩ := hf
    change φ (σ u.val⁻¹ x) = 0
    have hu : σ u.val⁻¹ x = x := hx u⁻¹
    rw [hu,heval]
  | zero => rfl
  | add f g _ _ hf hg =>
    change f x + g x = 0
    rw [hf,hg,add_zero]
  | smul a f _ hf =>
    change a * f x = 0
    rw [hf,mul_zero]

/-- Dual opposite-unipotent cyclicity bounds the fixed space by any nonzero fixed line. -/
theorem fixed_le_line_of_dual_cyclic
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (φ : Module.Dual (ZMod 2) V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun u : lower => σ.dual u φ) = ⊤)
    {z : V} (hz0 : z ≠ 0) (hz : z ∈ invariants (σ.comp lower.subtype)) :
    invariants (σ.comp lower.subtype) ≤ Submodule.span (ZMod 2) {z} := by
  have hφz : φ z ≠ 0 := fun h => hz0 (fixed_eq_zero_of_eval_eq_zero σ φ hspan hz h)
  have hφz1 : φ z = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hφz
  intro x hx
  have heval : φ (x - φ x • z) = 0 := by
    rw [map_sub, map_smul, hφz1, smul_eq_mul, mul_one, sub_self]
  have hzero : x - φ x • z = 0 := fixed_eq_zero_of_eval_eq_zero σ φ hspan
    ((invariants (σ.comp lower.subtype)).sub_mem hx
      ((invariants (σ.comp lower.subtype)).smul_mem _ hz)) heval
  exact Submodule.mem_span_singleton.mpr ⟨φ x, (sub_eq_zero.mp hzero).symm⟩
end Curtis

/-- Binary Curtis fixed-line uniqueness and opposite-unipotent cyclicity, including the trivial module. -/
theorem curtisInput [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) [IsIrreducible σ] : CurtisInput σ := by
  obtain ⟨z,hz0,hz,hspan⟩ := Curtis.exists_lower_fixed_upper_cyclic σ
  let : IsIrreducible σ.dual := isIrreducible_dual
  obtain ⟨φ,_,_,hdual⟩ := Curtis.exists_upper_fixed_lower_cyclic σ.dual
  exact ⟨z,hz0,hz,Curtis.fixed_le_line_of_dual_cyclic σ φ hdual hz0 hz,hspan⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility
