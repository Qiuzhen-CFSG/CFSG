module
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Cubic ratios on literal invariant sections

The same elementary cubic actor restricts to an invariant subspace and
acts on its quotient. Fixed codimension cannot increase in either step.
Consequently a finite cubic-ratio bound passes to these actual sections,
and it is unchanged by an isomorphism of the acting group. No faithfulness
or complete reducibility is needed for this transport.

Source: Aschbacher–Smith B.4.1 and the section step used in C.5.13, p.163.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G H V : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Cubic action restricts to the original invariant subspace. -/
theorem cubic_subrepresentation (U : Subrepresentation ρ) {A : Subgroup G}
    (h : IsCubic ρ A) : IsCubic U.toRepresentation A := by
  intro a ha b hb c hc v
  exact Subtype.ext (h a ha b hb c hc v)

/-- Cubic action descends to the original invariant quotient. -/
theorem cubic_quotient (U : Subrepresentation ρ) {A : Subgroup G}
    (h : IsCubic ρ A) : IsCubic U.quotientRepresentation A := by
  intro a ha b hb c hc v
  obtain ⟨w,rfl⟩ := U.toSubmodule.mkQ_surjective v
  exact congrArg U.toSubmodule.mkQ (h a ha b hb c hc w)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- An invariant submodule inherits any integral cubic-ratio bound. -/
theorem cubicRatio_subrepresentation_le_nat (U : Subrepresentation ρ) (n : ℕ)
    (h : cubicRatio ρ ≤ n) : cubicRatio U.toRepresentation ≤ n := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff ρ n).mp h
  exact (cubicRatio_le_nat_iff _ n).mpr ⟨A,hA,cubic_subrepresentation ρ U hc,
    (fixedCodim_subrepresentation_le ρ U A).trans hd⟩

/-- An invariant quotient inherits any integral cubic-ratio bound. -/
theorem cubicRatio_quotient_le_nat (U : Subrepresentation ρ) (n : ℕ)
    (h : cubicRatio ρ ≤ n) : cubicRatio U.quotientRepresentation ≤ n := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff ρ n).mp h
  refine (cubicRatio_le_nat_iff _ n).mpr ⟨A,hA,cubic_quotient ρ U hc,?_⟩
  have hh := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Group isomorphisms preserve the actual cubic actor and its rank. -/
theorem cubicRatio_comp_equiv_le_nat (e : H≃*G) (n : ℕ)
    (h : cubicRatio ρ ≤ n) : cubicRatio (ρ.comp e.toMonoidHom) ≤ n := by
  let : Finite H := Finite.of_equiv G e.toEquiv.symm
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff ρ n).mp h
  let B := A.map e.symm.toMonoidHom
  have he : B.map e.toMonoidHom=A := by
    rw [map_map]
    simp
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hz
    exact hA.1 (by rw [←he,hz,Subgroup.map_bot])
  have hr : rank B=rank A := by
    rw [←rank_map_injective e.toMonoidHom e.injective,he]
  refine (cubicRatio_le_nat_iff _ n).mpr ⟨B,hB,?_,?_⟩
  · intro a ha b hb c hce v
    exact hc (e a) (he ▸ mem_map_of_mem _ ha) (e b) (he ▸ mem_map_of_mem _ hb)
      (e c) (he ▸ mem_map_of_mem _ hce) v
  · have hf : fixedCodim (ρ.comp e.toMonoidHom) B=fixedCodim ρ A := by
      unfold fixedCodim
      rw [fixedSpace_comp_map,he]
    rwa [hf,hr]

end Representation.BinaryOffender
