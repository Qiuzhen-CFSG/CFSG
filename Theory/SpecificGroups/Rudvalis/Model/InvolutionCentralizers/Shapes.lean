module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The two Rudvalis centralizer shapes

The first shape retains actual successive normal kernels and quotient
isomorphisms. Extension notation does not assert a splitting. The second
carrier uses Suzuki parameter 1, hence field order 2^(2*1+1) = 8.
Transport of the first shape maps both normal kernels along the given
isomorphism and its induced quotient isomorphism.

These definitions assert no centralizer table. Their concrete witnesses
remain the marked max6 and C(a) calculations in the final assembly.
Source: Aschbacher–Smith, 16.1.5(11), printed p.1172; GLS3 Table 5.3r.
-/

@[expose] public section

open Subgroup
namespace Rudvalis.InvolutionCentralizers

/-- The literal centralizer of an element of the degree-4060 carrier. -/
abbrev Centralizer (t : Model) := centralizer ({t} : Set Model)
/-- The elementary abelian two-group of order 2ⁿ. -/
abbrev Elementary (n : ℕ) := Fin n → Multiplicative (ZMod 2)
/-- The Suzuki matrix carrier over GF(8), with parameter m = 1. -/
noncomputable abbrev SzEight := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1

/-- The successive normal kernels in S₅/E₆₄/E₃₂, with no splitting assertion. -/
def FirstShape (C : Type*) [Group C] : Prop :=
  ∃ (N : Subgroup C) (_ : N.Normal), Nonempty (N ≃* Elementary 5) ∧
    ∃ (P : Subgroup (C ⧸ N)) (_ : P.Normal),
      Nonempty (P ≃* Elementary 6) ∧
      Nonempty (((C ⧸ N) ⧸ P) ≃* Equiv.Perm (Fin 5))

/-- Transport both normal kernels and both literal quotient identifications. -/
theorem FirstShape.of_equiv {G H : Type*} [Group G] [Group H]
    (h : FirstShape G) (e : G ≃* H) : FirstShape H := by
  obtain ⟨N, hN, ⟨eN⟩, P, hP, ⟨eP⟩, ⟨eQ⟩⟩ := h
  let N' := N.map e.toMonoidHom
  let : N'.Normal := hN.map e.toMonoidHom e.surjective
  let q : (G ⧸ N) ≃* (H ⧸ N') := QuotientGroup.congr N N' e rfl
  let P' := P.map q.toMonoidHom
  let : P'.Normal := hP.map q.toMonoidHom q.surjective
  refine ⟨N', inferInstance, ⟨(e.subgroupMap N).symm.trans eN⟩,
    P', inferInstance, ⟨(q.subgroupMap P).symm.trans eP⟩,
    ⟨(QuotientGroup.congr P P' q rfl).symm.trans eQ⟩⟩

end Rudvalis.InvolutionCentralizers
