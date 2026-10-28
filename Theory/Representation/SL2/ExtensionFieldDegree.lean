module
public import Theory.Representation.BinaryResidualSection
public import Theory.Representation.NormalPKernelDescent
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Representation.SL2.TwoSubgroupFixedIndex

/-!
# Field-degree bounds through a normal binary kernel

When a finite actor maps onto SL₂(k) with two-group kernel, a moving
O²-action on a binary module has a moving irreducible section. The kernel
acts trivially on that section, and the SL₂ displacement bound therefore
bounds the fixed codimension in the original module. Neither faithfulness
of the original action nor trivial action of its two-core is assumed.

Source application: the first inequality in DGS, Groups and Graphs
(1985), proof of 10.7, p.159; the SL₂ bound is Niles (1979), Lemma 4.3.
-/

public noncomputable section

namespace Representation.SL2
open Subgroup BinaryOffender
open scoped MatrixGroups
variable {H F M : Type*} [Group H] [Finite H]
  [Field F] [Finite F] [CharP F 2]
  [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

/-- A moving residual survives passage to a simple section. The normal
binary kernel disappears there, so the same original actor has at least
the defining field degree of displacement. -/
theorem extension_fixedCodim_lower
    (π : H →* SL(2,F)) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) H M)
    (hmove : fixedSpace ρ (pResidual 2 H) ≠ ⊤)
    (A : Subgroup H) (hA : IsPGroup 2 (A.map π)) (hne : A.map π ≠ ⊥)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    n ≤ fixedCodim ρ A := by
  have hnot : ¬ pResidual 2 H ≤ ρ.ker := by
    intro hh
    apply hmove
    apply top_unique
    intro v _ a
    exact DFunLike.congr_fun (hh a.property) v
  obtain ⟨U,N,hi,hm⟩ := exists_irreducible_section_surviving_twoPerfect
    (pResidual 2 H) (isPPerfect_pResidual 2) hnot
  let := hi
  obtain ⟨τ,hτ,hτi⟩ := exists_irreducible_descent_of_pGroup_kernel
    N.quotientRepresentation π hπ hk
  have hτnt : ∃ g, τ g ≠ 1 := by
    by_contra! hh
    apply hm
    intro a ha
    rw [MonoidHom.mem_ker,←hτ a,hh]
  have hl := two_subgroup_fixedCodim_lower τ hτnt hn hF (A.map π) hA hne
  have he : τ.comp π = N.quotientRepresentation := MonoidHom.ext hτ
  have hcod : fixedCodim τ (A.map π) = fixedCodim N.quotientRepresentation A := by
    rw [←he,fixedCodim,fixedCodim,fixedSpace_comp_map]
  have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
  have hu := fixedCodim_subrepresentation_le ρ U A
  rw [hcod] at hl
  omega

end Representation.SL2
