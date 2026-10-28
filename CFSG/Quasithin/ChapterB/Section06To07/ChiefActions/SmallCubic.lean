module
public import Theory.SpecificGroups.SymmetricFive.OuterActorCubicSelection
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# The selected cubic for an actual natural S₅ chief action

The natural five-point action has no strong offenders. Every offender is
therefore one of the actual disjoint-transposition subgroups of B.3.2 and
contains an odd permutation. The concrete S₅ cubic selection consequently
applies to that same offender and prescribed Sylow subgroup. Transport uses
the specified action equivalence, retaining all subgroup positions and the
commutator and generation identities needed by the source lifting argument.

Source: Aschbacher–Smith, 3.1.9(5) and 15.1.12(4), using B.3.2.
-/
public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Equiv Representation.BinaryOffender QuasisimpleSource Offenders

/-- Every offender on the genuine natural S₅ module contains an odd permutation. -/
theorem natural_five_offender_outer (A : Subgroup (Perm (Fin 5)))
    (hA : IsOffender (BinaryPermutation.naturalRepresentation (Fin 5)) A) :
    ¬ A ≤ alternatingGroup (Fin 5) := by
  have hstrong : ¬ IsStrongFFModule (BinaryPermutation.naturalRepresentation (Fin 5)) := by
    rintro ⟨B,hB⟩
    exact Odd.not_isStrongOffender_natural (Or.inl rfl) B hB
  have hbest := (isBestOffender_iff_of_not_strong _ hstrong A).mpr
    ⟨hA.1,le_antisymm hA.2 (Nat.le_of_not_gt (fun h => hstrong ⟨A,hA.1,h⟩))⟩
  obtain ⟨m,hm,_,g,rfl⟩ :=
    (Odd.isBestOffender_natural_iff_caseAFamily (Or.inl rfl) A).mp hbest
  intro hle
  have hmem := hle (mem_map_of_mem (MulAut.conj g).toMonoidHom (pairSwap_mem 0 hm))
  have hsign : ((MulAut.conj g) (pairSwap 5 0)).sign = -1 := by
    change (g * (swap (0 : Fin 5) 1) * g⁻¹).sign = -1
    simp [Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1),mul_comm]
  have hh := Perm.mem_alternatingGroup.mp hmem
  change ((MulAut.conj g) (pairSwap 5 0)).sign = 1 at hh
  rw [hsign] at hh
  exact (by decide : (-1 : ℤˣ) ≠ 1) hh

/-- The actual natural action selects a cubic using the original offender,
with every premise of the source normalizer lift discharged. -/
theorem five_action_cubic_selection {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G)) (hA : IsOffender ρ A)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin 5))) :
    ∃ L R : Subgroup G, Nat.card L=3 ∧ R ≤ A ∧ R.relIndex A=2 ∧
      A ≤ normalizer (R : Set G) ∧ L ≤ centralizer (R : Set G) ∧
      A ≤ normalizer (L : Set G) ∧ L=⁅L,A⁆ ∧ L ⊔ (S : Subgroup G)=⊤ := by
  let : IsElementaryAbelian 2 A := hA.1.2
  have hmodel := hA.map_equivariant ρ (BinaryPermutation.naturalRepresentation (Fin 5))
    e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  exact Theory.SpecificGroups.SymmetricFive.CubicSelection.exists_outer_actor_selection_of_equiv
    e.groupEquiv S A hAS (natural_five_offender_outer _ hmodel)
end CFSG.Quasithin.ChapterB
