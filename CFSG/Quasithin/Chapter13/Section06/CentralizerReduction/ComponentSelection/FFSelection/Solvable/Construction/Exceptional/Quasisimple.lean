module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Action
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The quasisimple branch of the solvable construction

For a nontrivial solvable normal subgroup A with [A,C] = A, all four
clauses of B.5.1(1) are incompatible with the quasisimple alternative.
When F*(D) = D, quasisimplicity makes A central. In the outer-natural
cases the actual action equivalence identifies D with S_n (n ≥ 5) or
G₂(2); every nontrivial normal subgroup contains a nontrivial perfect
subgroup, so A is trivial. No centrality in D is inferred from
quasisimplicity of F*(D) alone.

The final application restricts the original minimal solvable X to the
actual offender actor on U_v, using its literal Sylow Thompson image.
It needs neither a factor decomposition nor the legacy triple-cover
convention. It consumes the complete native projective-line contract.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1(1), printed p.99; B.5.6(1), p.105; 13.6.13, p.929.
The G₂ calculation uses the attributed ATLAS port in its imported module.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

private theorem solvable_le_center {D : Type*} [Group D] [IsQuasisimple D]
    (A : Subgroup D) [A.Normal] [Group.IsSolvable A] : A ≤ center D := by
  rcases IsQuasisimple.normal_le_center_or_eq_top A with h | he
  · exact h
  · let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_surjective (f := A.subtype)
        (by rw [he]; exact topEquiv.surjective))).elim

private theorem symmetric_solvable_normal {n : ℕ} (hn : 5 ≤ n)
    (A : Subgroup (Equiv.Perm (Fin n))) [A.Normal] [Group.IsSolvable A] : A = ⊥ := by
  by_contra h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn)
    ((nontrivial_iff_ne_bot A).mpr h)
  let : Group.IsSolvable (alternatingGroup (Fin n)) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  let : Nontrivial (alternatingGroup (Fin n)) := alternatingGroup.nontrivial_of_three_le_card (by simpa using (show 3 ≤ n by omega))
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin n)) inferInstance

private theorem g2_solvable_normal
    (A : Subgroup (Atlas.G2.Model (ZMod 2))) [A.Normal] [Group.IsSolvable A] : A = ⊥ := by
  by_contra h
  have hle := Atlas.G2.BinaryException.H_le_normal A h
  let : Group.IsSolvable Atlas.G2.BinaryException.H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  let := Atlas.G2.BinaryException.H_isPerfect
  let : Nontrivial Atlas.G2.BinaryException.H :=
    (nontrivial_iff_ne_bot _).mpr Atlas.G2.BinaryException.H_ne_bot
  exact Group.IsPerfect.not_isSolvable Atlas.G2.BinaryException.H inferInstance

private theorem solvable_normal_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : ∀ B : Subgroup E, B.Normal → Group.IsSolvable B → B = ⊥)
    (A : Subgroup D) [A.Normal] [Group.IsSolvable A] : A = ⊥ := by
  have he := h (A.map e.toMonoidHom)
    (Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupMap A)
      (e.toMonoidHom.subgroupMap_surjective A))
  exact (map_eq_bot_iff_of_injective _ e.injective).mp he

private theorem whole_excluded {D : Type*} [Group D]
    (A C : Subgroup D) [A.Normal] [Group.IsSolvable A]
    (hne : A ≠ ⊥) (hfull : ⁅A, C⁆ = A)
    (hq : IsQuasisimple (generalizedFitting D)) (he : generalizedFitting D = ⊤) : False := by
  let : IsQuasisimple (⊤ : Subgroup D) := he ▸ hq
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv topEquiv
  apply hne
  apply le_bot_iff.mp
  calc
    A = ⁅A, C⁆ := hfull.symm
    _ ≤ ⁅center D, C⁆ := commutator_mono (solvable_le_center A) le_rfl
    _ = ⊥ := commutator_center_left C

/-- Exclude every quasisimple source case using the actual normal solvable
subgroup and its full commutator. The outer cases use their model maps. -/
theorem quasisimple_excluded {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (A C : Subgroup D) [A.Normal] [Group.IsSolvable A]
    (hne : A ≠ ⊥) (hfull : ⁅A, C⁆ = A)
    (hq : IsQuasisimple (generalizedFitting D))
    (ha : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ
      (generalizedFitting D)) : False := by
  cases ha.clause_one with
  | irreducible _ _ _ _ extension =>
    rcases extension with he | ⟨_, ho⟩
    · exact whole_excluded A C hne hfull hq he
    · apply hne
      rcases ho with hs | hg
      · obtain ⟨n, hn, _, ⟨e⟩⟩ := hs
        exact solvable_normal_transport e.groupEquiv
          (fun B hN hB => @symmetric_solvable_normal n hn B hN hB) A
      · obtain ⟨e⟩ := hg
        exact solvable_normal_transport e.groupEquiv
          (fun B hN hB => @g2_solvable_normal B hN hB) A
  | doubleThree _ he _ _ _ => exact whole_excluded A C hne hfull hq he
  | naturalDual _ _ he _ => exact whole_excluded A C hne hfull hq he
  | repeatedNatural _ _ _ _ _ he _ => exact whole_excluded A C hne hfull hq he

/-- Exclude the complete native quasisimple alternative on the original
star offender representation. -/
theorem minimalSolvable_quasisimple_excluded {G : Type*} [Group G] [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (hq : IsQuasisimple (generalizedFitting (FFFactors.offenderActor (starRepresentation z v))))
    (ha : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (FFFactors.offenderRepresentation (starRepresentation z v))
      (generalizedFitting (FFFactors.offenderActor (starRepresentation z v)))) : False := by
  obtain ⟨hn, hne, _, hs, hfull⟩ := minimalSolvable_in_offender L T z v hz S hS hX
  let := hn
  let := hs
  exact quasisimple_excluded _ _ _ hne hfull hq ha

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional
