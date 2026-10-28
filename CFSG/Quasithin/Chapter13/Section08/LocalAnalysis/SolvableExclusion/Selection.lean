module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Mathlib.Order.Minimal
public import Mathlib.GroupTheory.Solvable

/-!
# Choosing a minimal member of the genuine Hz family

A fixed nontrivial two-subgroup Z contained in L₁T and normalized by G₁
lies in the two-core of every intermediate overgroup. In the source Z=V₁
and G₁ centralizes Z. Finite subgroup order then gives a minimal member
of Hz below any solvable overgroup outside M, and solvability passes to it.
Minimality is among all members of Hz, not just solvable ones.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraphs of 13.8.13, printed pp.950–951. This supplies the selection and
generation reductions, not the supercritical or representation arguments.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup
variable {G : Type*} [Group G]

/-- The nontrivial two-core condition in Hz follows from the common line. -/
theorem mem_Hz_of_normal_two_subgroup
    {Z L₁ T G₁ M H : Subgroup G} (hZ : Z ≠ ⊥) (hp : IsPGroup 2 Z)
    (hZLT : Z ≤ L₁ ⊔ T) (hn : G₁ ≤ normalizer (Z : Set G))
    (hLT : L₁ ⊔ T ≤ H) (hG : H ≤ G₁) (hout : ¬ H ≤ M) :
    H ∈ Source.Hz L₁ T G₁ M := by
  have hzcore : Z ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (hZLT.trans hLT) (hG.trans hn)
  refine ⟨⟨?_, hLT⟩, hG, hout⟩
  intro he
  exact hZ (le_bot_iff.mp (he ▸ hzcore))

/-- Choose a minimal member of Hz below a solvable member. -/
theorem exists_minimal_Hz_below [Finite G]
    {L₁ T G₁ M H : Subgroup G} (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hs : Group.IsSolvable H) :
    ∃ J : Subgroup G, J ≤ H ∧ Minimal (· ∈ Source.Hz L₁ T G₁ M) J ∧
      Group.IsSolvable J := by
  obtain ⟨J, hJH, hJ⟩ := exists_minimal_le_of_wellFoundedLT
    (fun K => K ∈ Source.Hz L₁ T G₁ M) H hH
  let := hs
  exact ⟨J, hJH, hJ,
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hJH)⟩

/-- The first sentence of 13.8.13 applies to every solvable overgroup,
including those for which membership in H(L₁T) has not yet been established. -/
theorem exists_minimal_Hz_of_solvable_overgroup [Finite G]
    {Z L₁ T G₁ M H : Subgroup G} (hZ : Z ≠ ⊥) (hp : IsPGroup 2 Z)
    (hZLT : Z ≤ L₁ ⊔ T) (hn : G₁ ≤ normalizer (Z : Set G))
    (hLT : L₁ ⊔ T ≤ H) (hG : H ≤ G₁) (hout : ¬ H ≤ M)
    (hs : Group.IsSolvable H) :
    ∃ J : Subgroup G, J ≤ H ∧ Minimal (· ∈ Source.Hz L₁ T G₁ M) J ∧
      Group.IsSolvable J :=
  exists_minimal_Hz_below (mem_Hz_of_normal_two_subgroup hZ hp hZLT hn hLT hG hout) hs

/-- An outside subgroup in a minimal member generates it together with L₁T.
For the supercritical subgroup this is H=⟨P,L₁,T⟩. -/
theorem minimal_Hz_eq_generated
    {Z L₁ T G₁ M H P : Subgroup G} (hZ : Z ≠ ⊥) (hp : IsPGroup 2 Z)
    (hZLT : Z ≤ L₁ ⊔ T) (hn : G₁ ≤ normalizer (Z : Set G))
    (hH : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hP : P ≤ H) (hout : ¬ P ≤ M) : H = P ⊔ (L₁ ⊔ T) := by
  have hJH : P ⊔ (L₁ ⊔ T) ≤ H := sup_le hP hH.prop.1.2
  have hJ : P ⊔ (L₁ ⊔ T) ∈ Source.Hz L₁ T G₁ M :=
    mem_Hz_of_normal_two_subgroup hZ hp hZLT hn le_sup_right
      (hJH.trans hH.prop.2.1) (fun h => hout (le_sup_left.trans h))
  exact le_antisymm (hH.le_of_le hJ hJH) hJH

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
