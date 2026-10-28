module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.NestedEmbedding.Unitary.Action
public import Theory.SpecificGroups.SU3.NestedStrongClosure

/-!
# Whole-factor innerness of nested unitary actions

When the two factors are nested, their union is the larger subgroup. The
intrinsic strong-closure theorem makes that whole subgroup inner from the
innerness of its involutions; containment then gives the smaller factor.
The intrinsic proof retains the actual root Sylow and field conventions and
handles arbitrary two-power elements, including the order-eight root-field
case. No assumption of elementarity of either whole factor is needed.

Source: Aschbacher, On finite groups of component type (1975), Lemma 3.4,
printed pp.94–96, in the unitary terminal branch; Huppert II.10.12 and GLS3
Theorem 2.5.12 and Section 2.7 supply the concrete unitary calculations.
-/

public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.NestedStrongClosure

/-- Every element of both nested factors is inner under the literal unitary
model cardinalities, not just every involution of the factors. -/
theorem unitary_nested_pair_innerness {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n) :
    UnitaryNestedPairInnerness J := by
  intro K hK T B₁ B₂ _ _ _ _ _ hc hi hnested
  have solve (B : Subgroup K) (hcB : IsStronglyClosedSet (B : Set K) T ⊤)
      (hBU : (B : Set K) ⊆ (B₁ : Set K) ∪ B₂) :
      B.map K.subtype ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
    apply stronglyClosed_inner_of_involutions J hn hJ hcard hfixed K hK T B hcB
    intro a ha hs
    by_cases he : a = 1
    · subst a
      exact (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)).one_mem
    · exact hi a (hBU ha) ⟨he, hs⟩
  rcases hnested with h | h
  · have he : (B₁ : Set K) ∪ B₂ = B₂ := Set.union_eq_right.mpr h
    have hout := solve B₂ (he ▸ hc) (fun _ hx => Or.inr hx)
    exact ⟨(map_mono h).trans hout, hout⟩
  · have he : (B₁ : Set K) ∪ B₂ = B₁ := Set.union_eq_left.mpr h
    have hout := solve B₁ (he ▸ hc) (fun _ hx => Or.inl hx)
    exact ⟨hout, (map_mono h).trans hout⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
