module
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Involutory automorphisms fixing a subgroup with a binary-three section

The two actual involution centralizers of Rudvalis have orders 245760 and
116480. Neither order is divisible by 21. Every automorphism is inner, so
an involutory automorphism fixing a subgroup of order divisible by 21 is
the identity. Simplicity is inherited from the containing source component.

The application to Aschbacher--Smith 10.2.9, printed pp.750--751, retains
the literal image of the original SL₃(2) section. Model sources and native
word certificates are documented in the imported centralizer modules;
the centralizer table is GLS3 Table 5.3r.
-/

public section
open Subgroup
namespace Rudvalis

/-- Neither actual involution class has a centralizer with a factor 21. -/
theorem involution_centralizer_not_twentyOne (x : Model) (hx : orderOf x = 2) :
    ¬ 21 ∣ Nat.card (centralizer ({x} : Set Model)) := by
  rcases InvolutionCentralizers.centralizer_representatives x hx with h | h
  · rw [InvolutionCentralizers.first_centralizer_card h.1]
    decide
  · rw [InvolutionCentralizers.second_class_centralizer_card h.1]
    decide

/-- The pointwise automorphism fixer of a subgroup with order divisible by
21 has no nonidentity involution. -/
theorem eq_one_of_fixes_twentyOne [IsSimpleGroup Model]
    (B : Subgroup Model) (hB : 21 ∣ Nat.card B)
    (a : MulAut Model) (ha : a ^ 2 = 1) (hf : ∀ x ∈ B, a x = x) : a = 1 := by
  by_contra hne
  have ho : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha,hne⟩
  obtain ⟨g,hg⟩ := component_conj_surjective a
  obtain ⟨x,hx,he,hfixed⟩ := MulAut.inner_involution_representative
    LowCentralizers.model_center_eq_bot a ho ⟨g,hg.symm⟩
  have hBC : B ≤ centralizer ({x} : Set Model) := by
    rw [←hfixed]
    intro y hy
    exact (MulAut.mem_fixedSubgroup a y).mpr (hf y hy)
  exact involution_centralizer_not_twentyOne x hx (hB.trans (card_dvd_of_le hBC))

end Rudvalis
