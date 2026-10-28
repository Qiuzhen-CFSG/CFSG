module

public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Mathlib.GroupTheory.Index

/-!
# Four-subgroup generation and the hyperplane fixed-space span

Every subgroup of order four in a group meets a subgroup of relative index
two nontrivially. Its fixed space therefore lies in the sum of element fixed
spaces of that index-two subgroup. This proves the final implication in
H.15.4: generation by four-subgroup fixed spaces implies the asserted xi
equality for every hyperplane. The generation hypothesis must be proved
separately on the actual Mathieu module.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4, final paragraph, printed p.400.
-/

@[expose] public section
namespace MathieuCode.M22Quintet
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The span in H.15.4(4), using genuine elementary four-subgroups. -/
noncomputable def fourFixedSpan (ρ : Representation (ZMod 2) G V) (K : Subgroup G) :
    Submodule (ZMod 2) V :=
  ⨆ (B : Subgroup G) (_ : B ≤ K) (_ : IsElementaryAbelian 2 B) (_ : Nat.card B = 4),
    fixedSpace ρ B

/-- Relative index, rather than index in the ambient group, is essential here. -/
theorem four_subgroup_meets_index_two {A B K : Subgroup G}
    (hB : B ≤ K) (hcard : Nat.card B = 4) (hindex : A.relIndex K = 2) :
    ∃ b : G, b ∈ A ∧ b ∈ B ∧ b ≠ 1 := by
  have hne : A ⊓ B ≠ ⊥ := by
    intro he
    have hi := Subgroup.relIndex_le_of_le_right hB (show A.relIndex K ≠ 0 by omega)
    rw [← Subgroup.inf_relIndex_right, he, Subgroup.relIndex_bot_left, hcard,
      hindex] at hi
    omega
  by_contra! hn
  apply hne
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro b hb
  exact hn b hb.1 hb.2

theorem four_fixedSpace_le_fixedSpaceSpan (ρ : Representation (ZMod 2) G V)
    {A B K : Subgroup G} (hB : B ≤ K) (hcard : Nat.card B = 4)
    (hindex : A.relIndex K = 2) : fixedSpace ρ B ≤ fixedSpaceSpan ρ A := by
  obtain ⟨b, hbA, hbB, hb1⟩ := four_subgroup_meets_index_two hB hcard hindex
  apply le_trans ?_ (fixedSpace_le_fixedSpaceSpan ρ hbA hb1)
  intro v hv c
  exact hv ⟨c.val, (Subgroup.zpowers_le.mpr hbB) c.property⟩

theorem fourFixedSpan_le_fixedSpaceSpan (ρ : Representation (ZMod 2) G V)
    {A K : Subgroup G} (hindex : A.relIndex K = 2) :
    fourFixedSpan ρ K ≤ fixedSpaceSpan ρ A := by
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => iSup_le fun hcard => ?_
  exact four_fixedSpace_le_fixedSpaceSpan ρ hB hcard hindex

/-- The xi clause follows from the distinct four-subgroup generation clause. -/
theorem fixedSpaceSpan_eq_top_of_fourFixedSpan (ρ : Representation (ZMod 2) G V)
    {A K : Subgroup G} (hindex : A.relIndex K = 2)
    (hgen : fourFixedSpan ρ K = ⊤) : fixedSpaceSpan ρ A = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact fourFixedSpan_le_fixedSpaceSpan ρ hindex

end MathieuCode.M22Quintet
