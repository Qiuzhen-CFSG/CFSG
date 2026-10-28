module
public import Theory.GroupAction.SymplecticRankThree.ProjectiveIncidence
public import Theory.LinearAlgebra.BinaryPolarGeometry.Action

/-!
# Binary coordinates from Higman's polarity design

Every line has three points. Its intersection with a polar block is either
one point or the whole line, so the nonincidence rows satisfy the binary
addition law. The existing row-span reconstruction yields a nondegenerate
alternating four-space, with the original fifteen points identified with
its nonzero vectors. This derives coordinates from incidence rather than
assuming them. The resulting action preserves the same alternating form.

Source: Higman (1964), §7 and Lemma 10, pp.151–154, specialized to q=2;
the row-span construction is Theory.LinearAlgebra.BinaryPolarGeometry.
-/

public noncomputable section
open Theory.LinearAlgebra
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω : Type*} [Finite Ω] (D : PolarityDesign Ω 2)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = 3)
include hline

theorem binary_third_point {a b : Ω} (hab : a ≠ b) :
    ∃ c, c ≠ a ∧ c ≠ b ∧ D.line a b = {a,b,c} := by
  have hnot : ¬ D.line a b ⊆ {a,b} := by
    intro hh
    have hc := Set.ncard_le_ncard hh
    rw [hline a b hab, Set.ncard_pair hab] at hc
    omega
  obtain ⟨c,hc,hcn⟩ := Set.not_subset.mp hnot
  have hca : c ≠ a := fun he => hcn (Or.inl he)
  have hcb : c ≠ b := fun he => hcn (Or.inr he)
  refine ⟨c,hca,hcb,?_⟩
  symm
  apply Set.eq_of_subset_of_ncard_le (ht := Set.toFinite _)
  · intro x hx
    rcases hx with hx | hx | hx
    · exact hx.symm ▸ D.left_mem_line a b
    · exact hx.symm ▸ D.right_mem_line a b
    · exact hx.symm ▸ hc
  · rw [hline a b hab, Set.ncard_insert_of_notMem, Set.ncard_pair hcb.symm]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab,hca.symm⟩

theorem binary_one_or_all {a b c : Ω} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hl : D.line a b = {a,b,c}) :
    BinaryPolarGeometry.OneOrAll D.incident a b c := by
  intro w
  have hc : c ∈ D.line a b := hl.symm ▸ (by simp : c ∈ ({a,b,c} : Set Ω))
  have hsome : D.incident w a ∨ D.incident w b ∨ D.incident w c := by
    obtain ⟨x,hx,hxw⟩ := D.line_meets_block hline (by decide) hab w
    rw [hl] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl hxw
    · exact Or.inr (Or.inl hxw)
    · exact Or.inr (Or.inr hxw)
  have habc : D.incident w a → D.incident w b → D.incident w c := hc w
  have hacb : D.incident w a → D.incident w c → D.incident w b := by
    intro ha hc'
    have he := D.line_eq_of_mem hab hc hca.symm
    exact (he.symm ▸ D.right_mem_line a b) w ha hc'
  have hbca : D.incident w b → D.incident w c → D.incident w a := by
    intro hb hc'
    have he := D.line_eq_of_mem_of_mem hab (D.right_mem_line a b) hc hcb.symm
    exact (he.symm ▸ D.left_mem_line a b) w hb hc'
  tauto

theorem binaryPolarData (hdegree : Nat.card Ω = 15) : BinaryPolarGeometry.Data D.incident where
  reflexive := D.refl
  symmetric := D.symm
  nonincident a := by
    by_contra! hn
    have he : D.block a = Set.univ := Set.eq_univ_of_forall hn
    have hc := D.block_card a
    change (D.block a).ncard = 2^2+2+1 at hc
    rw [he,Set.ncard_univ,hdegree] at hc
    omega
  triples a b hab := by
    obtain ⟨c,hca,hcb,hl⟩ := D.binary_third_point hline hab
    exact ⟨c,D.binary_one_or_all hline hab hca hcb hl⟩

theorem binary_space_finrank (hdegree : Nat.card Ω = 15) :
    Module.finrank (ZMod 2) (BinaryPolarGeometry.Space D.incident) = 4 :=
  (D.binaryPolarData hline hdegree).space_finrank 4 (by rw [hdegree]; decide)

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
