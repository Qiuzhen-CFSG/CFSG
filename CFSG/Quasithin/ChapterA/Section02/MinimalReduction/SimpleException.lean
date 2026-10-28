module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Covering
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# A simple section in the unitary exception

A unitary exceptional witness with simple central quotient is quasisimple.
Its first component is consequently the whole covering group. Passing to
its central quotient, with the actual Hermitian form and fixed-field
convention preserved, places the section on the PSU₃ branch of Theorem B.
This argument does not require a separate ordinary-rank computation for SU₃.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.1(1.b) and the simple-section conclusion of A.2.15, printed pp.33, 37–38.
-/

public section

open Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterA.Section02
universe u v
variable {G : Type u} [Group G]

/-- The central quotient of an actual even-field SU₃ model is the matching PSU₃ model. -/
theorem IsSpecialUnitaryModel.projectiveModel {n : ℕ}
    (h : IsSpecialUnitaryModel G 3 (2 ^ n)) (hn : 0 < n) :
    ClassicalGroup.IsPSU (G ⧸ center G) 3 (2 ^ n) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := h
  let := hF
  let := hfin
  have hc : (center G).map e.toMonoidHom = center J.specialSubgroup := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (centerCongr e ⟨a, ha⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  have hk := J.specialToProjective_ker_eq_center
    (BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison.center_eq_bot
      J hn hcard hconj)
  refine ⟨F, hF, hfin, J, hcard, hconj, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e hc).trans
    ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective))

/-- If the exceptional section is simple, it already belongs to the Bender list. -/
theorem TheoremAException.theoremBModel_of_simple {S : Type v} [Group S]
    [IsSimpleGroup S] {p : ℕ} (h : TheoremAException G S p) : IsTheoremBModel S := by
  obtain ⟨_, H, _, ⟨e⟩, ⟨d⟩⟩ := h
  let : Group.IsPerfect H := d.semisimple.isPerfect
  let : IsQuasisimple H := { simple := e.symm.isSimpleGroup }
  have ht : IsComponent H ⊤ :=
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have heq : d.first = ⊤ := d.first_component.eq_of_le ht le_top
  let a : d.first ≃* H := (MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv
  have hm := d.first_model.of_mulEquiv a.symm
  exact .bender (.unitary d.n₁ (by have := d.first_large; omega)
    ((hm.projectiveModel (by have := d.first_large; omega)).of_mulEquiv e))

end CFSG.Quasithin.ChapterA.Section02
