module

public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.OuterRestriction
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Involutory automorphisms of M₁₁

Every automorphism is inner by the checked generator-rigidity theorem. Triviality
of the center identifies its order with that of its conjugator, so involution
conjugacy reduces the fixed subgroup to the explicit GL₂(3) centralizer.
Faithfulness of automorphisms on a perfect central quotient then transports both
innerness and the quotient centralizer to perfect central covers.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 16.1.5(3), printed p.1171. The stronger
innerness theorem also supplies the M₁₁ case of 16.1.6 for arbitrary two-elements.
-/

public section

open Subgroup
namespace Sporadic.Mathieu

/-- The concrete Witt-design group M₁₁ has trivial center. -/
theorem m11_center_eq_bot : center M11 = ⊥ := by
  let := m11_isSimpleGroup
  rcases (inferInstance : (center M11).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have he : m11InvolutionCentralizer = ⊤ := by
      apply top_unique
      intro x _
      apply (m11_mem_involutionCentralizer_iff x).mpr
      exact (mem_center_iff.mp (show x ∈ center M11 by rw [h]; trivial) _).symm
    have hc := m11_involutionCentralizer_card
    rw [he, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup M11) ≃* M11).toEquiv,
      m11_order] at hc
    norm_num at hc

/-- Every involutory automorphism of M₁₁ has fixed subgroup GL₂(3). -/
noncomputable def m11InvolutoryAutFixedEquiv (r : MulAut M11) (hr : orderOf r = 2) :
    r.fixedSubgroup ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := by
  refine Classical.choice ?_
  obtain ⟨g, rfl⟩ := m11_automorphism_inner r
  have hg : orderOf g = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot) g).symm.trans hr
  obtain ⟨s, hs⟩ := isConj_iff.mp (m11_involution_isConj_generatorA g hg)
  let e := MulAut.conj s
  have he : e g = m11GeneratorAInM11 := hs
  let ce := MulAut.fixedSubgroupCongr e (MulAut.conj g)
  rw [MulAut.congr_conj, he] at ce
  exact ⟨ce.trans ((MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj _)).trans
    m11InvolutionCentralizer_mulEquiv_gl2)⟩

variable {L : Type*} [Group L]
/-- Every automorphism of a group actually isomorphic to M₁₁ is inner. -/
theorem automorphism_inner_of_equiv_m11 (e : L ≃* M11) (r : MulAut L) : ∃ g : L, r = MulAut.conj g := by
  apply (MulAut.congr_inner_iff e r).mp
  obtain ⟨g, hg⟩ := m11_automorphism_inner (MulAut.congr e r)
  exact ⟨g, hg.symm⟩

/-- Transport the full fixed subgroup along the specified M₁₁ isomorphism. -/
noncomputable def involutoryAutFixedEquivOfM11 (e : L ≃* M11) (r : MulAut L) (hr : orderOf r = 2) :
    r.fixedSubgroup ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (MulAut.fixedSubgroupCongr e r).trans
    (m11InvolutoryAutFixedEquiv _ (((MulAut.congr e).orderOf_eq r).trans hr))

/-- Innerness of all automorphisms lifts to any perfect central cover of M₁₁. -/
theorem automorphism_inner_of_central_quotient_m11 [Group.IsPerfect L] (e : L ⧸ center L ≃* M11) (r : MulAut L) :
    ∃ g : L, r = MulAut.conj g := by
  apply (MulAut.centralQuotientAction_inner_iff e r).mp
  obtain ⟨g, hg⟩ := m11_automorphism_inner (MulAut.centralQuotientAction e r)
  exact ⟨g, hg.symm⟩

/-- The fixed subgroup on the central quotient of a perfect M₁₁ cover.
This is the quotient centralizer, not the image of the fixed subgroup upstairs. -/
noncomputable def involutoryAutQuotientFixedEquivOfM11 [Group.IsPerfect L]
    (e : L ⧸ center L ≃* M11) (r : MulAut L) (hr : orderOf r = 2) :
    ((center L).quotientAut r).fixedSubgroup ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (MulAut.fixedSubgroupCongr e ((center L).quotientAut r)).trans
    (m11InvolutoryAutFixedEquiv _ ((orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) r).trans hr))
end Sporadic.Mathieu


