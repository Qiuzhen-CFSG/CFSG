module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.ResidualEscape
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry.ParabolicGeometry

/-!
# The original conjugate and escaping element for J.4

The constructed element of the second residual lies in L and outside H.
J.2.3(9) shows that it moves U. The source J.2.2(5) theorem then gives the
literal conjugate subgroup inside H, its quotient image of order two, and
its intersection with HC. The original orbit argument supplies an element
of this conjugate outside Q, as required in the opening notation of J.4.

Source: Aschbacher–Smith, J.4 and J.4.1(1),(5), printed p.440.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The complete actual choice at the start of J.4, in direct conjugation convention. -/
structure SourceChoice where
  g : G
  in_residual : g ∈ p.L₂
  outside_H : g ∉ d.toTypeRuSetup.H
  v : G
  v_mem : v ∈ d.toTypeRuSetup.U.map (MulAut.conj g).toMonoidHom
  v_not_Q : v ∉ d.toTypeRuSetup.Q

/-- Every source plane admits the required conjugate and escaping element. -/
theorem Plane.exists_sourceChoice : Nonempty (SourceChoice p) := by
  obtain ⟨g,hg,hn⟩ := p.exists_residual_outside_H
  have hgL := p.L₂_le_L hg
  have hi := SpecialCore.CommutatorGeometry.U_inf_conjugate d g hgL hn
  have hne : d.toTypeRuSetup.U.map (MulAut.conj g).toMonoidHom ≠ d.toTypeRuSetup.U := by
    intro he
    rw [he,inf_idem] at hi
    have hc := d.ru2.card_U d.card_Z
    change Nat.card d.toTypeRuSetup.U = 32 at hc
    rw [hi,d.ru1.card_V] at hc
    norm_num at hc
  have hnot := ConjugateIntersections.conjugateU_not_le_Q d g hgL hne
  obtain ⟨v,hv,hnv⟩ := Set.not_subset.mp hnot
  exact ⟨⟨g,hg,hn,v,hv,hnv⟩⟩

/-- The chosen original conjugate lies in H, has quotient image two, and meets HC in V. -/
theorem SourceChoice.conjugate_properties (s : SourceChoice p) :
    let Uα := d.toTypeRuSetup.U.map (MulAut.conj s.g).toMonoidHom
    Uα ≤ d.toTypeRuSetup.H ∧
      Nat.card ((Uα.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      Uα ⊓ d.toTypeRuSetup.HC = d.V := by
  apply lemma_J_2_2_five_source d s.g (p.L₂_le_L s.in_residual)
  intro he
  have hvU : s.v ∈ d.toTypeRuSetup.U := by
    rw [← he]
    exact s.v_mem
  exact s.v_not_Q (d.ru2.six.kernel_le hvU)

/-- The opening J.4 data exist for every finite group of type Ru. -/
theorem source_J4_choice (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (p : Plane d), Nonempty (SourceChoice p) := by
  obtain ⟨d,hp⟩ := source_plane h
  obtain ⟨p⟩ := hp
  exact ⟨d,p,p.exists_sourceChoice⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
