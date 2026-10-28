module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12CentralClass
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import Theory.Mathieu.M12.Properties.InvolutionFusion
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductProjection
public import Theory.SpecificGroups.Alternating.FiveComponents

/-!
# M₁₂ involution-table assembly interfaces

This module records the source-faithful assembly of the M₁₂ rows in
Aschbacher–Smith 16.1.5(4), printed p.1171. The marked quaternion row is
proved in `M12CentralClass`; the strict Sylow-index and quaternion component
consequences are proved in `M12Consequences`. `InvolutionFusion` proves that
all inner involutions are conjugate to the two concrete representatives `z`
and `m12Involution2A`.

The remaining concrete model inputs are kept explicit here: the 2A centralizer
identification with C₂ × S₅ and exhaustive coverage of outer involutions. This
prevents a finite-group label or an unconnected family tag from being used as
the source theorem. Once those two model facts are supplied, the assembly
lemmas below discharge the exact inner and component conclusions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair Theory.GroupTheory

/-- Transport of the quaternion-kernel centralizer presentation across an
actual group isomorphism. -/
public theorem IsM12QuaternionExtension.of_mulEquiv {C D : Type*} [Group C] [Group D]
    (h : IsM12QuaternionExtension C) (e : C ≃* D) : IsM12QuaternionExtension D := by
  obtain ⟨Q, hQ, ⟨d⟩, ⟨f⟩⟩ := h
  let R := Q.map e.toMonoidHom
  let : R.Normal := hQ.map e.toMonoidHom e.surjective
  exact ⟨R, inferInstance, ⟨d.map (e.subgroupMap Q)⟩,
    ⟨(QuotientGroup.congr Q R e rfl).symm.trans f⟩⟩

private theorem alternative_congr (e : M12 ≃* M12) (r : MulAut M12)
    (h : M12InvolutionAlternative r) :
    M12InvolutionAlternative (MulAut.congr e r) := by
  have he := MulAut.fixedSubgroupCongr e r
  rcases h with ⟨hi, hq | hp⟩ | ⟨ho, hp⟩
  · exact Or.inl ⟨(MulAut.congr_inner_iff e r).mpr hi,
      Or.inl (hq.of_mulEquiv he)⟩
  · obtain ⟨hp⟩ := hp
    exact Or.inl ⟨(MulAut.congr_inner_iff e r).mpr hi,
      Or.inr ⟨he.symm.trans hp⟩⟩
  · obtain ⟨hp⟩ := hp
    exact Or.inr ⟨fun hi => ho ((MulAut.congr_inner_iff e r).mp hi),
      ⟨he.symm.trans hp⟩⟩

/-- The source-correct inner table follows from inner fusion and the two
centralizer rows. The second row is intentionally an explicit model input. -/
public theorem m12_inner_alternative_of_centralizer_rows (r : MulAut M12)
    (hr : orderOf r = 2) (hinner : ∃ g : M12, r = MulAut.conj g)
    (h2A : ∀ g : M12, IsConj m12Involution2A g →
      Nonempty (Subgroup.centralizer ({g} : Set M12) ≃* C2 × S5)) :
    M12InvolutionAlternative r := by
  obtain ⟨g, rfl⟩ := hinner
  have hg : orderOf g = 2 := by
    rw [← orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot m12_center_eq_bot) g]
    exact hr
  rcases M12InvolutionFusion.involution_fusion g hg with hz | hA
  · obtain ⟨c, hc⟩ := isConj_iff.mp hz
    have hc' : MulAut.congr (MulAut.conj c) (MulAut.conj z) = MulAut.conj g := by
      rw [MulAut.congr_conj]
      change MulAut.conj (c * z * c⁻¹) = MulAut.conj g
      rw [hc]
    simpa only [hc'] using alternative_congr (MulAut.conj c) (MulAut.conj z)
      m12_marked_inner_alternative
  · obtain ⟨e⟩ := h2A g hA
    have he : Nonempty ((MulAut.conj g).fixedSubgroup ≃* C2 × S5) := by
      rw [MulAut.fixedSubgroup_conj]
      exact ⟨e⟩
    exact Or.inl ⟨⟨g, rfl⟩, Or.inr he⟩

/-- Once the outer fixed-subgroup row is supplied, the complete table follows
from the inner assembly. The outer hypothesis retains actual non-innerness. -/
public theorem m12_involution_alternative_of_rows (r : MulAut M12)
    (hr : orderOf r = 2)
    (hrows : (∃ g : M12, r = MulAut.conj g) ∨
      ((¬ ∃ g : M12, r = MulAut.conj g) ∧
        Nonempty (r.fixedSubgroup ≃* C2 × A5)))
    (h2A : ∀ g : M12, IsConj m12Involution2A g →
      Nonempty (Subgroup.centralizer ({g} : Set M12) ≃* C2 × S5)) :
    M12InvolutionAlternative r := by
  rcases hrows with hinner | houter
  · exact m12_inner_alternative_of_centralizer_rows r hr hinner h2A
  · exact Or.inr houter

/-- Every component in either product row is actually A₅. -/
public theorem m12_component_equiv_a5_of_alternative (r : MulAut M12)
    (ht : M12InvolutionAlternative r) (K : Subgroup r.fixedSubgroup)
    (hK : IsComponent r.fixedSubgroup K) : Nonempty (K ≃* A5) := by
  rcases ht with ⟨_, hq | hp⟩ | ⟨_, hp⟩
  · exact (quaternionExtension_no_component hq K hK).elim
  · obtain ⟨e⟩ := hp
    obtain ⟨L, hL, ⟨f⟩⟩ :=
      IsComponent.equiv_component_of_solvable_prod _ (hK.map_equiv e)
    obtain ⟨g⟩ := component_symmetric_five_equiv L hL
    exact ⟨(e.subgroupMap K).trans (f.trans g)⟩
  · obtain ⟨e⟩ := hp
    obtain ⟨L, hL, ⟨f⟩⟩ :=
      IsComponent.equiv_component_of_solvable_prod _ (hK.map_equiv e)
    obtain ⟨g⟩ := component_alternating_five_equiv L hL
    exact ⟨(e.subgroupMap K).trans (f.trans g)⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
