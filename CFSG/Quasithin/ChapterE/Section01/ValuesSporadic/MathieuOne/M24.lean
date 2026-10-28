module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.Reduction
public import Theory.Mathieu.M24.ValueBoundParabolics.Construction
public import Theory.Mathieu.M24.ValueBoundParabolics.Transport
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# Rank-one E-generation for an M₂₄ generalized Fitting subgroup

Three native order-3072 subgroups through a Sylow two-subgroup generate M₂₄.
Their actual S₃ two-core quotients imply solvability and hence rank-one
E-generation. Sylow conjugacy transports the triple to the specified carrier.
Every automorphism of M₂₄ is inner, so self-centralization of F*(G) identifies
the ambient group itself with M₂₄ and excludes any proper outer extension.

Source: Aschbacher–Smith, E.1.14(4), printed p.214, citing Asc82a Lemma 4.9.
The reused native triple also supplies E.4.3(2), printed pp.241–242.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterE.MathieuOne
variable {G : Type*} [Group G] [Finite G]

/-- The generating triple supplies the bound for every actual M₂₄ carrier. -/
theorem isEGenerated_of_equiv_m24 (e : G ≃* M24) : IsEGenerated 1 G := by
  classical
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨P, hP, hc, hgen⟩ := M24ValueBoundParabolics.exists_native_triple
  obtain ⟨R, hR, hrgen, -, hrq⟩ :=
    M24ValueBoundParabolics.transport_native_triple e T P hP hc hgen
  apply isEGenerated_of_family T (Set.range R)
  · simpa only [sSup_range] using hrgen
  · rintro H ⟨i, rfl⟩
    obtain ⟨ei⟩ := hrq i
    let := isSolvable_of_symmetricThree_twoCore_quotient ei
    exact ⟨hR i, isEGenerated_one_of_solvable⟩

/-- E.1.14(4), upper bound for the M₂₄ generalized Fitting subgroup case. -/
theorem isEGenerated_of_m24_socle (e : generalizedFitting G ≃* M24) :
    IsEGenerated 1 G := by
  obtain ⟨a⟩ := ambient_equiv_of_inner_automorphisms e M24OuterRestriction.conj_surjective
  exact isEGenerated_of_equiv_m24 a
end CFSG.Quasithin.ChapterE.MathieuOne
