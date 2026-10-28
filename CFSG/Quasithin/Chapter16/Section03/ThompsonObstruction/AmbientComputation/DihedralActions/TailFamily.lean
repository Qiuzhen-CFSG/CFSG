module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.TailFamily.Family

/-!
# The exact maximum elementary family of the cyclic tail

For an explicit ActionData witness, the maximum elementary subgroups of
Q = T_C⟨w⟩ are exactly B⟨w⟩ with B maximum elementary in R, and J(Q)=R⟨w⟩.
In the two centralizing alternatives, the direct-product theorem applies;
in the semidihedral case every elementary subgroup of T_C lies in its given
involution-generated dihedral subgroup R. In the faithful alternative, the
index-two rotation-extension calculation excludes all elementary subgroups
outside R⟨w⟩ of order at least eight. Restricting the maximum family then
reduces to the same direct product.

The dihedral maximum four-groups are proved to generate R, rather than taking
J(R)=R as an extra premise. RankGeometry is unnecessary for this intrinsic
calculation. Construction of ActionData and source-theorem assembly remain
separate obligations. This module deliberately does not import MaxJClassification.

Source: Aschbacher--Smith, 16.3.12, printed pp.1181--1182 / PDF pp.1198--1199,
combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

private theorem tail_centralizing_maxFamily_le (d : Prepared T z t L) (a : ActionData d)
    (hw : a.w ∈ centralizer (commutingSylow T L : Set G))
    (hR : a.R = commutingSylow T L ∨ a.R = omegaOneAmbient (commutingSylow T L))
    {E : Subgroup G} (hE : E ∈ elementaryAbelianMaxSubgroups
      (commutingSylow T L ⊔ zpowers a.w)) : E ≤ a.R ⊔ zpowers a.w := by
  obtain ⟨B, hB, C, hC, rfl⟩ :=
    (maxFamily_sup_iff_of_disjoint_of_commuting _ _ (TailFamily.candidate_disjoint d a)
      (le_centralizer_iff.mpr (zpowers_le.mpr hw)) E).mp hE
  apply sup_le_sup _ hC.1
  rcases hR with hR | hR
  · exact hR.symm ▸ hB.1
  · rw [hR]
    let := hB.2.1
    intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x (hB.1 hx)
      (elemPow_eq_one_of_isElementaryAbelian x hx)

/-- All three source alternatives place every maximum elementary tail subgroup
inside the compatible product R⟨w⟩. -/
theorem tail_maxFamily_le (d : Prepared T z t L) (a : ActionData d)
    {E : Subgroup G} (hE : E ∈ elementaryAbelianMaxSubgroups
      (commutingSylow T L ⊔ zpowers a.w)) : E ≤ a.R ⊔ zpowers a.w := by
  rcases a.alternative with ⟨hw, hR | hR⟩ | ⟨hl, hy, hR⟩
  · exact tail_centralizing_maxFamily_le d a hw (Or.inl hR.1) hE
  · exact tail_centralizing_maxFamily_le d a hw (Or.inr hR.1) hE
  · exact TailFamily.faithful_large_le d a hl hy hR E hE.1 hE.2.1
      (TailFamily.maxFamily_card_ge_eight d a hE)

private theorem tail_maxFamily_restrict (d : Prepared T z t L) (a : ActionData d)
    (E : Subgroup G) :
    E ∈ elementaryAbelianMaxSubgroups (commutingSylow T L ⊔ zpowers a.w) ↔
      E ∈ elementaryAbelianMaxSubgroups (a.R ⊔ zpowers a.w) := by
  have hNQ : a.R ⊔ zpowers a.w ≤ commutingSylow T L ⊔ zpowers a.w :=
    sup_le_sup_right a.R_le _
  constructor
  · intro hE
    exact ⟨tail_maxFamily_le d a hE, hE.2.1,
      fun F hF hFe => hE.2.2 F (hF.trans hNQ) hFe⟩
  · intro hE
    obtain ⟨F, hF⟩ := elementaryAbelianMaxSubgroups_nonempty
      (commutingSylow T L ⊔ zpowers a.w)
    refine ⟨hE.1.trans hNQ, hE.2.1, ?_⟩
    intro B hBQ hB
    exact (hF.2.2 B hBQ hB).trans
      (hE.2.2 F (tail_maxFamily_le d a hF) hF.2.1)

/-- Exact maximum elementary family of the cyclic tail in 16.3.12.
The ActionData witness is explicit; its construction remains with the source
assembly. No additional rank-geometry hypothesis is needed for this calculation. -/
theorem tail_maxFamily_iff (d : Prepared T z t L) (a : ActionData d) (E : Subgroup G) :
    E ∈ elementaryAbelianMaxSubgroups (commutingSylow T L ⊔ zpowers a.w) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups a.R, E = B ⊔ zpowers a.w :=
  (tail_maxFamily_restrict d a E).trans (TailFamily.product_maxFamily d a E)

/-- The maximum elementary family generates precisely the dihedral factor and w. -/
theorem tail_maxJ (d : Prepared T z t L) (a : ActionData d) :
    elementaryAbelianMaxJ (commutingSylow T L ⊔ zpowers a.w) = a.R ⊔ zpowers a.w := by
  have hf : elementaryAbelianMaxSubgroups (commutingSylow T L ⊔ zpowers a.w) =
      elementaryAbelianMaxSubgroups (a.R ⊔ zpowers a.w) := by
    ext E
    exact tail_maxFamily_restrict d a E
  change sSup (elementaryAbelianMaxSubgroups _) = _
  rw [hf]
  exact TailFamily.product_maxJ d a

/-- Elementary subgroups outside R⟨w⟩ have strictly smaller order in the faithful
case, even though some outside elements can themselves be involutions. -/
theorem tail_faithful_small_outside (d : Prepared T z t L) (a : ActionData d)
    (hlarge : 4 < orderOf a.y) (hy : a.w⁻¹ * a.y * a.w = a.y * z)
    (hR : a.R = zpowers (a.y ^ 2) ⊔ zpowers t)
    (E : Subgroup G) (hEQ : E ≤ commutingSylow T L ⊔ zpowers a.w)
    (hE : IsElementaryAbelian 2 E) (hout : ¬ E ≤ a.R ⊔ zpowers a.w) :
    Nat.card E < 8 := by
  by_contra h
  exact hout (TailFamily.faithful_large_le d a hlarge hy hR E hEQ hE (by omega))

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
