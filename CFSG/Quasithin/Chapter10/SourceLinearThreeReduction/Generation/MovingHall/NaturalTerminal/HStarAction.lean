module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.PairedCoordinates
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.Classification

/-!
# The comparison H-star action over a general even field

The original natural pair controls the Baumann normalizer. The original H-star
subgroup escapes that normalizer, forcing Thompson movement on its reduced
omega-center orbit. This supplies its two-residual commutator identity and the
full E.2.3 single-or-paired marked action, without a field-four restriction.
The alpha decomposition is on that same orbit and centralizer quotient.

Source: Aschbacher–Smith 10.2.2(2), 10.2.3(4), pp.744–746, and E.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The literal H* omega-orbit satisfies the missing movement premise of E.2.3. -/
theorem Context.hstar_thompson_moves_omega_orbit
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    ¬ elementaryAbelianMaxJ (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ centralizer
      (((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H) : Set H) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  apply thompson_moves_of_noncentral_reduced_baumann_not_normal S
    (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) U
    (source_hstar_omega_orbit_reduced D ctx.hstar)
    (source_hstar_omega_orbit_centralizer_proper D ctx.hstar ctx.moving)
  intro hB
  let := hB
  have hbmap : (baumann (S : Subgroup H)).map H.subtype = baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype =
      baumann ((S : Subgroup H).map H.subtype) at he
    exact he.trans (congrArg baumann (map_subgroupOf_eq_of_le ctx.hstar.1.1.2))
  have hnB := (baumann (S : Subgroup H)).le_normalizer_map H.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hbmap] at hnB
  exact ctx.hstar.1.2 (hnB.trans (ctx.original_baumann_normalizer_le D n hn hF e))

/-- Original 10.2.2(2), retaining the intrinsic H and original Sylow subgroup. -/
theorem Context.hstar_residual_eq_thompson_commutator
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    pResidual 2 H = ⁅pResidual 2 H,elementaryAbelianMaxJ (T.subtype ctx.hstar.1.1.2 : Subgroup H)⁆ := by
  let S := T.subtype ctx.hstar.1.1.2
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  apply minimalParabolic_residual_commutator_of_normalized_two_actor S
    (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) _ (sSup_le fun _ hA => hA.1)
    ((S : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _))
  exact fun hc => hJ (hc.trans (le_centralizer_iff.mp hU.le_centralizer_pCore))
set_option backward.isDefEq.respectTransparency false in
/-- The complete source alternatives retain their genuine factor and module markings. -/
theorem Context.hstar_marked_alternatives
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).normal
    letI := (source_hstar_omega_orbit_reduced D ctx.hstar).elementary
    let C := centralizer (U : Set H)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    let σ := α.comp Y.subtype
    letI := offenderSubgroup_normal α
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ K : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
        Nonempty (MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ d : SourceTwoFactorCase σ,
        (∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
        ((∃ K : BinaryField, Nonempty (d.MarkedProduct (linearNatural K 2))) ∨
          Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) ctx.large
  rcases source_nonsolvable_natural_factors
      (Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1) S hP U hU hs hJ with hsingle | ⟨d,_,_⟩
  · exact Or.inl hsingle
  · have hcore : pCore 2 (H ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
    have hne : q.ker ≠ ⊤ := by
      rw [hk]
      exact source_hstar_omega_orbit_centralizer_proper D ctx.hstar ctx.moving
    have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
    have hff : IsFFModule α := by
      obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
      · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
      · exact hf
    obtain ⟨t,ht₁,ht₂,hkind⟩ := source_offender_two_factor_shared_natural α
      (S.mapSurjective hq) hp hff hcore d
    exact Or.inr ⟨d,⟨t,ht₁,ht₂⟩,hkind⟩

/-- The actual H* alpha subgroup has the E.2.3 moved-plus-fixed decomposition. -/
theorem Context.hstar_alpha_and_span
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    thompsonAlpha (S : Subgroup H) =
      ((⁅U,pResidual 2 H⁆ : Subgroup H) ⊓
        centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) ⊔
      (thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ∧
    conjugateSpanBy (thompsonAlpha (S : Subgroup H)) (pResidual 2 H) =
      (⁅U,pResidual 2 H⁆ : Subgroup H) ⊔
        (thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  exact (source_action_conclusions (Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1)
    (T.subtype ctx.hstar.1.1.2) (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) _ hU
    (ctx.hstar_thompson_moves_omega_orbit D n hn hF e)).2.2.2
end CFSG.Quasithin.Chapter10.MovingHall
