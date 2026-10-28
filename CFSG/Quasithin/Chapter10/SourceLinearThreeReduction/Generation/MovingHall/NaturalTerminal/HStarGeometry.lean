module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarAction
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.ComponentLocalClass
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.CommonOvergroup

/-!
# Natural comparison components over an arbitrary even field

For the original H-star orbit, its seed-centralizer identity excludes both
five-letter actions. The remaining single or paired natural action produces
an actual C-component, its localV identity, and a local-class embedding of
the original ambient Baumann subgroup. The same source makes Baum(T) Sylow
in its join with O²(H), giving a common maximal two-local overgroup of H
and N_G(Baum(T)).

The seed-centralizer identity is still an earlier Hall-action obligation of
the moving-Hall assembly owner. No block or overcomponent is assumed here.
Source: Aschbacher–Smith 10.2.2(4), 10.2.3(4), pp.744–746, and E.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine natural source selection after the Hall seed-centralizer step. -/
theorem Context.hstar_linear_alternatives_of_seed_centralizer
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
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
        ∃ K : BinaryField, IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) K 2) ∨
      ∃ (d : SourceTwoFactorCase σ) (K : BinaryField),
        Nonempty (d.MarkedProduct (linearNatural K 2)) ∧
        ∃ t : S.mapSurjective hq,
          d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
          d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
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
  have hZU : Z ≤ U := subgroupOf_mono H (le_conjugateSpanBy _ _)
  rcases ctx.hstar_marked_alternatives D n hn hF e with
    ⟨hqs,c,hkind⟩ | ⟨d,hexchange,hkind⟩
  · rcases hkind with hlinear | hfive
    · exact Or.inl ⟨hqs,c,hlinear⟩
    · obtain ⟨a⟩ := hfive
      exfalso
      exact not_marked_five_movedSection_of_seed U Z q hq hk hZU S hCZ Y
        (generalizedFitting Y) c.sectionData a
  · rcases hkind with ⟨K,hlinear⟩ | hfive
    · exact Or.inr ⟨d,K,hlinear,hexchange⟩
    · obtain ⟨a⟩ := hfive
      exact (not_pairedFive_of_seed U Z q hq hk hZU S hCZ Y d a).elim
set_option backward.isDefEq.respectTransparency false in
theorem Context.hstar_component_localClass_of_seed_centralizer
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧
      U ≤ normalizer (K : Set H) ∧ B ≤ normalizer (K : Set H) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map
        (K ⊔ B).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) := by
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
  have hfit := source_hstar_fitting_eq_core D ctx.hstar
  have hsq := Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (generationParameter_le_one_of_solvable (G := H))) ctx.large
  have h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  rcases ctx.hstar_linear_alternatives_of_seed_centralizer D n hn hF e hCZ with
    ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
  · obtain ⟨hR,hlocal,hv⟩ := quasisimple_linear_component_localClass
      h36 hsq S hP U hU hJ q hq hk hqs c.sectionData K hlinear hs
      (source_hstar_omega_orbit_eq_normalClosure D ctx.hstar) hfit
    exact ⟨pResidual 2 H,hR,by rw [normalizer_eq_top]; exact le_top,
      by rw [normalizer_eq_top]; exact le_top,hlocal,hv⟩
  · obtain ⟨K,hK,_,_,hUK,hBK,hlocal,hv⟩ :=
      first_component_localClass h36 hsq S hP U hU hJ q hq hk hs hfit d K c hexchange
    exact ⟨K,hK,hUK,hBK,hlocal,hv⟩

/-- The actual H* local class uses exactly the original ambient Baumann inclusion. -/
theorem Context.hstar_common_baumann_embedding_of_seed_centralizer
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧ U ≤ normalizer (K : Set H) ∧
      B ≤ normalizer (K : Set H) ∧
      ChapterC.GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (ChapterC.GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map
        (K ⊔ B).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      ∃ b : baumann (T : Subgroup G) →* (K ⊔ B : Subgroup H),
        ChapterC.GlaubermanNiles.InLocalClass b ∧
        (H.subtype.comp (K ⊔ B).subtype).comp b = (baumann (T : Subgroup G)).subtype := by
  obtain ⟨K,hK,hUK,hBK,hlocal,hv⟩ :=
    ctx.hstar_component_localClass_of_seed_centralizer D n hn hF e hCZ
  exact ⟨K,hK,hUK,hBK,hlocal,hv,
    ChapterC.GlaubermanNiles.original_baumann_embedding (T : Subgroup G) H ctx.hstar.1.1.2
      (K ⊔ baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)) le_sup_right hlocal⟩
set_option backward.isDefEq.respectTransparency false in
theorem Context.hstar_baumann_sylow_of_seed_centralizer
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      ((pResidual 2 H).map H.subtype ⊔ baumann (T : Subgroup G)) := by
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
  let := offenderSubgroup_normal α
  have hP := source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large
  have hJ := ctx.hstar_thompson_moves_omega_orbit D n hn hF e
  have hs : Chapter1.IsSylowIn 2 (baumann (S : Subgroup H))
      (pResidual 2 H ⊔ baumann (S : Subgroup H)) := by
    rcases ctx.hstar_linear_alternatives_of_seed_centralizer D n hn hF e hCZ with
      ⟨hqs,c,K,hlinear⟩ | ⟨d,K,⟨c⟩,hexchange⟩
    · exact (quasisimple_linear_baumann_of_section S hP U hU hJ q hq hk
        hqs c.sectionData K hlinear).1
    · exact (source_global_baumann_and_alpha S hP U hU hJ q hq hk d K c hexchange).1
  have hm := Chapter1.Section02.IndexTwo.isSylowIn_map hs H.subtype
  have hSm : (S : Subgroup H).map H.subtype=(T : Subgroup G) :=
    map_subgroupOf_eq_of_le ctx.hstar.1.1.2
  have hBm := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
  change (baumann (S : Subgroup H)).map H.subtype=baumann ((S : Subgroup H).map H.subtype) at hBm
  rw [hSm] at hBm
  rwa [Subgroup.map_sup,hBm] at hm

theorem Context.hstar_baumann_normalizer_common_overgroup
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      normalizer (baumann (T : Subgroup G) : Set G) ⊔ H ≤ M₁ := by
  have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
    fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZB : omegaOneCenterAmbient (T : Subgroup G) ≤ baumann (T : Subgroup G) := by
    intro z hz
    refine ⟨hZT hz,?_⟩
    intro a ha
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 a
      ((sSup_le (fun _ hA => hA.1) : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G))
        ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1))
  have hB : baumann (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hz := bot_unique (hZB.trans he.le)
    exact ctx.moving (by rw [hz,commutator_bot_left])
  exact Chapter3.HStar.normalizer_residual_sylow_common_overgroup D.simpleQTKE T
    (le_normalizer_componentOrbit L T) ctx.hstar (baumann (T : Subgroup G)) hB inf_le_left
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _))
    (ctx.hstar_baumann_sylow_of_seed_centralizer D n hn hF e hCZ)
end CFSG.Quasithin.Chapter10.MovingHall
