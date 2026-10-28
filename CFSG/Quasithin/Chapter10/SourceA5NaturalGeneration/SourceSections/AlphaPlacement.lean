module
public import Stellmacher.OmegaCenterCentralizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
/-!
# Removing the original central alpha summand

The source hypothesis C_Z(L₀)=1, with Z=Ω₁(Z(T)), forces C_T(L₀)=1
by normal-subgroup detection in the two-group T. In particular the
central alpha summand in E.2.3 vanishes. Applied to the original paired
linear source, this places the original Sylow center in its actual moved
module, retaining the literal quotient and component maps.

Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_sylow_orbit_centralizer_eq_bot
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ :=
  inf_centralizer_eq_bot_of_omega_center _ _ T.isPGroup'
    (le_normalizer_componentOrbit L T) hz

theorem source_alpha_orbit_centralizer_eq_bot
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  apply bot_unique
  apply le_trans (inf_le_inf_right _ ?_) (source_sylow_orbit_centralizer_eq_bot hz).le
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  exact (fun _ hx => hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false in
theorem source_original_alpha_le_moved_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      thompsonAlpha (T : Subgroup G) ≤
        ⁅D.moduleSubgroup,localOrbit T L⁆ := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have hspan := paired_orbit_span_of_source_model S (source_a5_minimal_parabolic D e hn)
    U hU hJ q hq hk d F c hexchange
  have hplace : thompsonAlpha (S : Subgroup X) ≤
      ⁅U,pResidual 2 X⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X)) :=
    (le_conjugateSpanBy _ _).trans_eq hspan
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hα : (thompsonAlpha (S : Subgroup X)).map X.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hS]
  have hm := map_mono (f := X.subtype) hplace
  rw [hα,Subgroup.map_sup,map_commutator,
    map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 X)),source_join_residual D] at hm
  have hcentral :
      (thompsonAlpha (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X)).map X.subtype = ⊥ := by
    apply bot_unique
    apply le_trans ?_ (source_alpha_orbit_centralizer_eq_bot hz).le
    rintro z ⟨w,hw,rfl⟩
    refine ⟨hα ▸ mem_map_of_mem X.subtype hw.1,?_⟩
    intro l hl
    obtain ⟨a,ha,rfl⟩ := (source_join_residual D).symm ▸ hl
    exact congrArg X.subtype (hw.2 a ha)
  simpa only [hcentral,sup_bot_eq] using hm

set_option backward.isDefEq.respectTransparency false in
theorem source_original_seed_le_moved_of_paired_linear
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      omegaOneCenterAmbient (T : Subgroup G) ≤
        ⁅D.moduleSubgroup,localOrbit T L⁆ := by
  dsimp only
  intro hJ d F c hexchange
  have h := source_original_seed_le_moved_sup_central_alpha_of_paired_linear
    D e hn hJ d F c hexchange
  simpa only [source_alpha_orbit_centralizer_eq_bot hz,sup_bot_eq] using h

end CFSG.Quasithin.Chapter10
