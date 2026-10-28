module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.SeedCentralizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.AlphaPlacement

/-!
# Original alpha placement after the general-field seed calculation

The vanished omega-center fixed subgroup eliminates the whole Sylow
centralizer of L₀. It therefore kills the coordinate kernel of the original
paired section and the central-alpha summand in E.2.3. Consequently alpha
lies in the original moved module, and the paired coordinates are injective.
These are the literal two missing inputs of the original Cartan-axis test.
Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE.ThompsonAction
open ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

set_option backward.isDefEq.respectTransparency false in
theorem Context.original_alpha_le_moved
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L) :
    thompsonAlpha (T : Subgroup G) ≤ ⁅D.moduleSubgroup,localOrbit T L⁆ := by
  have hz := (ctx.fixed_centers_of_natural_marking D degree hdegree hF e mark hBR).1
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
  have hP := source_natural_minimal_parabolic D e degree hdegree hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D degree hdegree hF e
  have hspan := paired_orbit_span_of_source_model S hP U hU hJ q hq hk d E c hexchange
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

/-- The original paired coordinates have trivial kernel once the fixed center vanishes. -/
theorem Context.original_coordinates_injective
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (localOrbit T L) V}
    (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G)) ρ) :
    Function.Injective c.coordinates := by
  have hz := (ctx.fixed_centers_of_natural_marking D degree hdegree hF e mark hBR).1
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [c.kernel_eq]
  have hker : D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ D.module_le_sylow).trans
      (source_sylow_orbit_centralizer_eq_bot hz).le)
  rw [hker,bot_subgroupOf]

end CFSG.Quasithin.Chapter10.MovingHall
