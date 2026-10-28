module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.PairedHall
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.PairedHallNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaAxis

/-!
# The original comparison component after the general-field Hall calculation

The surviving paired H-star source supplies its canonical first component,
with the original field order and nontrivial alpha fixed subgroup. The same
component retains the local-class and localV identities, generates H with
its Sylow, and has a two-conjugate residual cover. The prescribed Hall acts
on it and every conjugate. The common characteristic-pair theorem gives
the block alternative for this same component and the original L. Its actual
intersection with the original Hall lies on one of the original natural
coordinate axes, by the nonzero alpha fixed subgroup.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

/-- Original paired comparison, with field order, Hall action and block alternative discharged. -/
theorem Context.paired_component_and_block
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
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
    let B₀ := baumann (S : Subgroup H)
    letI := offenderSubgroup_normal α
    ∃ (d : SourceTwoFactorCase (α.comp Y.subtype)) (E : BinaryField),
      Nat.card E.Carrier = Nat.card F ∧ Nonempty (d.MarkedProduct (linearNatural E 2)) ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ K.map q = d.first.map Y.subtype ∧
        (solvableResidual (RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first)).map
          (RankOneBaumann.PairedFactorOrbit.factorPreimage q Y d.first).subtype = K ∧
        U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
        InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
        (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map (K ⊔ B₀).subtype =
          (⁅U,K⁆ : Subgroup H) ⊔ (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
        thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥ ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier)) ∧ K ⊔ (S : Subgroup H) = ⊤ ∧
        (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
        Nat.card F - 1 ∣ Nat.card (K ⊓ normalizer (B₀ : Set H) : Subgroup H) ∧
        B ≤ normalizer (K : Set H) ∧
        (∀ t : H, B ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set H)) ∧
        (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
          (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m)) ∧
        ∃ E' : BinaryField,
          letI : Algebra (ZMod 2) E'.Carrier := ZMod.algebra _ 2
          ∃ (q₁ q₂ : localOrbit T L →* SL(2,E'.Carrier)),
            Nonempty (BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
              (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
              (Representation.prod (SL2.BinarySmall.natural.comp q₁)
                (SL2.BinarySmall.natural.comp q₂))) ∧
            ((B ⊓ K).map H.subtype ≤ q₁.ker.map (localOrbit T L).subtype ∨
              (B ⊓ K).map H.subtype ≤ q₂.ker.map (localOrbit T L).subtype) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU := source_hstar_omega_orbit_reduced D ctx.hstar
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' C
  have hBR : B.map H.subtype ≤ localOrbit T L :=
    hBB.trans ((map_subtype_le _).trans inf_le_left)
  have hCZ := ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR
  have hkc : q.ker = pCore 2 H := hk.trans
    (source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar hCZ)
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
  obtain ⟨d,E,hE,⟨c⟩,hexchange⟩ := ctx.hstar_paired_same_field_of_borel D n hn hF e mark hBB
  obtain ⟨K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover⟩ :=
    first_component_localClass_with_coverage h36 hsq S hP U hU hJ q hq hk hkc
      hs hfit d E c hexchange
  have hdiv := paired_source_selected_cartan_divisor S hP U hU hJ q hq hk
    (hkc.symm ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 H))) d E c hexchange K hi
    (localClass_inclusion_sylow K (baumann (S : Subgroup H)) hlocal)
  rw [hE] at hdiv
  have hBN := source_hstar_paired_hall_normalizes D ctx.hstar B ctx.hall_le ctx.hall d K hcan hcover
  obtain ⟨hz,hzH⟩ := ctx.fixed_centers_of_natural_marking D n hn hF e mark hBR
  refine ⟨d,E,hE,⟨c⟩,K,hK,hi,hcan,hUK,hBK,hlocal,hv,hfixed,heq,hgen,hcover,hdiv,hBN.1,hBN.2,
    ctx.one_block_of_intrinsic_localClass D n hn hF e hz hzH K hK hBK hlocal hgen,?_⟩
  obtain ⟨E',q₁,q₂,c',_,_⟩ := (ctx.original_paired_coordinates_and_seed D n hn hF e).1
  refine ⟨E',q₁,q₂,⟨c'⟩,?_⟩
  have hfixedG := alpha_fixed_subtype_nontrivial T H ctx.hstar.1.1.2 K hfixed
  have hfixedP : thompsonAlpha (T : Subgroup G) ⊓
      centralizer ((B ⊓ K).map H.subtype : Set G) ≠ ⊥ := by
    intro he
    exact hfixedG (bot_unique ((inf_le_inf_left _ (centralizer_le (map_mono inf_le_right))).trans he.le))
  exact ctx.original_odd_axis_of_natural_marking D n hn hF e mark hBR q₁ q₂ c'
    ((B ⊓ K).map H.subtype) (map_mono inf_le_left) hfixedP

end CFSG.Quasithin.Chapter10.MovingHall
