module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearCoverage
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.QuasisimpleLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.LocalAmbient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
/-!
# Actual H* component coverage for the common characteristic pair

Over an arbitrary even field, the single natural source selects O²(H). The paired source keeps its actual
perfect component and Sylow exchanger, intrinsic SL₂ quotient, and positive
alpha fixed subgroup. Both supply K join S = H, the literal generation
premise of the common characteristic-pair block alternative. The earlier
Hall-action seed-centralizer identity remains with the moving-Hall owner.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterE ChapterE.ThompsonAction
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)


set_option backward.isDefEq.respectTransparency false in
/-- The same selected component retains generation, localV and its natural quotient. -/
theorem Context.hstar_component_coverage_of_seed_centralizer
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
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧
      (K = pResidual 2 H ∨
        ((thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥) ∧
          (∃ E : BinaryField, Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier))) ∧
          ∃ t ∈ (S : Subgroup H),
            pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)) := by
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
      by rw [normalizer_eq_top]; exact le_top,hlocal,hv,
      pResidual_sup_sylow_eq_top S,Or.inl rfl⟩
  · have hkc : q.ker = pCore 2 H := hk.trans
      (source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar hCZ)
    obtain ⟨K₀,hK,_,_,hUK,hBK,hlocal,hv,hfixed,heq,hgen,ht⟩ :=
      first_component_localClass_with_coverage h36 hsq S hP U hU hJ q hq hk hkc
        hs hfit d K c hexchange
    exact ⟨K₀,hK,hUK,hBK,hlocal,hv,hgen,Or.inr ⟨hfixed,⟨K,heq⟩,ht⟩⟩

end CFSG.Quasithin.Chapter10.MovingHall
