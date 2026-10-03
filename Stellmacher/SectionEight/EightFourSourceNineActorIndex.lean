module
public import Stellmacher.SectionEight.EightFourStarResidualAction
public import Stellmacher.SectionEight.EightFourSourceNineRestrictedCommutation
public import Stellmacher.SectionEight.EightFourShiftedCenterAction
public import Stellmacher.SectionThree.PSetFixedHyperplaneActor

/-!
# The shifted actor index in Stellmacher (8.4)

The actual restricted commutation theorem gives common fixed index two for
the shifted center acting on the first-step star. The star is elementary
and normal in the first-step stabilizer. Its residual action is nontrivial:
otherwise the original fixed seed would be normal, contrary to the strict
normal-closure branch.

Apply the intrinsic solvable PSet fixed-hyperplane theorem to this exact
star and actor. Its proof constructs a residual-active irreducible section,
derives the faithful action and fixed-generation hypotheses of (1.2), and
controls the actor kernel by the local two-core. This gives actor index at
most two. The proved shifted-center noncontainment excludes index one,
and finiteness excludes index zero.

All original source-nine arguments are retained. No actor index, rank,
fixed-space generation, or local normality is added as a hypothesis.
Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40/PDF p.30,
(8.4), the application of (1.2) immediately after the R1 argument.

The local versions retain all graph, witness and source-nine data, with the
same explicit conditional inputs. Original canonical statements are exact
wrappers through the local context and fieldwise configuration conversion.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The shifted center has index two over its first-step core intersection. -/
public theorem eight_four_source_nine_actor_index_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    (ZAt ctx.Γ next ⊓ QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      (ZAt ctx.Γ next) = 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C := ⨆ vertex, F vertex cp.firstStep
  let next := Γ.act configuration.y⁻¹ cp.a'
  let h := ctx.sectionSeven
  have hrestricted := eight_four_source_nine_restricted_commutation_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hfixed := (eight_four_source_nine_index_two_of_restricted_commutation_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen hrestricted).2.2.2
  have haction := eight_four_source_nine_shifted_center_action_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hnormal := (eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula).2.2.2
  have helementary := (eight_four_star_elementary_core_local ctx hcenter w hbranch
    F hbase hcov hsub hformula cp.firstStep).1
  have hactor : IsElementaryAbelian 2 (ZAt Γ next) :=
    SevenSix.z_isElementaryAbelian_of_neighbor h Γ
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm configuration.hadj))
  have hseedC : w.oneJFixedPoints S ≤ C := by
    rw [← hbase]
    exact le_iSup (fun vertex => F vertex cp.firstStep) cp.a
  have hres := eight_four_fixed_overgroup_residual_action_nontrivial_local
    ctx hcenter w hbranch C hseedC
  have hlocal := (SevenSix.edge_local_data h Γ cp).2
  have hbound := SectionThree.pSet_fixed_hyperplane_actor_bound
    S (GAt Γ cp.firstStep) C (ZAt Γ next)
    (SevenSix.sectionThreeHypotheses h) ((pFamily_iff_pSet _ _ _).mp hlocal.1)
    hlocal.2 (hnormal cp.firstStep).1 (hnormal cp.firstStep).2
    helementary hactor haction.2.1 hres hfixed
  have hQ : QAt Γ cp.firstStep = twoCoreAmbient (GAt Γ cp.firstStep) :=
    Γ.twoCoreAt_def cp.firstStep
  rw [← hQ] at hbound
  have hpositive : (ZAt Γ next ⊓ QAt Γ cp.firstStep).relIndex (ZAt Γ next) ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have hnotone : (ZAt Γ next ⊓ QAt Γ cp.firstStep).relIndex (ZAt Γ next) ≠ 1 := by
    intro hone
    exact haction.2.2.1 ((Subgroup.relIndex_eq_one.mp hone).trans inf_le_right)
  change (ZAt Γ next ⊓ QAt Γ cp.firstStep).relIndex (ZAt Γ next) = 2
  omega



/-- Canonical specializations retaining the same actual witness and configuration. -/
public theorem eight_four_source_nine_actor_index
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    (ZAt ctx.Γ next ⊓ QAt ctx.Γ ctx.criticalPath.firstStep).relIndex
      (ZAt ctx.Γ next) = 2 := by
  exact eight_four_source_nine_actor_index_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end Stellmacher.SectionEight
