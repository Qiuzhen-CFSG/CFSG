module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.MovedComparison
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# The single comparison in the actual common overgroup

When K = O²(H), the original Sylow normalizes K. Unique C-component
containment and the source orbit bound make its containing component I
normal in the common maximal two-local subgroup. Thus T intersects I in
an actual Sylow and O₂(I) normalizes K. The original orbit Borel joined
with T is solvable, supplying the actor used by the rank-two quotient
calculation. No Hall placement is assumed here.

Source: Aschbacher–Smith 10.2.3, printed pp.745–746, using 1.2.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The original full Sylow normalizes the single comparison residual. -/
theorem ComparisonConfiguration.single_normalized
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H) :
    (T : Subgroup G) ≤ normalizer (c.component.map H.subtype : Set G) := by
  rw [hsingle]
  have hm := (pResidual 2 H).le_normalizer_map H.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hm
  exact (show (T : Subgroup G) ≤ H from ctx.hstar.1.1.2).trans hm

/-- The containing C-component is normal in the actual common overgroup. -/
theorem ComparisonConfiguration.single_overcomponent_normal
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H) :
    (c.overcomponent.subgroupOf c.ambient).Normal := by
  let M := c.ambient
  let K := (c.component.map H.subtype).subgroupOf M
  let I := c.overcomponent.subgroupOf M
  have hHM : H ≤ M := le_sup_right.trans c.borel_overgroup
  have hTM : (T : Subgroup G) ≤ M := ctx.hstar.1.1.2.trans hHM
  have hKM : c.component.map H.subtype ≤ M := (map_subtype_le _).trans hHM
  have hlocal : K ∈ Chapter1.L M (T.subtype hTM) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hKM).mp ⟨hKM,(c.local_components D).1⟩
  have hSK : (T.subtype hTM : Subgroup M) ≤ normalizer (K : Set M) := by
    rw [←subgroupOf_normalizer_eq hKM]
    exact comap_mono (c.single_normalized D hsingle)
  have hsq := D.simpleQTKE.twoLocal_sqtk c.maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨J,⟨hJ,hKJ⟩,hu⟩ := Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))) hQ (T.subtype hTM) hlocal
  have hI : I = J := hu I ⟨c.overcomponent_mem.2,subgroupOf_mono M c.component_le⟩
  have hn := cComponent_normal_of_unique_of_orbit_two hJ hKJ
    (fun X hX hKX => hu X ⟨hX,hKX⟩) (T.subtype hTM) hSK
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hJ)
  change I.Normal
  rw [hI]
  exact hn

/-- In the single row the original Sylow normalizes the containing component. -/
theorem ComparisonConfiguration.single_overcomponent_normalized
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H) :
    (T : Subgroup G) ≤ normalizer (c.overcomponent : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer c.overcomponent_mem.1).mp
    (c.single_overcomponent_normal D hsingle)
  exact ctx.hstar.1.1.2.trans ((le_sup_right.trans c.borel_overgroup).trans hn)

/-- The actual Borel joined with the Sylow is solvable. -/
theorem original_borel_sylow_solvable
    (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Group.IsSolvable (sourceOrbitBorel T L ⊔ (T : Subgroup G) : Subgroup G) := by
  let := CentralHall.Nonlinear.HallGeometry.source_sl2_borel_solvable D e ctx.nonnormal
  let := T.isPGroup'.isNilpotent
  exact Group.isSolvable_sup_of_normalizes _ _ source_original_sylow_normalizes_borel

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement

namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- The full original Sylow intersects the containing component in a Sylow. -/
theorem ComparisonConfiguration.single_sylow
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H) :
    ∃ S : Sylow 2 c.overcomponent,
      (S : Subgroup c.overcomponent) = (T : Subgroup G).subgroupOf c.overcomponent := by
  have hTM : (T : Subgroup G) ≤ c.ambient :=
    (show (T : Subgroup G) ≤ H from ctx.hstar.1.1.2).trans (le_sup_right.trans c.borel_overgroup)
  let I := c.overcomponent.subgroupOf c.ambient
  let := c.single_overcomponent_normal D hsingle
  obtain ⟨S,hS⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal I
  let e := subgroupOfEquivOfLe c.overcomponent_mem.1
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (S : Subgroup I).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,c.overcomponent_mem.1 x.property⟩,x.property⟩,hx,rfl⟩

/-- The two-core normalizes the original perfect comparison, before taking any quotient. -/
theorem ComparisonConfiguration.single_core_normalizes
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H) :
    c.overcomponent.pCoreIn 2 ≤ normalizer (c.component.map H.subtype : Set G) := by
  obtain ⟨S,hS⟩ := c.single_sylow D hsingle
  have hc : pCore 2 c.overcomponent ≤ (T : Subgroup G).subgroupOf c.overcomponent :=
    hS ▸ pCore_isPGroup.le_sylow_of_normal S
  have hm := map_mono (f := c.overcomponent.subtype) hc
  have ht : ((T : Subgroup G).subgroupOf c.overcomponent).map c.overcomponent.subtype ≤
      (T : Subgroup G) := by
    rw [subgroupOf_map_subtype]
    exact inf_le_left
  exact hm.trans (ht.trans (c.single_normalized D hsingle))
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
