module
public import Stellmacher.SectionEight.EightTwoFrattiniNeighborJoin
public import BenderSuzuki.External.Huppert.IV.Basic
public import Theory.Frattini.CentralElementarySupplement
public import Stellmacher.SectionEight.EightTwoDistanceTwoDefs
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionEight.EightTwoVZeroCentralSupplement

public import Stellmacher.SectionEight.EightTwoDistanceTwoCenterStructure
public import Stellmacher.SectionEight.EightTwoVZeroFrattiniNontrivial
public import Stellmacher.SectionEight.EightTwoThreeBackwardShifts
public import Stellmacher.SectionEight.EightTwoBackwardModuleGeneration

/-!
# Excluding critical distance two in Stellmacher (8.2)

Under the original local Section Eight context and first-step noncentrality,
the critical path cannot have length two. All backward vertices, cores,
centers and neighbor-center joins remain in the actual supplied graph.

Choose the two backward critical pairs. Their common subgroup
V0 = Va intersect Qm intersect Qfirst is normal in Ga, central in Va and
has index four in Va. The proved quotient-action argument makes Phi(V0)
nontrivial: elementary V0 would force Va elementary, contradicting the
nonzero commutator of its two critical neighbor centers.

A third backward shift puts Vn outside Qm, so Vn and Ga intersect Gm
generate Gm. At the actual second backward vertex n, criticality gives
V0 = Za join (V0 intersect Qn). Since Za is central and elementary in V0,
the ambient Frattini subgroups of V0 and that intersection agree. The
odd-dihedral neighboring-core transfer then centralizes Phi(V0) by Vn.
Characteristicity gives Ga-normality, and the generating equality gives
Gm-normality. The adjacent stabilizers generate the ambient group, forcing
this nontrivial two-subgroup into its trivial two-core, a contradiction.
Only the supplement at this actual n is needed, rather than the source's
more general sentence over all neighbors.

Source: Stellmacher (8.2), Journal of Algebra 190 (1997), printed p.38,
`refs/latex/stellmacher-n-group.tex`. This completes the distance-two
branch; the separate length bound supplies the final distance-one assembly.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext

private theorem frattini_centralizes_second_backward
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : ctx.criticalPath.length = 2)
    (m n : ctx.Γ.Vertex)
    (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (hn : n ∈ neighborhood ctx.Γ m)
    (hcritical : IsCriticalPair ctx.Γ n ctx.criticalPath.a) :
    SectionsFiveToSeven.frattiniAmbient (distanceTwoVZero ctx m) ≤
      Subgroup.centralizer (VAt ctx.Γ n : Set G) := by
  let Γ := ctx.Γ
  let X := distanceTwoVZero ctx m
  have hsup := eight_two_vzero_central_supplement_local ctx hcenter (by omega) m n hm hn hcritical
  have hXQ : X ≤ q Γ m := inf_le_left.trans inf_le_right
  have hpQ : IsPGroup 2 (q Γ m) := by
    rw [q, Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer Γ m)).map (stabilizer Γ m).subtype
  have hpX : IsPGroup 2 X := hpQ.of_injective
    (Subgroup.inclusion hXQ) (Subgroup.inclusion_injective hXQ)
  have hXa : X ≤ q Γ ctx.criticalPath.a :=
    (inf_le_left.trans inf_le_left).trans
      (SevenSix.neighbor_join_le_core_of_length_gt_one Γ ctx.criticalPath (by omega) _)
  have hfirst : ctx.criticalPath.firstStep ∈ neighborhood Γ ctx.criticalPath.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr ctx.criticalPath.firstStep_adj
  have hZa : IsElementaryAbelian 2 (z Γ ctx.criticalPath.a) :=
    SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hcentral : z Γ ctx.criticalPath.a ≤ Subgroup.centralizer (X : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core _ _ hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((SevenSix.centerAmbient_le_centralizer _).trans (Subgroup.centralizer_le hXa)))
  have heq := frattini_map_eq_of_central_elementary_supplement X
    (X ⊓ q Γ n) (z Γ ctx.criticalPath.a) hpX hZa hcentral hsup
  change (frattini X).map X.subtype ≤ _
  rw [heq]
  exact eight_two_frattini_centralizes_neighbor_join_local ctx hcenter n
    (X ⊓ q Γ n) inf_le_right

private theorem contradiction_of_common_normal_frattini
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (m n : ctx.Γ.Vertex) (hm : m ∈ neighborhood ctx.Γ ctx.criticalPath.a)
    (X : Subgroup G) (hX : IsPGroup 2 X)
    (hnormal : NormalIn X (GAt ctx.Γ ctx.criticalPath.a))
    (hne : SectionsFiveToSeven.frattiniAmbient X ≠ ⊥)
    (hcentral : SectionsFiveToSeven.frattiniAmbient X ≤
      Subgroup.centralizer (VAt ctx.Γ n : Set G))
    (hgen : VAt ctx.Γ n ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m) = GAt ctx.Γ m) :
    False := by
  let Γ := ctx.Γ
  let N := SectionsFiveToSeven.frattiniAmbient X
  have hGa : stabilizer Γ ctx.criticalPath.a ≤ Subgroup.normalizer (N : Set G) := by
    have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
    exact hnorm.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        X (frattini X))
  have hGm : stabilizer Γ m ≤ Subgroup.normalizer (N : Set G) := by
    change GAt ctx.Γ m ≤ _
    rw [← hgen]
    exact sup_le ((Subgroup.le_centralizer_iff.mp hcentral).trans
      (Subgroup.centralizer_le_normalizer _)) (inf_le_left.trans hGa)
  let E : Subgroup G := stabilizer Γ ctx.criticalPath.a ⊓ stabilizer Γ m
  let T : Sylow 2 E := default
  have htop : stabilizer Γ ctx.criticalPath.a ⊔ stabilizer Γ m = ⊤ :=
    (edge_sectionThree_data ctx.sectionSeven Γ hm T).2.2.2.2.1
  have hNnormal : N.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (htop ▸ sup_le hGa hGm))
  have hNp : IsPGroup 2 N := (hX.to_subgroup (frattini X)).map X.subtype
  apply hne
  exact le_bot_iff.mp ((show N ≤ pCore 2 G from le_sSup ⟨hNnormal, hNp⟩).trans_eq
    ctx.sectionSeven.twoCore_eq_bot)

public theorem eight_two_critical_distance_ne_two_local
    {G : Type*} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ctx.criticalPath.length ≠ 2 := by
  intro hlen
  obtain ⟨m, n, hm, hn, hgen1, hgen2, hcrit1, hcrit2, _hout1, _hout2⟩ :=
    eight_two_exists_two_backward_shifts_local ctx hcenter (by omega)
  have hlast : ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, by omega⟩ =
      ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_first]
    apply congrArg ctx.criticalPath.path
    apply Fin.ext
    dsimp
    omega
  have hbefore : ctx.criticalPath.path ⟨ctx.criticalPath.length - 2, by omega⟩ =
      ctx.criticalPath.a := by
    rw [← ctx.criticalPath.path_start]
    apply congrArg ctx.criticalPath.path
    apply Fin.ext
    dsimp
    omega
  rw [hlast] at hcrit1 hgen2
  rw [hbefore] at hcrit2
  obtain ⟨hnormal, hcentral, _hdecomp, hindex⟩ :=
    eight_two_distance_two_center_structure_local ctx hcenter hlen m n hm hn
      hgen1 hgen2 hcrit1 hcrit2
  have hne := eight_two_distance_two_vzero_frattini_ne_bot_local ctx hcenter hlen
    m hm hcrit1 hnormal hcentral hindex
  obtain ⟨r, _hr, _hgen3, _hcrit3, _hout3, hVnot⟩ :=
    eight_two_exists_three_backward_shifts_local ctx hcenter hlen m n hm hn hcrit2
  have hgenMiddle := eight_two_backward_module_generates_middle_local ctx hcenter hlen
    m n hm hn hgen2 hVnot
  have hPhi := frattini_centralizes_second_backward ctx hcenter hlen m n hm hn hcrit2
  have hXQ : distanceTwoVZero ctx m ≤ q ctx.Γ m := inf_le_left.trans inf_le_right
  have hpQ : IsPGroup 2 (q ctx.Γ m) := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer ctx.Γ m)).map (stabilizer ctx.Γ m).subtype
  exact contradiction_of_common_normal_frattini ctx m n hm (distanceTwoVZero ctx m)
    (hpQ.to_le hXQ) hnormal hne hPhi hgenMiddle

end Stellmacher.SectionEight
