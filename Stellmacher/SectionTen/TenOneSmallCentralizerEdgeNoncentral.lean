module
public import Stellmacher.SectionTen.TenOneSmallResidualIntersectionPrimitive
public import Stellmacher.SectionTen.TenOneSmallResidualCentralDisplacement
public import Stellmacher.SectionTen.TenOneSmallPrimitiveCentralizer
public import Stellmacher.SectionTen.TenOneResidualKernelCoreTransfer
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCard
public import Theory.GroupTheory.RelativeCentralLayerCentralizerIndex
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Noncentral edge action on the order-sixteen elementary centralizer

In the actual small first-module case, Wstar of order sixteen has an edge
commutator escaping the middle center. Both the first and terminal edges
are covered, with the latter obtained by actual local conjugation fixing
the middle vertex. This is the noncommutativity step before (8) in
Stellmacher (10.1)(a3), printed p.61 of `refs/files/stellmacher-n-group.pdf`.

Suppose the first edge commutator lies in the middle center. The residual
quotient-action transfer puts Wstar in the first core, and square
preservation refines its first residual-core commutator to the first
central line. The two residual cores have a primitive common element.
Their intersection therefore has order eight: the middle residual product
and the two edge indices exclude containment of the middle residual core
in the first core, giving the upper bound eight. The middle central plane
has index two in this intersection. The relative centralizer bound using
the first central line now gives index at most two in Wstar. Its centralizer
is exactly the middle center by the primitive-point centralizer theorem,
so the same index is four, a contradiction.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_wstar_edge_commutator_not_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Nat.card Wstar = 16 →
      ¬ ⁅Wstar,GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ ZAt ctx.Γ middle := by
  let M := GAt ctx.Γ middle
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ middle
  let Qf := QAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
  let D := twoCoreIn (EAt ctx.Γ middle)
  let Z := ZAt ctx.Γ middle
  let L := ZAt ctx.Γ ctx.criticalPath.firstStep
  let I := R ⊓ D
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  let edge := M ⊓ P
  change Nat.card Wstar=16 → ¬ ⁅Wstar,edge⁆ ≤ Z
  intro hWcard hassume
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQP : Q ≤ P := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle
    ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2
  have hQfM : Qf ≤ M := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    ctx.criticalPath.firstStep middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2
  have hcore (v : ctx.Γ.Vertex) : QAt ctx.Γ v ≤ GAt ctx.Γ v := by
    change ctx.Γ.twoCoreAt v ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hres (v : ctx.Γ.Vertex) : twoCoreIn (EAt ctx.Γ v) ≤ QAt ctx.Γ v := by
    change twoCoreIn (ctx.Γ.twoResidualAt v) ≤ ctx.Γ.twoCoreAt v
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hRQf : R ≤ Qf := hres _
  have hDQ : D ≤ Q := hres _
  have hQfedge : Qf ≤ edge := le_inf hQfM (hcore _)
  have hRedge : R ≤ edge := hRQf.trans hQfedge
  have hDedge : D ≤ edge := hDQ.trans (le_inf (hcore _) hQP)
  have hWP : Wstar ≤ P := (inf_le_left : Wstar ≤ Q).trans hQP
  have hWZ : ⁅Wstar,R⁆ ≤ Z := (Subgroup.commutator_mono le_rfl hRedge).trans hassume
  have hZV : Z ≤ VAt ctx.Γ ctx.criticalPath.firstStep :=
    nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)
  obtain ⟨_,hWelementary,_,hWD,_⟩ :=
    ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  change Wstar ⊓ D = Z at hWD
  let _ : IsElementaryAbelian 2 Wstar := hWelementary
  have hWQf : Wstar ≤ Qf :=
    ten_one_two_subgroup_le_first_core_of_residual_commutator ctx middle hpath hmodel
      Wstar hWP (IsElementaryAbelian.isPGroup 2 Wstar) (hWZ.trans hZV)
  have hWL : ⁅Wstar,R⁆ ≤ L :=
    ten_one_small_residual_commutator_le_first_center ctx middle hpath hsmall hmodel Wstar hWP hWZ
  have hDnot : ¬ D ≤ Qf := by
    intro hle
    have hQQf : Q ≤ Qf := by
      rw [show Q = D ⊔ Wstar from ten_one_small_middle_core_residual_centralizer_product
        ctx middle hpath hsmall hmodel]
      exact sup_le hle hWQf
    have hedge : edge = Qf := by
      rw [show edge = Q ⊔ Qf from (ten_one_middle_edge_core_product ctx middle hpath).symm]
      exact sup_eq_right.mpr hQQf
    have hc : Nat.card edge = 2 * Nat.card Qf := by
      have hh : Nat.card (P ⊓ M : Subgroup G) = 2 * Nat.card Qf :=
        (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
          ctx.criticalPath.firstStep hmodel).edge_card middle (ctx.Γ.adjacent_symm hfirst)
      simpa only [edge,inf_comm] using hh
    rw [hedge] at hc
    have hpos : 0 < Nat.card Qf := Nat.card_pos
    omega
  have hQfindex : (Qf.subgroupOf edge).index = 2 := by
    have hc : Nat.card edge = 2 * Nat.card Qf := by
      have hh : Nat.card (P ⊓ M : Subgroup G) = 2 * Nat.card Qf :=
        (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven
          ctx.criticalPath.firstStep hmodel).edge_card middle (ctx.Γ.adjacent_symm hfirst)
      simpa only [edge,inf_comm] using hh
    have hh := (Qf.subgroupOf edge).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQfedge).toEquiv,hc] at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hh
  have hDindex : (Qf.subgroupOf D).index = 2 := by
    have hh := Subgroup.subgroupOf_index_eq_two (Qf.subgroupOf edge) (D.subgroupOf edge)
      hQfindex (by
        intro hle
        apply hDnot
        intro d hd
        exact hle (show (⟨d,hDedge hd⟩:edge) ∈ D.subgroupOf edge from hd))
    change (Qf.subgroupOf edge).relIndex (D.subgroupOf edge) = 2 at hh
    rw [Subgroup.relIndex_subgroupOf hDedge] at hh
    exact hh
  have hDcard : Nat.card D = 16 := by
    obtain ⟨e⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  have hIQfcard : Nat.card (Qf.subgroupOf D) = 8 := by
    have hh := (Qf.subgroupOf D).index_mul_card
    rw [hDindex,hDcard] at hh
    omega
  have hIupper : Nat.card I ≤ 8 := by
    rw [← hIQfcard,← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show I ≤ D from inf_le_right)).toEquiv]
    exact Subgroup.card_le_of_le (Subgroup.subgroupOf_mono D
      ((inf_le_left : I ≤ R).trans hRQf))
  have hZR : Z ≤ R := hZV.trans
    (ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel)
  have hZD : Z ≤ D := ten_one_middle_center_le_residual_core ctx middle hpath
  have hZI : Z ≤ I := le_inf hZR hZD
  have hZcard : Nat.card Z = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  let _ : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  obtain ⟨x,hxR,hxD,hx2⟩ := ten_one_small_residual_intersection_primitive
    ctx middle hpath hsmall hmodel
  have hxI : x ∈ I := ⟨hxR,hxD⟩
  have hIlower : 4 < Nat.card I := by
    have hlo : 4 ≤ Nat.card I := hZcard ▸ Subgroup.card_le_of_le hZI
    by_contra hnot
    have hIZ : I=Z := (Subgroup.eq_of_le_of_card_ge hZI (by omega)).symm
    have hxZ : x∈Z := hIZ ▸ hxI
    exact hx2 (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Z) x hxZ)
  have hIcard : Nat.card I = 8 := by
    have hdiv : Nat.card I ∣ 16 := hDcard ▸ Subgroup.card_dvd_of_le (inf_le_right : I ≤ D)
    interval_cases h : Nat.card I <;> norm_num at hdiv
    all_goals rfl
  have hZIindex : (Z.subgroupOf I).index = 2 := by
    have hh := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hh
    omega
  have hZcent : Z ≤ Subgroup.centralizer (Q : Set G) := by
    change ZAt ctx.Γ middle ≤ Subgroup.centralizer (QAt ctx.Γ middle : Set G)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
  have hWZcent : Wstar ≤ Subgroup.centralizer (Z : Set G) :=
    (inf_le_left : Wstar ≤ Q).trans (Subgroup.le_centralizer_iff.mp hZcent)
  have hWLcent : Wstar ≤ Subgroup.centralizer (L : Set G) := hWP.trans
    (nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩)
  have hLcard : Nat.card L = 2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext (by rw [ctx.critical_length]; decide)
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩).1
  have hupper : (Subgroup.centralizer (I : Set G)).relIndex Wstar ≤ 2 := by
    rw [← hLcard]
    exact Subgroup.relIndex_centralizer_le_card_of_central_index_two_layer Wstar I Z L
      hWZcent hWLcent hZIindex ((Subgroup.commutator_mono le_rfl inf_le_left).trans hWL)
  have hcent : Wstar ⊓ Subgroup.centralizer (I : Set G) = Z := by
    apply le_antisymm
    · intro w hw
      apply (ten_one_small_primitive_wstar_centralizer ctx middle hpath hsmall hmodel x hxD hx2).le
      exact ⟨hw.1,(Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxI)) hw.2⟩
    · have hZW : Z ≤ Wstar := by rw [← hWD]; exact inf_le_left
      exact le_inf hZW (hZcent.trans (Subgroup.centralizer_le
        ((inf_le_right : I ≤ D).trans hDQ)))
  have hCsub : (Subgroup.centralizer (I : Set G)).subgroupOf Wstar = Z.subgroupOf Wstar := by
    ext w
    constructor
    · intro hw
      exact hcent.le ⟨w.property,hw⟩
    · intro hw
      exact (hcent.ge hw).2
  have hZW : Z ≤ Wstar := by rw [← hWD]; exact inf_le_left
  have hc := ((Subgroup.centralizer (I : Set G)).subgroupOf Wstar).index_mul_card
  rw [hCsub,Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv,hZcard,hWcard] at hc
  change ((Subgroup.centralizer (I : Set G)).subgroupOf Wstar).index ≤ 2 at hupper
  rw [hCsub] at hupper
  omega

public theorem ten_one_small_wstar_terminal_edge_commutator_not_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Nat.card Wstar = 16 →
      ¬ ⁅Wstar,GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a'⁆ ≤ ZAt ctx.Γ middle := by
  let M := GAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  change Nat.card Wstar=16 → ¬ ⁅Wstar,M ⊓ GAt ctx.Γ ctx.criticalPath.a'⁆ ≤ ZAt ctx.Γ middle
  intro hcard hcomm
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
  have hfix : ctx.Γ.act (mover:G) middle=middle :=
    (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp mover.property
  let f := (MulAut.conj (mover:G)⁻¹).toMonoidHom
  have hWnorm : M ≤ Subgroup.normalizer (Wstar : Set G) :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).1
  have hWmap : Wstar.map f=Wstar :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWnorm (M.inv_mem mover.property))
  have hZmap : (ZAt ctx.Γ middle).map f=ZAt ctx.Γ middle :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (stabilizer_le_normalizer_z ctx.Γ middle (M.inv_mem mover.property))
  have hMmap : M.map f=M := by
    change (GAt ctx.Γ middle).map f=GAt ctx.Γ middle
    change conjugateBy (stabilizer ctx.Γ middle) (mover:G)⁻¹=stabilizer ctx.Γ middle
    rw [← stabilizer_act,hfix]
  have hfirstmap : (GAt ctx.Γ ctx.criticalPath.firstStep).map f=
      GAt ctx.Γ ctx.criticalPath.a' := by
    change conjugateBy (stabilizer ctx.Γ ctx.criticalPath.firstStep) (mover:G)⁻¹=
      stabilizer ctx.Γ ctx.criticalPath.a'
    rw [← stabilizer_act,hmove]
  apply ten_one_small_wstar_edge_commutator_not_le_center ctx middle hpath hsmall hmodel hcard
  change ⁅Wstar,M ⊓ GAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ ZAt ctx.Γ middle
  apply (Subgroup.map_le_map_iff_of_injective (f := f) (MulAut.conj (mover:G)⁻¹).injective).mp
  rw [Subgroup.map_commutator,hWmap,
    Subgroup.map_inf M (GAt ctx.Γ ctx.criticalPath.firstStep) f (MulAut.conj (mover:G)⁻¹).injective,
    hMmap,hfirstmap,hZmap]
  exact hcomm

end Stellmacher.SectionTen
