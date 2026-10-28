module
public import Stellmacher.SectionTen.TenOneSmallCommonCorePointFixed
public import Stellmacher.SectionTen.TenOneSmallLocalCentralizerCore
public import Stellmacher.SectionTen.TenOneSmallNeighborMaximalElementary
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.CentralEightPointCentralizer
public import Stellmacher.SectionTen.TenOneSmallTerminalCorePacket

/-!
# The terminal-core centralizer of a noncentral common-core point

In the actual order-eight first-module and SL2(2) case of Section Ten,
let W0 be the intersection of the middle neighborhood core intersection
with its generated module. For every a in W0 outside the middle center,
C_Qterminal(a) lies in the terminal residual two-core. The original
ambient context, graph subgroups, and point are retained throughout.

Put C=C_Qterminal(Vterminal). The initial-orbit edge centralizer theorem
places C in Qmiddle. Its intersection with the elementary Wstar centralizes
Vterminal, so joining them gives an elementary subgroup of Qmiddle.
The proved maximality of the neighbor module puts that intersection in
Vterminal. The two actual point-centralizer formulas now identify C_C(a)
with Zmiddle, and the middle class-two theorem puts every [a,c] there.
The transported terminal structure packet supplies the residual order,
center, module action, self-centralizer, and core order bound. The generic
central-eight point-centralizer theorem combines these data: its square
argument first derives a's residual-core membership and then the asserted
bound for every element centralizing a.

Source: Stellmacher (10.1)(a3)(11), Journal of Algebra190 (1997), printed
p.62, the abbreviated assertion C_Qterminal(a)≤O2(Eterminal). In particular,
no containment of W0 in the terminal residual core is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem terminal_middle_centralizer_data
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a:G)
    (ha : a∈NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle)⊓
      GeneratedNeighborhoodV ctx.Γ middle)
    (haZ : a∉ZAt ctx.Γ middle) :
    let Q := QAt ctx.Γ ctx.criticalPath.a'
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let C := Q⊓centralizer (V:Set G)
    C⊓centralizer ({a}:Set G)=ZAt ctx.Γ middle ∧
      (∀c∈C,⁅a,c⁆∈ZAt ctx.Γ middle) ∧ a∈Q ∧ a^2=1 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := QAt Γ cp.a'
  let V := VAt Γ cp.a'
  let C := Q⊓centralizer (V:Set G)
  let M := QAt Γ middle
  let Z := ZAt Γ middle
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle)⊓GeneratedNeighborhoodV Γ middle
  let Wstar := M⊓centralizer (W0:Set G)
  change C⊓centralizer ({a}:Set G)=Z ∧ (∀c∈C,⁅a,c⁆∈Z) ∧ a∈Q ∧ a^2=1
  have hb : 2<cp.length := by change 2<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨horbit,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hW0M : W0≤M := inf_le_right.trans
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  have hW0Q : W0≤Q := inf_le_left.trans
    (sInf_le ⟨cp.a',(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩)
  have hW0e := (ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel).2.1
  let _ : IsElementaryAbelian 2 W0 := hW0e
  have hW0W : W0≤Wstar := le_inf hW0M (le_centralizer W0)
  have haW : a∈Wstar := hW0W ha
  have haM : a∈M := hW0M ha
  have hZV : Z≤V := nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal)
  have hVM : V≤M := (show V≤GeneratedNeighborhoodV Γ middle from
    le_sSup ⟨cp.a',(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩).trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  have hVQ : V≤Q := neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.a'
  have hVe : IsElementaryAbelian 2 V := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case (by omega)).1
    change IsElementaryAbelian 2 (v Γ cp.a')
    rw [←hmove,v_act]
    exact IsElementaryAbelian.map _
  let _ := hVe
  have hCM : C≤M :=
    (inf_le_inf_left Q (centralizer_le hZV)).trans
      (nine_three_orbit_edge_core_centralizer ctx.toLocalContext.toSectionNineLocalContext
        middle horbit cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal))
  have hVC : V≤C := le_inf hVQ (le_centralizer V)
  have hVfixed : V⊓centralizer ({a}:Set G)=Z :=
    ten_one_small_common_core_point_terminal_fixed ctx middle hpath hsmall hmodel a ha haZ
  have hWfixed : M⊓centralizer ({a}:Set G)=Wstar :=
    ten_one_small_core_point_centralizer ctx middle hpath hsmall hmodel a haW haZ
  have hWe : IsElementaryAbelian 2 Wstar :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.1
  let _ := hWe
  let K := C⊓Wstar
  let _ : IsElementaryAbelian 2 K := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (setLike_mul_comm (s:=Wstar) x.property.2 y.property.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun k =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Wstar) k k.property.2)) }
  let _ : IsElementaryAbelian 2 (V⊔K : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (inf_le_left.trans (show C≤centralizer (V:Set G) from inf_le_right))
  have hmax : V⊔K=V := ten_one_small_neighbor_module_maximal_elementary
    ctx middle hpath hsmall hmodel cp.a' hterminal (V⊔K) le_sup_left
      (sup_le hVM ((inf_le_left:K≤C).trans hCM))
  have hKV : K≤V := hmax ▸ le_sup_right
  have hfixed : C⊓centralizer ({a}:Set G)=Z := by
    apply le_antisymm
    · intro c hc
      have hcK : c∈K := ⟨hc.1,hWfixed.le ⟨hCM hc.1,hc.2⟩⟩
      exact hVfixed.le ⟨hKV hcK,hc.2⟩
    · intro z hz
      exact ⟨hVC (hVfixed.ge hz).1,(hVfixed.ge hz).2⟩
  refine ⟨hfixed,?_,hW0Q ha,elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=W0) a ha⟩
  intro c hc
  exact ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel
    (commutator_mem_commutator haM (hCM hc))

public theorem ten_one_small_terminal_core_centralizer_le_residual
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a:G)
    (ha : a∈NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle)⊓
      GeneratedNeighborhoodV ctx.Γ middle)
    (haZ : a∉ZAt ctx.Γ middle) :
    QAt ctx.Γ ctx.criticalPath.a'⊓centralizer ({a}:Set G)≤
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') := by
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.a'
  let L := ZAt ctx.Γ middle
  obtain ⟨hRQ,hVR,hRcard,hVcard,hVe,hQcard,hRN,hZcentral,hZV,hZcard,hcomm,hself,hcenter,hderived⟩ :=
    ten_one_small_terminal_core_packet ctx middle hpath hsmall hmodel
  let _ := hVe
  have hrelativeCenter : R⊓centralizer (R:Set G)=Z := by
    change CenterAmbient R=Z at hcenter
    rw [←hcenter]
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
      intro r
      exact Subtype.ext (mem_centralizer_iff.mp hc r r.property)
    · rintro ⟨r,hr,rfl⟩
      refine ⟨r.property,mem_centralizer_iff.mpr ?_⟩
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hr ⟨y,hy⟩)
  obtain ⟨hfixed,hvalue,haQ,ha2⟩ :=
    terminal_middle_centralizer_data ctx middle hpath hsmall hmodel a ha haZ
  have hLV : L≤V := nine_seven_neighbor_center_le_module ctx.Γ
    (ctx.Γ.adjacent_symm (sectionTenOpeningGeometry ctx middle hpath).2.2.1)
  have hLcard : Nat.card L=4 := (sectionTenOpeningData ctx middle hpath).center_card
  exact Subgroup.inf_centralizer_le_of_central_eight Q R V Z L
    hRQ hVR hRN hVcard hRcard hQcard hZV hZcard hZcentral hcomm hself
    hrelativeCenter hderived a haQ ha2 hLV hLcard hfixed hvalue
end Stellmacher.SectionTen
