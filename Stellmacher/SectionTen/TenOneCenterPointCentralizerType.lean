module
public import Stellmacher.SectionTen.TenOneSmallDerived
public import Stellmacher.SectionNine.EmbeddedOrderTwoVertex
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Theory.GroupAction.FourGroupOrbit

/-!
# Ambient centralizers of nonidentity middle-center points

In the standing Section Ten geometry, every nonidentity point in the
middle four-center generates the center of some neighboring vertex.
Consequently its full centralizer in the original ambient H has
characteristic two. No small-module assumption is needed for these facts.

The first neighbor center supplies an involution fixed by an edge Sylow
subgroup of the middle stabilizer. Its orbit generates the middle center:
a proper nontrivial closure would be an invariant line, excluded by the
proved middle-center geometry. The four-group orbit theorem then shows
that the orbit contains all three nonidentity points. The same stabilizer
conjugator transports the first neighbor to the required neighbor, with
its center exactly the chosen point's cyclic subgroup. The embedded
order-two-vertex theorem supplies characteristic two for the literal full
ambient centralizer after the given embedding; no hypotheses are moved
from H onto the generated graph group.

Source: Stellmacher (10.1)(a3), printed p.62, the assertion about C_H(v)
preceding (10), and the neighboring center identification used after (11).
The orbit-counting step uses the general four-group theorem, and the
ambient characteristic-two transfer is the proved Section Nine interface.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_center_point_neighbor
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (v : G) (hv : v ∈ ZAt ctx.Γ middle) (hvne : v ≠ 1) :
    ∃ neighbor : ctx.Γ.Vertex, ctx.Γ.adjacent middle neighbor ∧
      ZAt ctx.Γ neighbor = zpowers v := by
  classical
  let P := GAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let L := ZAt ctx.Γ ctx.criticalPath.firstStep
  have hopen := sectionTenOpeningData ctx middle hpath
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hZcard : Nat.card Z = 4 := hopen.center_card
  have hLcard : Nat.card L = 2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext (by rw [ctx.critical_length]; decide)
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩).1
  have hLZ : L ≤ Z := by
    change ZAt ctx.Γ ctx.criticalPath.firstStep ≤ ZAt ctx.Γ middle
    rw [hopen.center_direct_product.1]
    exact le_sup_left
  have hPZ : P ≤ normalizer (Z : Set G) := stabilizer_le_normalizer_z ctx.Γ middle
  let _ := conjMulDistribMulActionOfLeNormalizer P Z hPZ
  let _ : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [hopen.center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  have hLne : L ≠ ⊥ := by intro h; simp [h] at hLcard
  obtain ⟨x,hxne⟩ := ne_bot_iff_exists_ne_one.mp hLne
  let z : Z := ⟨x,hLZ x.property⟩
  have hzne : z ≠ 1 := by intro h; exact hxne (Subtype.ext (congrArg (fun w : Z => (w:G)) h))
  have hz2 : z^2=1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 Z) z
  let O := closure (MulAction.orbit P z)
  let D := O.map Z.subtype
  have hDP : P ≤ normalizer (D : Set G) := by
    change P ≤ normalizer ((closure (MulAction.orbit P z)).map Z.subtype : Set G)
    rw [MonoidHom.map_closure,le_normalizer_closure_iff]
    rintro actor hactor _ ⟨point,hpoint,rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(⟨actor,hactor⟩ : P) • point,
      MulAction.mapsTo_smul_orbit (⟨actor,hactor⟩ : P) z hpoint,?_⟩
    rfl
  have hDne : D ≠ ⊥ := by
    intro hh
    have hm : (z:G) ∈ D := mem_map_of_mem Z.subtype (subset_closure (MulAction.mem_orbit_self z))
    rw [hh] at hm
    exact hzne (Subtype.ext hm)
  have hDcard : Nat.card D = 4 := by
    have hnot2 := ten_one_no_invariant_middle_line ctx middle hpath D
      (map_subtype_le O) hDP
    have hdiv : Nat.card D ∣ 4 := hZcard ▸ card_dvd_of_le (map_subtype_le O)
    have hlo : 1 < Nat.card D := (one_lt_card_iff_ne_bot D).mpr hDne
    have hhi : Nat.card D ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    interval_cases hn : Nat.card D <;> norm_num at hdiv
    all_goals omega
  have hgen : O = ⊤ := by
    apply (card_eq_iff_eq_top (H:=O)).mp
    rw [← card_map_of_injective (K:=O) Z.subtype_injective]
    exact hDcard.trans hZcard.symm
  let edge := P ⊓ GAt ctx.Γ ctx.criticalPath.firstStep
  let TS : Sylow 2 edge := default
  obtain ⟨_,SS,hSS⟩ :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) TS).1
  have hSfirst : (SS : Subgroup P).map P.subtype ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [hSS]
    exact (map_subtype_le (TS : Subgroup edge)).trans inf_le_right
  have hfix (s : SS) : (s:P) • z = z := by
    apply Subtype.ext
    have hs : ((s:P):G) ∈ GAt ctx.Γ ctx.criticalPath.firstStep :=
      hSfirst (mem_map_of_mem P.subtype s.property)
    have hc := (nine_next_center_centralizes_stabilizer
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep
      ⟨1,ctx.Γ.act_one _⟩) hs
    have hh := mem_centralizer_iff.mp hc x x.property
    change ((s:P):G)*(x:G)*((s:P):G)⁻¹=(x:G)
    rw [← hh]
    simp
  obtain ⟨actor,hactor⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_card_four hZcard z hzne hz2 SS hfix hgen
      (⟨v,hv⟩ : Z) (fun hh => hvne (congrArg Subtype.val hh)))
  have hconj : (actor:G)*(x:G)*(actor:G)⁻¹ = v := congrArg Subtype.val hactor
  have hx2 : (x:G)^2=1 := congrArg (fun w : Z => (w:G)) hz2
  have hxGne : (x:G) ≠ 1 := fun hh => hxne (Subtype.ext hh)
  have hLcyc : L = zpowers (x:G) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    rw [hLcard,Nat.card_zpowers,orderOf_eq_prime hx2 hxGne]
  let neighbor := ctx.Γ.act (actor:G)⁻¹ ctx.criticalPath.firstStep
  have hmid : ctx.Γ.act (actor:G)⁻¹ middle = middle := by
    exact (Set.ext_iff.mp (ctx.Γ.stabilizer_def middle) _).mp (P.inv_mem actor.property)
  refine ⟨neighbor,?_,?_⟩
  · change ctx.Γ.adjacent middle (ctx.Γ.act (actor:G)⁻¹ ctx.criticalPath.firstStep)
    have hadj := adjacent_act ctx.Γ (actor:G)⁻¹ hfirst
    rw [hmid] at hadj
    exact hadj
  · change ctx.Γ.z (ctx.Γ.act (actor:G)⁻¹ ctx.criticalPath.firstStep) = _
    rw [z_act,inv_inv]
    change L.map (MulAut.conj (actor:G)).toMonoidHom = _
    rw [hLcyc,MonoidHom.map_zpowers]
    exact congrArg zpowers hconj

public theorem ten_one_center_point_centralizer_characteristic_two
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (v : G) (hv : v ∈ ZAt ctx.Γ middle) (hvne : v ≠ 1) :
    IsCharacteristicTwoType (centralizer ({embedding v} : Set H)) := by
  obtain ⟨neighbor,_,hneigh⟩ := ten_one_center_point_neighbor ctx middle hpath v hv hvne
  have hZelem : IsElementaryAbelian 2 (ZAt ctx.Γ middle) := by
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let _ := hZelem
  have hv2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=ZAt ctx.Γ middle) v hv
  have hcard : Nat.card (ZAt ctx.Γ neighbor) = 2 := by
    rw [hneigh,Nat.card_zpowers,orderOf_eq_prime hv2 hvne]
  have hh := (embedded_orderTwoVertex_residual_subnormal
    ctx.toAmbientSectionNineContext neighbor hcard).2.2
  rw [hneigh,MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure] at hh
  exact hh

end Stellmacher.SectionTen