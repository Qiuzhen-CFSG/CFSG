module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SixCycle.Source
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.Placement.QuotientMove
public import Theory.Combinatorics.SimpleGraph.SixCycle.OppositeSwap
public import Theory.SpecificGroups.SymmetricFive.PentagonSwap
/-!
# From the original S5 actor to parabolic five-placement

The source quotient inverter is even because it is the square of the original
order-four root. A distinct commuting quotient involution therefore moves its
two inverted pentagons. Canonical color transport turns this into exchange of
the opposite zu-colored vertices of the proved six-cycle. The source actor
sends z to u, excluding the opposite z vertex, so the marked opposite-pair
lemma sends F1 to its unique u-colored neighbor. That neighbor contains the
original fixed five C_P(u).

All input quotient elements are values of the original H/Q map. No ambient
SL2-factor normalization, Small, or global recognition is required.
Source: Aschbacher--Smith proof of J.4.7, printed pp.444--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (p:Plane d) (s:SourceChoice p) (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
  (e:first≃*p.F₁ B5) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
  (hfive:(zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include hz in
theorem actor_normalizes_pair (j:G) (hjz:j*c.z*j⁻¹=sourceU e)
    (hjt:j*(c.z*sourceU e)*j⁻¹=c.z*sourceU e) :
    j∈normalizer (pairSpan c.z (sourceU e):Set G) := by
  obtain ⟨_,_,_,hcomm⟩:=source_pair_marks p B5 c e hz
  have hju:j*sourceU e*j⁻¹=c.z := by
    have he:(sourceU e)*(j*sourceU e*j⁻¹)=c.z*sourceU e := by
      calc
        _=(j*c.z*j⁻¹)*(j*sourceU e*j⁻¹):=by rw [hjz]
        _=j*(c.z*sourceU e)*j⁻¹:=by group
        _=c.z*sourceU e:=hjt
    apply mul_left_cancel (a:=sourceU e)
    exact he.trans hcomm.eq
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [pairSpan,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    change zpowers (j*c.z*j⁻¹)⊔zpowers (j*sourceU e*j⁻¹)≤_
    rw [hjz,hju]
    exact sup_le le_sup_right le_sup_left
  · rw [card_map_of_injective (MulAut.conj j).injective]

include q s hi f hleft hz hfive in
theorem fixedFive_le_conjugate_of_color_move (j:G)
    (hjz:j*c.z*j⁻¹=sourceU e) (hjt:j*(c.z*sourceU e)*j⁻¹=c.z*sourceU e)
    (hmove:∀E∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e),E.conjBy j≠E) :
    fixedFive B5 (sourceU e)≤(p.F₁ B5).conjBy j := by
  obtain ⟨ι,h0,hcol,h1,_,_⟩:=SixCycle.source_cycle_iso q p s c B5 hi e f hleft hz hfive
  have hjN:=actor_normalizes_pair p c B5 e hz j hjz hjt
  let a:=sourceGraphEquiv p B5 c e hz j hjN
  have hc0:((ι 0):Subgroup G)∈colorFamily p B5 c.z (sourceU e) c.z:=hcol 0
  have hc2:((ι 2):Subgroup G)∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e):=hcol 2
  have hc5:((ι 5):Subgroup G)∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e):=hcol 5
  have h5:(a (ι 5):Subgroup G)∈colorFamily p B5 c.z (sourceU e) (c.z*sourceU e) := by
    rw [sourceGraphEquiv_apply]
    simpa only [hjt] using color_conjugate_mem p B5 c.z (sourceU e) j hjN hc5
  have h52:a (ι 5)=ι 2 := by
    let C:=colorFamily p B5 c.z (sourceU e) (c.z*sourceU e)
    have hc:Nat.card C=2:=source_color_family_card q p s c B5 hi e f hleft hz hfive _ (by simp [colors])
    let x:C:=⟨ι 5,hc5⟩
    let y:C:=⟨ι 2,hc2⟩
    let z:C:=⟨a (ι 5),h5⟩
    have hy:y≠x:=by
      intro h
      have h':ι 2=ι 5:=Subtype.ext (congrArg (fun A:C=>(A:Subgroup G)) h)
      exact (by decide: (2:Fin 6)≠5) (ι.injective h')
    have hz':z≠x:=by
      intro h
      have he:((ι 5:globalFamily p B5 c.z (sourceU e)):Subgroup G).conjBy j=ι 5:=
        (sourceGraphEquiv_apply p B5 c e hz j hjN (ι 5)).symm.trans (congrArg (fun A:C=>(A:Subgroup G)) h)
      exact hmove _ (hcol 5) he
    obtain ⟨w,_,hw⟩:=(Nat.card_eq_two_iff' x).mp hc
    exact Subtype.ext (congrArg (fun A:C=>(A:Subgroup G)) ((hw z hz').trans (hw y hy).symm))
  have h03:a (ι 0)≠ι 3 := by
    have hu:(a (ι 0):Subgroup G)∈colorFamily p B5 c.z (sourceU e) (sourceU e) := by
      rw [sourceGraphEquiv_apply]
      simpa only [hjz] using color_conjugate_mem p B5 c.z (sourceU e) j hjN hc0
    intro he
    have hn:sourceU e≠c.z:=(source_pair_marks p B5 c e hz).2.2.1.symm
    exact Set.disjoint_left.mp (colorFamily_disjoint p B5 c e hz hn) hu
      ((congrArg Subtype.val he).symm ▸ hcol 3)
  have hadj:=SimpleGraph.SixCycle.opposite_swap_neighbor _ ι a h52 h03
  have he:=congrArg Subtype.val hadj
  rw [h0,sourceGraphEquiv_apply,baseVertex_coe] at he
  exact h1.trans_eq he.symm

include hz hfive in
theorem sourceInverter_even :
    d.ru2.quotientMap (sourceInverter p B5 e)∈alternatingGroup (Fin 5) := by
  obtain ⟨t,_,ht2,_,_,_⟩:=source_quotient_pentagons c B5 e hz hfive
  have he:t^2=sourceInverter p B5 e:=Subtype.ext ht2
  rw [←he,map_pow]
  apply Equiv.Perm.mem_alternatingGroup.mpr
  rw [map_pow,Int.units_sq]

include q s hi f hleft hz hfive in
theorem fixedFive_le_conjugate_of_quotient_actor (j k:G)
    (hjz:j*c.z*j⁻¹=sourceU e) (hjt:j*(c.z*sourceU e)*j⁻¹=c.z*sourceU e)
    (hk:k∈normalizer (pairSpan c.z (sourceU e):Set G))
    (hkcolor:k*(c.z*sourceU e)*k⁻¹=c.z)
    (a:d.toTypeRuSetup.H) (ha:(a:G)=k*j*k⁻¹)
    (hao:orderOf (d.ru2.quotientMap a)=2)
    (hane:d.ru2.quotientMap a≠d.ru2.quotientMap (sourceInverter p B5 e))
    (hac:Commute (d.ru2.quotientMap (sourceInverter p B5 e)) (d.ru2.quotientMap a)) :
    fixedFive B5 (sourceU e)≤(p.F₁ B5).conjBy j := by
  apply fixedFive_le_conjugate_of_color_move q p s c B5 hi e f hleft hz hfive j hjz hjt
  apply color_member_moved_of_quotient p s B5 hi c e hz hfive k j hk hkcolor a ha
  intro P hP
  have hiP:= (source_family_mem_iff_inverts p s B5 hi c e hz hfive P).mp
    ((source_family_mem_iff p s B5 hi c e hz hfive P).mpr hP)
  exact Theory.SpecificGroups.SymmetricFive.PentagonSwap.moves_inverted_sylow _ _
    (source_quotient_order_two p B5 c e hz hfive) (sourceInverter_even p c B5 e hz hfive)
    hao hane hac P hiP
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
