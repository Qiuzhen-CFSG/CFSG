module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.SourceSelection
public import Theory.GroupTheory.NormalFourCentralizer
/-!
# The actual centralizer-order comparison in 13.5.6

The Sylow image of the original natural action has order at least eight,
since its range contains A₆. A two-group fixing a nondegenerate plane has
image of order at most two. Comparing the common action kernel shows that
C_T(W) has index at least four in T. In contrast, the original invariant
four-group V₂ has centralizer of index at most two in T.

Source: Aschbacher--Smith 13.5.6, printed p.917. These are the actual order
bounds needed for normalizer escape; no centralizer order is an input.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
open Section08.SourceCompletion Section07.NaturalAction
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
local notation "H" => (L⊔(T:Subgroup G):Subgroup G)

theorem sylow_permutation_image_card_ge_eight :
    8≤Nat.card (((T:Subgroup G).subgroupOf H).map (permutation d)) := by
  let f:=permutation d
  let P: Sylow 2 f.range := (T.subtype le_sup_right).mapSurjective f.rangeRestrict_surjective
  have hdiv:8∣Nat.card f.range := by
    have hdiv:=card_dvd_of_le (alternating_le_range d)
    have hc:Nat.card (alternatingGroup (Fin 6))=360:=by
      rw [nat_card_alternatingGroup,Nat.card_fin];decide
    rw [hc] at hdiv
    exact (by decide:8∣360).trans hdiv
  have hP:8∣Nat.card P:=P.pow_dvd_card_of_pow_dvd_card (n:=3) hdiv
  have hp:0<Nat.card P:=Nat.card_pos
  have hh:(P:Subgroup f.range).map f.range.subtype=
      ((T:Subgroup G).subgroupOf H).map f := by
    rw [Sylow.coe_mapSurjective,map_map,Sylow.coe_subtype]
    rfl
  rw [←hh,card_map_of_injective f.range.subtype_injective]
  exact Nat.le_of_dvd hp hP

theorem planeCentralizer_image_card_le_two (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0) :
    Nat.card (planeCentralizerImage d W)≤2 := by
  rcases planeCentralizer_image_cases d W hWV hcard hn with hb|⟨r,hr,hR⟩
  · rw [hb]
    have hc:Nat.card (⊥:Subgroup (Equiv.Perm (Fin 6)))=1:=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
    omega
  · rw [hR,Nat.card_zpowers,hr.orderOf]

/-- A nondegenerate plane has Sylow centralizer of index at least four. -/
theorem planeCentralizer_relIndex_ge_four (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0) :
    4≤(planeCentralizer (T:=T) W).relIndex (T:Subgroup G) := by
  let B:Subgroup H:=(T:Subgroup G).subgroupOf H
  let A:Subgroup H:=(planeCentralizer (T:=T) W).subgroupOf H
  let K:Subgroup H:=B⊓(permutation d).ker
  have hAB:A≤B:=fun _ h=>h.1
  have hKA:K≤A:=by
    rintro x ⟨hx,hk⟩
    refine ⟨hx,?_⟩
    intro v hv
    have hh:=conjugation d x ⟨v,hWV hv⟩
    rw [show permutation d x=1 from hk,map_one,Module.End.one_apply] at hh
    have hh':x.val*v*x.val⁻¹=v:=congrArg Subtype.val (d.coordinate.injective hh)
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hAK:A⊓(permutation d).ker=K:=by
    apply le_antisymm
    · exact inf_le_inf_right _ hAB
    · exact le_inf hKA inf_le_right
  have hmult:=relIndex_mul_relIndex K A B hKA hAB
  have hkA:K.relIndex A=Nat.card (A.map (permutation d)):=by
    rw [←hAK,inf_relIndex_left,relIndex_ker]
  have hkB:K.relIndex B=Nat.card (B.map (permutation d)):=by
    change (B⊓(permutation d).ker).relIndex B=_
    rw [inf_relIndex_left,relIndex_ker]
  rw [hkA,hkB] at hmult
  have hlo:=sylow_permutation_image_card_ge_eight d
  have hhi:=planeCentralizer_image_card_le_two d W hWV hcard hn
  have hABi:A.relIndex B=(planeCentralizer (T:=T) W).relIndex (T:Subgroup G):=
    relIndex_subgroupOf le_sup_right
  change Nat.card (A.map (permutation d))≤2 at hhi
  change 8≤Nat.card (B.map (permutation d)) at hlo
  rw [hABi] at hmult
  nlinarith

theorem four_mul_card_planeCentralizer_le_sylow (W:Subgroup G)(hWV:W≤V)(hcard:Nat.card W=4)
    (hn:¬∀x∈image d W,∀y∈image d W,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form x y=0) :
    4*Nat.card (planeCentralizer (T:=T) W)≤Nat.card T := by
  have hr:=planeCentralizer_relIndex_ge_four d W hWV hcard hn
  have hc:=relIndex_mul_relIndex (⊥:Subgroup G) (planeCentralizer (T:=T) W)
    (T:Subgroup G) bot_le inf_le_left
  simp only [relIndex_bot_left] at hc
  nlinarith

theorem sylow_le_two_mul_card_seedPlaneCentralizer :
    Nat.card T≤2*Nat.card (planeCentralizer (T:=T) V₂) := by
  let := elementary d
  let : IsElementaryAbelian 2 V₂:=IsElementaryAbelian.of_le (d.plane_le_seed.trans d.seed_le)
  have hVT:V₂≤(T:Subgroup G):=d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow)
  let D:Subgroup T:=V₂.subgroupOf T
  let e:D≃*V₂:=subgroupOfEquivOfLe hVT
  let : IsElementaryAbelian 2 D:=IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  let : D.Normal:=normal_subgroupOf_of_le_normalizer d.plane_stable
  have hd:Nat.card D=4:=(Nat.card_congr e.toEquiv).trans d.plane_card
  have hi:=centralizer_index_le_two_of_normal_four T.isPGroup' D hd
  have he:centralizer (D:Set T)=(planeCentralizer (T:=T) V₂).subgroupOf T := by
    ext t
    constructor
    · intro ht
      refine ⟨t.property,?_⟩
      intro v hv
      exact congrArg Subtype.val (ht ⟨v,hVT hv⟩ hv)
    · intro ht v hv
      exact Subtype.ext (ht.2 v.val hv)
  have hc:Nat.card (centralizer (D:Set T))=Nat.card (planeCentralizer (T:=T) V₂):=
    Nat.card_congr ((MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe inf_le_left)).toEquiv
  have hm:=card_mul_index (centralizer (D:Set T))
  rw [hc] at hm
  nlinarith
end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry
