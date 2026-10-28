module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.NormalFourCentralizerSeparation
/-! # The original central-core involution and its full ambient centralizer
A nontrivial normal subgroup of a finite two-group meets its center.
Choose an involution in the intersection of the original two-core and Sylow
center. Source 2.5.6 applies to its cyclic subgroup, giving the exact ambient
centralizer, the original Sylow image and preservation of the starred choice.
Comparing Sylow orders separates this involution from the original mark z.
This proves source 2.5.11(2), without assuming the later center-order conclusion.
Source: Aschbacher--Smith, printed p.557.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.central_core_involution_centralizer
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2)
    (htC:t∈twoCore H) (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    H≤centralizer ({t}:Set G) ∧
      centralizer ({t}:Set G)∈gammaZero (Chapter1.He G) M ∧
      (∃P:Sylow 2 (centralizer ({t}:Set G)),
        (P:Subgroup (centralizer ({t}:Set G))).map (centralizer ({t}:Set G)).subtype=
          (S:Subgroup H).map H.subtype) ∧
      (H∈gammaStar (Chapter1.He G) M→centralizer ({t}:Set G)∈gammaStar (Chapter1.He G) M) ∧
      ¬IsConj t z := by
  let Y:=(S:Subgroup H).map H.subtype
  let E:=zpowers t
  have ht1:t≠1:=by intro he;rw [he,orderOf_one] at ht;omega
  have hE:E≠⊥:=by intro he;exact ht1 (mem_bot.mp (he ▸ mem_zpowers t))
  have htL:t∈centralizer (L:Set G):=by
    have hc:=generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
    rw [←hc] at htC
    exact (centralizer_le (le_componentOrbit L Y)) htC.2
  have hEC:E≤Y⊓centralizer (L:Set G):=zpowers_le.mpr ⟨htZ.1,htL⟩
  have hYE:Y≤normalizer (E:Set G):=by
    rw [normalizer_zpowers_eq_centralizer_of_order_two t ht]
    exact fun a ha=>mem_centralizer_singleton_iff.mpr (htZ.2 a ha)
  have hH:=normalizes_centralizer_subgroup hgen hEC hYE
  have hc:=centralizer_subgroup_normalizer (MathieuSourceSetup.sourceTuple c) hgen hE hEC hYE
  rw [normalizer_zpowers_eq_centralizer_of_order_two t ht] at hH hc
  obtain ⟨hgamma,⟨P,hP⟩,hstar,_⟩:=hc
  refine ⟨hH,hgamma,⟨P,hP⟩,hstar,?_⟩
  have hYt:Y≤centralizer ({t}:Set G):=by rw [show Y=(S:Subgroup H).map H.subtype from rfl,←hP];exact map_subtype_le _
  have hTz:(c.T:Subgroup G)≤centralizer ({z}:Set G):=by
    intro a ha
    obtain ⟨w,hw,he⟩:=c.mem_center
    have hh:=congrArg Subtype.val (mem_center_iff.mp hw ⟨a,ha⟩)
    change a*(w:G)=(w:G)*a at hh
    change (w:G)=z at he
    exact mem_centralizer_singleton_iff.mpr (he ▸ hh)
  have hmax:¬2∣Y.relIndex (centralizer ({t}:Set G)):=by
    rw [show Y=(S:Subgroup H).map H.subtype from rfl,←hP]
    change ¬2∣(((P:Subgroup (centralizer ({t}:Set G))).map
      (centralizer ({t}:Set G)).subtype).subgroupOf (centralizer ({t}:Set G))).index
    rw [subgroupOf,comap_map_eq_self_of_injective (centralizer ({t}:Set G)).subtype_injective]
    exact P.not_dvd_index
  apply not_isConj_of_sylow_centralizer_card_lt t z Y c.T
    (S.isPGroup'.map H.subtype) c.T.isPGroup' hYt hTz hmax
  exact lt_of_le_of_ne (card_le_of_le c.sylow_lt.le)
    (fun h=>c.sylow_lt.ne (eq_of_le_of_card_ge c.sylow_lt.le h.ge))

/-- Choose the central-core involution directly from the original source tuple. -/
theorem MathieuSourceSetup.exists_central_core_involution
    (c:MathieuSourceSetup H L M S z) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧
      t∈centerIn ((S:Subgroup H).map H.subtype) := by
  let Y:=(S:Subgroup H).map H.subtype
  let C:=twoCore H⊓centerIn Y
  have hQ:twoCore H≠⊥:=(c.gamma.elim (fun h=>h.1.1) (fun h=>h.1)).1
  have hCY:C≤Y:=inf_le_right.trans inf_le_left
  have hC:C≠⊥:=inf_centerIn_ne_bot (S.isPGroup'.map H.subtype) hQ
    (pCoreIn_le_sylow H S) ((map_subtype_le _).trans (le_normalizer_twoCore H))
  let : Nontrivial C:=(nontrivial_iff_ne_bot _).mpr hC
  have hp:IsPGroup 2 C:=(S.isPGroup'.map H.subtype).to_le hCY
  have hd:2∣Nat.card C:=hp.card_eq_or_dvd.resolve_left (by
    have :=Finite.one_lt_card (α:=C)
    omega)
  obtain ⟨t,ht⟩:=exists_prime_orderOf_dvd_card' (G:=C) 2 hd
  exact ⟨t,(Subgroup.orderOf_coe t).trans ht,t.property.1,t.property.2⟩

/-- Full source 2.5.11(2), with the actual involution constructed internally. -/
theorem MathieuSourceSetup.exists_central_core_involution_centralizer
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧
      t∈centerIn ((S:Subgroup H).map H.subtype) ∧
      H≤centralizer ({t}:Set G) ∧
      centralizer ({t}:Set G)∈gammaZero (Chapter1.He G) M ∧
      (∃P:Sylow 2 (centralizer ({t}:Set G)),
        (P:Subgroup (centralizer ({t}:Set G))).map (centralizer ({t}:Set G)).subtype=
          (S:Subgroup H).map H.subtype) ∧
      (H∈gammaStar (Chapter1.He G) M→centralizer ({t}:Set G)∈gammaStar (Chapter1.He G) M) ∧
      ¬IsConj t z := by
  obtain ⟨t,ht,hC,hZ⟩:=MathieuSourceSetup.exists_central_core_involution c
  exact ⟨t,ht,hC,hZ,MathieuSourceSetup.central_core_involution_centralizer c hgen t ht hC hZ⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
