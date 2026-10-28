module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.A6QuotientSource
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FixedIndexExclusion

/-!
# The proper fixed-A₆ overcomponent quotient

A proper fixed A₆ component makes the involution act nontrivially on its
quasisimple overcomponent. Its centerless fixed component survives the
central quotient. Restriction to a normal component and quotient passage
both decrease the Sylow fixed index. The full known-simple quotient census
and the index-four bound therefore force the quotient to be A₈.

Source: Aschbacher–Smith 2.4.36, printed p.549. This preserves the actual
involution action and the specified fixed component throughout.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Section05.Overcomponents
variable {G : Type*} [Group G] [Finite G]

theorem proper_fixed_component_quotient
    (E K : Subgroup G) [E.Normal] [IsQuasisimple E]
    (hE : IsSQTK KnownSimple.IsKnownSimple E)
    (z : G) (hz : orderOf z = 2)
    (hK : IsComponentIn K (centralizer ({z} : Set G)))
    (hKE : K < E) (eK : K ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 G) (hi : (centralizer ({z} : Set G)).relIndex (P : Subgroup G) ≤ 4) :
    let a := quotientAut (center E) (MulAut.conjNormal z : MulAut E)
    ∃ B : Subgroup a.fixedSubgroup, orderOf a = 2 ∧
      IsComponent a.fixedSubgroup B ∧ Nonempty (B ≃* alternatingGroup (Fin 6)) ∧
      A6FixedQuotientModels (E ⧸ center E) a ∧
      ∃ Q : Sylow 2 (E ⧸ center E), (a.fixedSubgroup.subgroupOf Q).index ≤ 4 := by
  let a : MulAut E := MulAut.conjNormal z
  let C := E ⊓ centralizer ({z} : Set G)
  have hf : a.fixedSubgroup = (centralizer ({z} : Set G)).subgroupOf E := by
    ext y
    rw [MulAut.mem_fixedSubgroup]
    change a y = y ↔ (y : G) ∈ centralizer ({z} : Set G)
    rw [Subtype.ext_iff,mem_centralizer_singleton_iff]
    change z * (y : G) * z⁻¹ = (y : G) ↔ (y : G) * z = z * y
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have ha2 : a^2 = 1 := by
    change (MulAut.conjNormal z : MulAut E)^2 = 1
    have hz2 : z^2=1 := hz ▸ pow_orderOf_eq_one z
    rw [←map_pow,hz2,map_one]
  have hane : a ≠ 1 := by
    intro he
    have hEC : E ≤ centralizer ({z} : Set G) := by
      intro y hy
      have hh : (⟨y,hy⟩ : E) ∈ a.fixedSubgroup := by rw [he,MulAut.mem_fixedSubgroup]; rfl
      rw [hf] at hh
      exact hh
    have hKi : IsComponent E (K.subgroupOf E) := (hK.restrict hKE.le hEC).2
    have htop : IsComponent E ⊤ := ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩
    exact hKE.not_ge (subgroupOf_eq_top.mp (hKi.eq_of_le htop le_top))
  have ha : orderOf a = 2 := orderOf_eq_prime ha2 hane
  let f : a.fixedSubgroup ≃* C :=
    E.normalizerFixedEquivCentralizer ⟨z,by rw [normalizer_eq_top]; exact mem_top z⟩
  have hKC : K ≤ C := le_inf hKE.le hK.1
  let B := (K.subgroupOf C).map f.symm.toMonoidHom
  have hB : IsComponent a.fixedSubgroup B :=
    (hK.restrict hKC inf_le_right).2.map_equiv f.symm
  let eB : B ≃* alternatingGroup (Fin 6) :=
    (f.symm.subgroupMap (K.subgroupOf C)).symm.trans
      ((subgroupOfEquivOfLe hKC).trans eK)
  have hZ : center B = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    apply eB.injective
    rw [map_one]
    have hh : eB v ∈ center (alternatingGroup (Fin 6)) := (Subgroup.centerCongr eB ⟨v,hv⟩).property
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6))] at hh
    exact hh
  let b := quotientAut (center E) a
  let q := QuotientGroup.mk' (center E)
  have hcompat : ∀ x, q (a x) = b (q x) :=
    fun x => (quotientAut_apply_mk (center E) a x).symm
  have hb : orderOf b = 2 :=
    (orderOf_injective (quotientAut (center E)) MulAut.quotient_center_injective a).trans ha
  obtain ⟨hD,⟨eD⟩⟩ := MulAut.fixedSubgroupMap_component_of_center_eq_bot a b q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hcompat B hB hZ
  let D := B.map (MulAut.fixedSubgroupMap a b q hcompat)
  let e : D ≃* alternatingGroup (Fin 6) := eD.symm.trans eB
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : Group.IsPerfect (E ⧸ center E) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center E))
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model hE
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  refine ⟨D,hb,hD,⟨e⟩,a6_fixed_quotient_models hm b hb D hD e,?_⟩
  obtain ⟨U,hU⟩ := P.exists_subgroupOf_eq_of_normal E
  let Q : Sylow 2 (E ⧸ center E) := U.mapSurjective (QuotientGroup.mk'_surjective (center E))
  have hiU : a.fixedSubgroup.relIndex (U : Subgroup E) ≤ 4 := by
    rw [hU,hf]
    change ((centralizer ({z} : Set G)).comap E.subtype).relIndex ((P : Subgroup G).subgroupOf E) ≤ 4
    rw [relIndex_comap,subgroupOf_map_subtype]
    exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hi
  have hfix : a.fixedSubgroup ≤ b.fixedSubgroup.comap q := by
    intro x hx
    change q x ∈ b.fixedSubgroup
    rw [MulAut.mem_fixedSubgroup,←hcompat,(MulAut.mem_fixedSubgroup _ _).mp hx]
  refine ⟨Q,?_⟩
  change b.fixedSubgroup.relIndex (U.mapSurjective (QuotientGroup.mk'_surjective (center E)) : Subgroup _) ≤ 4
  rw [Sylow.coe_mapSurjective,←relIndex_comap]
  exact (relIndex_le_of_le_left hfix index_ne_zero_of_finite).trans hiU

theorem proper_fixed_component_quotient_alternating_eight
    (E K : Subgroup G) [E.Normal] [IsQuasisimple E]
    (hE : IsSQTK KnownSimple.IsKnownSimple E)
    (z : G) (hz : orderOf z = 2)
    (hK : IsComponentIn K (centralizer ({z} : Set G)))
    (hKE : K < E) (eK : K ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 G) (hi : (centralizer ({z} : Set G)).relIndex (P : Subgroup G) ≤ 4) :
    Nonempty ((E ⧸ center E) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨B,ha,_,⟨eB⟩,hm,Q,hiQ⟩ := proper_fixed_component_quotient E K hE z hz hK hKE eK P hi
  exact alternating_eight_of_fixed_index _ ha hm B eB Q hiQ

end CFSG.Quasithin.Chapter2.DoubleA3
