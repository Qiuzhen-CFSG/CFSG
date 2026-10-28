module
public import Stellmacher.SectionTen.TenOneDisplacementNormalization
public import Theory.GroupTheory.ElementaryEightPlaneFullRestriction

/-!
# The selected displacement has a full middle-center plane stabilizer

For the source-(13) selected actor in the first neighbor module, the enlarged
displacement L=[Vend,t]∨Zmiddle is elementary of order eight and its actual
conjugation image under Gmiddle has order twenty-four. The image preserves
the middle-center plane. The selected first-line containment, quotient
rank-two displacement, and source-(13) normalization remain explicit inputs.

Center splitting identifies L with [Vend,t]∨Zend, giving order eight inside
elementary Vend. On the middle-center plane, the restriction kernel in
Gmiddle is exactly Qmiddle: the three distinct neighbor-center lines detect
the cubic local action. Thus restriction has image order six. Its kernel
inside the action on L is nontrivial, since otherwise Qmiddle centralizes L
and its involutions lie in Ω₁Z(Qmiddle)=Zmiddle, contradicting their orders.
The generic elementary-eight full-restriction theorem gives image order24.

This supplies the full plane stabilizer for the extraspecial-order27
exclusion between (13) and (14) of Stellmacher (10.1), Journal of Algebra
190 (1997), printed p.63 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_displacement_plane_image
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (actor : G) (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hselected : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4)
    (hnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer
      ((⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ middle : Subgroup G) : Set G)) :
    let L := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔ ZAt ctx.Γ middle
    let f : GAt ctx.Γ middle →* MulAut L :=
      L.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
    IsElementaryAbelian 2 L ∧ Nat.card L = 8 ∧ Nat.card f.range = 24 ∧
      ∀ j ∈ f.range, ((ZAt ctx.Γ middle).subgroupOf L).map j.toMonoidHom =
        (ZAt ctx.Γ middle).subgroupOf L := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ middle
  let Q := QAt Γ middle
  let V := VAt Γ cp.a'
  let Z := ZAt Γ middle
  let D := ⁅V, Subgroup.zpowers actor⁆
  let L := D ⊔ Z
  let U := GeneratedNeighborhoodV Γ middle
  let f : P →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  let W := Z.subgroupOf L
  obtain ⟨horbit, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 1 < cp.length := by rw [ctx.critical_length]; decide
  have hb2 : 2 < cp.length := by rw [ctx.critical_length]; decide
  have hopen := sectionTenOpeningData ctx middle hpath
  obtain ⟨hjoin, hcenters⟩ := nine_seven_center_join ctx.toAmbientSectionNineContext middle horbit
  have hlines := nine_seven_center_lines_of_center_join ctx.sectionSeven Γ middle
    hopen.quotient_model hopen.center_card hjoin hcenters
  have hZcard : Nat.card Z = 4 := hopen.center_card
  have hZL : Z ≤ L := le_sup_right
  have hZV : Z ≤ V := nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal)
  have hVU : V ≤ U := le_sSup ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hterminal, rfl⟩
  have hfirstU : VAt Γ cp.firstStep ≤ U :=
    le_sSup ⟨_, (mem_neighborhood_iff_adjacent Γ).mpr hfirst, rfl⟩
  have hDV : D ≤ V := by
    have hDU : D ≤ DerivedAmbient U := by
      rw [show DerivedAmbient U = ⁅U,U⁆ from Subgroup.map_subtype_commutator U]
      exact Subgroup.commutator_mono hVU ((Subgroup.zpowers_le.mpr hactor).trans hfirstU)
    exact hDU.trans ((ten_one_generated_derived_le_intersection ctx middle hpath).trans inf_le_right)
  have hLV : L ≤ V := sup_le hDV hZV
  have hLQ : L ≤ Q := hLV.trans (hVU.trans
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb2 middle))
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hVelem : IsElementaryAbelian 2 V := by
    obtain ⟨mover, hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    change IsElementaryAbelian 2 (VAt Γ cp.a')
    rw [← hmove, VAt, v_act]
    exact IsElementaryAbelian.map _
  let _ := hVelem
  let _ : IsElementaryAbelian 2 L := by
    let _ : IsElementaryAbelian 2 (L.subgroupOf V) := by
      refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) x
    rw [← Subgroup.map_subgroupOf_eq_of_le hLV]
    exact IsElementaryAbelian.map_subtype
  have hLsplit : L = D ⊔ ZAt Γ cp.a' := by
    change D ⊔ Z = D ⊔ ZAt Γ cp.a'
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [show Z = ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a' from hopen.center_direct_product.1]
      exact sup_le (hselected.trans le_sup_left) le_sup_right
    · exact sup_le le_sup_left ((show ZAt Γ cp.a' ≤ Z from by
        rw [show Z = ZAt Γ cp.firstStep ⊔ ZAt Γ cp.a' from hopen.center_direct_product.1]
        exact le_sup_right).trans le_sup_right)
  have hLcard : Nat.card L = 8 := by
    rw [hLsplit]
    change Nat.card (D ⊔ ZAt Γ cp.a' : Subgroup G) = 4 * Nat.card (ZAt Γ cp.a') at hindex
    rw [(hlines.1 cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)).1] at hindex
    exact hindex
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z Γ middle
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt middle ≤ Γ.vertexStabilizer middle
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hformula (g : P) (x : L) : (f g x : G) = (g:G)*(x:G)*(g:G)⁻¹ := rfl
  have hstable (j : MulAut L) (hj : j∈f.range) (x : L) : x∈W ↔ j x∈W := by
    obtain ⟨g, rfl⟩ := hj
    change (x:G)∈Z ↔ (f g x:G)∈Z
    rw [hformula]
    exact Subgroup.mem_normalizer_iff.mp (hPZ g.property) x
  have hmap (j : MulAut L) (hj : j∈f.range) : W.map j.toMonoidHom = W := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (hstable j hj x).mp hx
    · intro x hx
      refine ⟨j.symm x, ?_, j.apply_symm_apply x⟩
      apply (hstable j hj _).mpr
      simpa using hx
  let restriction : f.range →* MulAut W := {
    toFun := fun j => (j.val.subgroupMap W).trans (MulEquiv.subgroupCongr (hmap j j.property))
    map_one' := by ext x; rfl
    map_mul' := by intro j k; ext x; rfl }
  have hrestriction (j : f.range) (x : W) :
      (restriction j x : L) = (j:MulAut L) x := rfl
  let r : P →* MulAut W := restriction.comp f.rangeRestrict
  have hQfix (g : G) (hg : g∈Q) (z : G) (hz : z∈Z) : g*z*g⁻¹=z := by
    have hzomega : z ∈ omegaOneCenter Q := hopen.center_omega ▸ hz
    exact mul_inv_eq_iff_eq_mul.mpr (((mem_omegaOneCenterAmbient_iff Q z).mp hzomega).2.2 g hg)
  have hrkernel : r.ker = Q.subgroupOf P := by
    ext g
    change r g = 1 ↔ (g:G)∈Q
    constructor
    · intro hg
      have hfix (z : G) (hz : z∈Z) : (g:G)*z*(g:G)⁻¹=z := by
        let x : W := ⟨⟨z,hZL hz⟩,hz⟩
        have hh := congrArg (fun k : MulAut W => ((k x:L):G)) hg
        exact hh
      have hvertices : ∀ neighbor, Γ.adjacent middle neighbor →
          Γ.act (g:G)⁻¹ neighbor=neighbor := by
        intro neighbor hn
        have hnN := (mem_neighborhood_iff_adjacent Γ).mpr hn
        have hgfix : Γ.act (g:G)⁻¹ middle=middle :=
          (Set.ext_iff.mp (Γ.stabilizer_def middle) _).mp (P.inv_mem g.property)
        have hmove := adjacent_act Γ (g:G)⁻¹ hn
        rw [hgfix] at hmove
        have hmoveN := (mem_neighborhood_iff_adjacent Γ).mpr hmove
        have hsubgroup : ZAt Γ (Γ.act (g:G)⁻¹ neighbor)=ZAt Γ neighbor := by
          rw [ZAt,z_act,inv_inv]
          apply le_antisymm
          · rintro x ⟨y,hy,rfl⟩
            change (g:G)*y*(g:G)⁻¹∈ZAt Γ neighbor
            rw [hfix y ((hcenters neighbor hnN).2 hy)]
            exact hy
          · intro x hx
            refine ⟨x,hx,?_⟩
            exact hfix x ((hcenters neighbor hnN).2 hx)
        by_contra hne
        have hd := hlines.2.2 _ _ hmoveN hnN hne
        rw [hsubgroup] at hd
        exact (hcenters neighbor hnN).1 (disjoint_self.mp hd)
      have hmem := ((cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven middle
        hopen.quotient_model).kernel g⁻¹).mpr hvertices
      exact Q.inv_mem_iff.mp hmem
    · intro hg
      ext x
      change (g:G)*(x.val:G)*(g:G)⁻¹=(x.val:G)
      exact hQfix g hg x x.property
  have hrange : Nat.card restriction.range = 6 := by
    have heq : r.range = restriction.range := by
      change (restriction.comp f.rangeRestrict).range = restriction.range
      rw [MonoidHom.range_comp,
        f.rangeRestrict.range_eq_top_of_surjective f.rangeRestrict_surjective,← MonoidHom.range_eq_map]
    obtain ⟨projection, hsurj, hkernel⟩ := hopen.quotient_model
    have hindexR := Subgroup.index_ker r
    have hindexP := Subgroup.index_ker projection
    rw [hrkernel] at hindexR
    rw [hkernel,projection.range_eq_top_of_surjective hsurj,Subgroup.card_top,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
        (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hindexP
    rw [← heq]
    exact hindexR.symm.trans hindexP
  have hker : restriction.ker ≠ ⊥ := by
    intro hk
    have hLZ : L ≤ Z := by
      intro x hx
      rw [show Z=omegaOneCenter Q from hopen.center_omega]
      apply (mem_omegaOneCenterAmbient_iff Q x).mpr
      refine ⟨hLQ hx,elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=L) x hx,?_⟩
      intro g hg
      let gP : P := ⟨g,hQP hg⟩
      have hr : gP∈r.ker := hrkernel ▸ hg
      have hm : f.rangeRestrict gP∈restriction.ker := hr
      rw [hk,Subgroup.mem_bot] at hm
      have hf : f gP=1 := congrArg Subtype.val hm
      have hh := congrArg (fun j : MulAut L => (j ⟨x,hx⟩:G)) hf
      change g*x*g⁻¹=x at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hbound := Subgroup.card_le_of_le hLZ
    rw [hLcard,hZcard] at hbound
    omega
  have hWcard : Nat.card W=4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv).trans hZcard
  exact ⟨inferInstance,hLcard,elementaryEight_plane_card_twentyfour_of_full_restriction
    hLcard W hWcard f.range restriction hrestriction hrange hker,hmap⟩

end Stellmacher.SectionTen
