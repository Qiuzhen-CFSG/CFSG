module
public import Stellmacher.SectionTen.TenOneSmallCommutatorActor
public import Stellmacher.SectionNine.NineNextCenterResidualCommutator
public import Stellmacher.SectionNine.NineResidualOddCoreEquality
public import Stellmacher.TwoResidualSylowSupplement
public import Stellmacher.SectionFiveToSeven.NeighborModuleNormalClosure
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# Full terminal residual support in the large case of (10.1)

In the actual Section Ten path, suppose no first-module actor outside the
terminal core induces a quotient transvection. The terminal module is its
commutator with the terminal residual. Consequently the odd core of the
literal terminal quotient action has full commutator support on V/Z.
Neither source (13), a residual model, nor a module cardinality is assumed.

Put N=[V,E]. The next-center residual theorem places the terminal center
inside N. The actual edge Sylow fixes the middle center modulo that line
and supplements E. Hence the middle center has central image in the
terminal stabilizer modulo N. Its normal closure is V, so [V,P] lies in N.
The selected nontransvection actor puts the first center in [V,P]; the two
endpoint centers generate the middle center, and normal closure now gives
V=N. The exact quotient commutator-image formula and residual/odd-core
image equality give the second theorem without changing the supplied
normality instance, elementary quotient instance, action, or kernel.

Source: Stellmacher (10.1), printed p.63, the passage from (1.3) to (14).
The full-support transfer explains why (1.3)'s support cardinality is the
cardinality of the whole terminal quotient in the subsequent case analysis.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionEight
open scoped IsMulCommutative
universe u

public theorem ten_one_large_terminal_residual_full
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    : ⁅VAt ctx.Γ ctx.criticalPath.a', EAt ctx.Γ ctx.criticalPath.a'⁆ =
        VAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let E := EAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let seed := ZAt Γ middle
  let N := ⁅V,E⁆
  have hshort : 1 < cp.length := by
    have := ctx.critical_length
    change 1 < ctx.criticalPath.length
    omega
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hZN : Z ≤ N := nine_next_center_le_residual_commutator
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  have htwo : Nat.card Z = 2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩).1
  have hseed : seed = ZAt Γ cp.firstStep ⊔ Z :=
    (sectionTenOpeningData ctx middle hpath).center_direct_product.1
  have hZseed : Z ≤ seed := by rw [hseed]; exact le_sup_right
  have hseedCard : Nat.card seed = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hVclosure : V = (Subgroup.normalClosure (seed.subgroupOf P : Set P)).map P.subtype :=
    neighbor_module_eq_normalClosure_center ctx.sectionSeven Γ middle cp.a' hterminal
  have hVP : V ≤ P := hVclosure ▸ Subgroup.map_subtype_le _
  have hseedV : seed ≤ V := by
    change ZAt Γ middle ≤ VAt Γ cp.a'
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨middle,(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal),rfl⟩
  have hseedP : seed ≤ P := hseedV.trans hVP
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.a' ≤ P
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hPE : P ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp (by
      change ((Γ.twoResidualAt cp.a').subgroupOf P).Normal
      rw [Γ.twoResidualAt_def]
      exact twoResidualIn_normal P)
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPV)
  have hNP : N ≤ P := hNV.trans hVP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_commutator_of_le_normalizers' hPV hPE
  let _ : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  let edge := P ⊓ GAt Γ middle
  let edgeSylow : Sylow 2 edge := default
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) edgeSylow
  obtain ⟨sylow,hsylow⟩ := hdata.2.1.1.2.1
  let S := (sylow : Subgroup P).map P.subtype
  have hSMiddle : S ≤ GAt Γ middle := by
    change (sylow : Subgroup P).map P.subtype ≤ GAt Γ middle
    rw [hsylow]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hindex : Z.relIndex seed = 2 := by
    have hcount := (Z.subgroupOf seed).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZseed).toEquiv,htwo,hseedCard] at hcount
    change Z.relIndex seed * 2 = 4 at hcount
    omega
  have hScomm : ⁅seed,S⁆ ≤ N := (commutator_le_of_normalizing_index_two seed Z S hindex
    (hSMiddle.trans (stabilizer_le_normalizer_z Γ middle))
    (hSP.trans (stabilizer_le_normalizer_z Γ cp.a'))).trans hZN
  have hnative : E.subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    have hn : E.subgroupOf P = twoResidualSubgroup P := by
      change (Γ.twoResidualAt cp.a').subgroupOf P = _
      rw [Γ.twoResidualAt_def]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [hn,SectionThree.twoResidualSubgroup_eq_hktPResidual',
      SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  have hgen : E.subgroupOf P ⊔ (sylow : Subgroup P) = ⊤ := by
    rw [hnative]
    exact twoResidualAmbient_top_sup_sylow sylow
  let q := QuotientGroup.mk' (N.subgroupOf P)
  have hEcomm : ⁅seed.subgroupOf P,E.subgroupOf P⁆ ≤ N.subgroupOf P := by
    intro x hx
    exact (Subgroup.commutator_mono hseedV le_rfl)
      (show (x : G) ∈ ⁅seed,E⁆ from by
        have hh := Subgroup.mem_map_of_mem P.subtype hx
        rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hseedP,
          Subgroup.map_subgroupOf_eq_of_le hEP] at hh
        exact hh)
  have hScommNative : ⁅seed.subgroupOf P,(sylow : Subgroup P)⁆ ≤ N.subgroupOf P := by
    intro x hx
    apply hScomm
    have hh := Subgroup.mem_map_of_mem P.subtype hx
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hseedP] at hh
    exact hh
  have hseedCentral : (seed.subgroupOf P).map q ≤ Subgroup.center (P ⧸ N.subgroupOf P) := by
    have hEzero : ⁅(seed.subgroupOf P).map q,(E.subgroupOf P).map q⁆ = ⊥ := by
      rw [← Subgroup.map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      exact hEcomm
    have hSzero : ⁅(seed.subgroupOf P).map q,(sylow : Subgroup P).map q⁆ = ⊥ := by
      rw [← Subgroup.map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      exact hScommNative
    apply Subgroup.centralizer_eq_top_iff_subset.mp
    apply top_unique
    have hgenMap : (E.subgroupOf P).map q ⊔ (sylow : Subgroup P).map q = ⊤ := by
      rw [← Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    rw [← hgenMap]
    exact sup_le
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEzero))
      (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSzero))
  have hVnative : V.subgroupOf P = Subgroup.normalClosure (seed.subgroupOf P : Set P) := by
    rw [hVclosure]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hVcentral : (V.subgroupOf P).map q ≤ Subgroup.center (P ⧸ N.subgroupOf P) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [hVnative]
    exact Subgroup.normalClosure_le_normal (Subgroup.map_le_iff_le_comap.mp hseedCentral)
  have hVPcomm : ⁅V,P⁆ ≤ N := by
    have hkill : ⁅V.subgroupOf P,(⊤ : Subgroup P)⁆ ≤ N.subgroupOf P := by
      have hz : (⁅V.subgroupOf P,(⊤ : Subgroup P)⁆).map q = ⊥ := by
        rw [Subgroup.map_commutator,
          Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
        exact Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hVcentral
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
    have hm := Subgroup.map_mono (f := P.subtype) hkill
    rw [Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hVP,
      Subgroup.map_subgroupOf_eq_of_le hNP,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hm
    exact hm
  obtain ⟨actor,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  have hselected := (hcases.resolve_left (hno actor hactor hout)).2
  have hactorP : actor ∈ P := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2 hactor
  have hfirstN : ZAt Γ cp.firstStep ≤ N := hselected.trans
    ((Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactorP)).trans hVPcomm)
  have hseedN : seed ≤ N := by rw [hseed]; exact sup_le hfirstN hZN
  have hVN : V ≤ N := by
    rw [hVclosure]
    exact (Subgroup.map_mono (show Subgroup.normalClosure (seed.subgroupOf P : Set P) ≤
      N.subgroupOf P from Subgroup.normalClosure_le_normal (fun x hx => hseedN hx))).trans_eq
        (Subgroup.map_subgroupOf_eq_of_le hNP)
  exact le_antisymm hNV hVN

public theorem ten_one_large_terminal_oddCore_full_support
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [_hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) :
    commutatorAction (SectionOne.oddCore action.range)
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) = ⊤ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let E := EAt Γ cp.a'
  let W := V ⧸ Z.subgroupOf V
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.a' ≤ P
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hfull : ⁅V,E⁆ = V := ten_one_large_terminal_residual_full ctx middle hpath hno
  have himage := Subgroup.quotient_conjugation_commutatorAction_eq_image P V Z E
    (stabilizer_le_normalizer_v Γ cp.a') hEP hN action hformula
  rw [hfull,Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at himage
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hcore : pCore 2 P ≤ action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  have hresimage := nine_local_residual_image_eq_oddCore
    ctx.toLocalContext.toSectionNineLocalContext cp.a' middle (Γ.adjacent_symm hterminal)
    action.rangeRestrict action.rangeRestrict_surjective hcore
  change (E.subgroupOf P).map action.rangeRestrict = SectionOne.oddCore action.range at hresimage
  have hresmap : (SectionOne.oddCore action.range).map action.range.subtype =
      (E.subgroupOf P).map action := by
    rw [← hresimage,Subgroup.map_map]
    rfl
  rw [← commutatorAction_map_actor_subtype action.range (SectionOne.oddCore action.range),hresmap]
  exact himage

end Stellmacher.SectionTen
