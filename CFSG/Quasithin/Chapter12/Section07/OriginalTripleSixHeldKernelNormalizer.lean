module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCoreOverlap
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ExtraspecialCentricNormalizer
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The original marked extraspecial normalizer and its faithful action

The same dihedral kernel supplies an actual central involution of T in U.
Even characteristic at the original T removes the odd centralizer of P,
so C_G(P)=Z(P)=Z(T). Its full normalizer Y=N_G(P) centralizes that marked
involution, and its action on P/Z(P) has exactly P as kernel.
This constructs an actual overgroup and action; the two-parabolic comparison
and identification of Y/P remain separate source duties.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_kernel_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤Y ∧
        Nat.card P=128 ∧ IsExtraspecial 2 P ∧ Nat.card (U⊓P : Subgroup G)=16 ∧
        ∃ z : G, orderOf z=2 ∧ z∈U ∧
          centerIn P=zpowers z ∧ centerIn (T : Subgroup G)=zpowers z ∧
          centralizer (P : Set G)=zpowers z ∧ Y≤centralizer ({z} : Set G) ∧
          (normalQuotientAction (P.subgroupOf Y) (center (P.subgroupOf Y))).ker=
            P.subgroupOf Y ∧
          ∃ j : (Y⧸P.subgroupOf Y)→*MulAut ((P.subgroupOf Y)⧸center (P.subgroupOf Y)),
            Function.Injective j ∧
            (∀ y : Y, j (QuotientGroup.mk' (P.subgroupOf Y) y)=
              normalQuotientAction (P.subgroupOf Y) (center (P.subgroupOf Y)) y) ∧
            ∃ S : Sylow 2 (Y⧸P.subgroupOf Y), Nonempty (S≃*DihedralGroup 4) := by
  obtain ⟨π,hπ,hPT,hTP,hPc,hEx,hCT,_⟩ :=
    original_tripleSix_escaping_marked_dihedral_quotient h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let N := P.subgroupOf Y
  let : IsExtraspecial 2 P := hEx
  let eN : N≃*P := subgroupOfEquivOfLe P.le_normalizer
  let : IsExtraspecial 2 N := IsExtraspecial.of_mulEquiv eN.symm hEx
  have hPne : P≠⊥ := by
    intro he
    have hc : Nat.card P=1 := Subgroup.card_eq_one.mpr he
    have hh : (1:ℕ)=128 := hc.symm.trans hPc
    norm_num at hh
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
    (show IsTwoLocal Y from ⟨P,hPne,IsExtraspecial.isPGroup 2 P,rfl⟩) hTP
  have hodd : pPrimeCore 2 Y=⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (Chapter1.mem_He_iff.mp hHe)
  have hcent : (T.subtype hTP : Subgroup Y)⊓centralizer (N : Set Y)≤N := by
    intro x hx
    apply hCT
    refine ⟨hx.1,?_⟩
    intro p hp
    exact congrArg Subtype.val (hx.2 (⟨p,P.le_normalizer hp⟩:Y) hp)
  obtain ⟨hC,hZ,hker⟩ := extraspecial_centric_central_quotient_kernel
    (T.subtype hTP) N hodd hcent
  have hNP : N.map Y.subtype=P := map_subgroupOf_eq_of_le P.le_normalizer
  have hZN : ((center N).map N.subtype).map Y.subtype=centerIn P := by
    rw [map_embeddedCenter N Y.subtype Y.subtype_injective,hNP,centerIn_eq_map_center]
  have hCG : centralizer (P : Set G)=centerIn P := by
    apply le_antisymm
    · intro x hx
      have hxN : (⟨x,Subgroup.centralizer_le_normalizer _ hx⟩:Y)∈centralizer (N : Set Y) := by
        intro p hp
        exact Subtype.ext (hx p.val hp)
      rw [hC] at hxN
      exact hZN ▸ mem_map_of_mem Y.subtype hxN
    · exact inf_le_right
  have hZY : centerIn P≤(center Y).map Y.subtype := by
    rw [←hZN,hZ]
  have hZT : centerIn P=centerIn (T : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hPT hx.1,?_⟩
      obtain ⟨y,hy,rfl⟩ := hZY hx
      intro v hv
      exact congrArg Subtype.val (mem_center_iff.mp hy (⟨v,hTP hv⟩:Y))
    · intro x hx
      have hxP := hCT ⟨hx.1,centralizer_le hPT hx.2⟩
      exact ⟨hxP,centralizer_le hPT hx.2⟩
  let eP := π.ker.equivMapOfInjective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective
  let : IsExtraspecial 2 π.ker := IsExtraspecial.of_mulEquiv eP.symm hEx
  let := D.elementary
  let U₀ := U.subgroupOf T
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf D.le_sylow
  have hQc : Nat.card π.ker=128 := (Nat.card_congr eP.toEquiv).trans hPc
  have hUc : Nat.card U₀=64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe D.le_sylow).toEquiv]
    exact (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  obtain ⟨hI,_,hZU,_⟩ := extraspecial_dihedral_elementary_overlap π hQc U₀ hUc
  have hIc : Nat.card (U⊓P : Subgroup G)=16 := by
    have hmap : (U₀⊓π.ker : Subgroup T).map (T : Subgroup G).subtype=U⊓P := by
      rw [Subgroup.map_inf _ _ _ (T : Subgroup G).subtype_injective,
        map_subgroupOf_eq_of_le D.le_sylow]
    rw [←hmap,card_map_of_injective (T : Subgroup G).subtype_injective]
    exact hI
  have hZU' : centerIn P≤U := by
    rw [centerIn_eq_map_center,←map_embeddedCenter π.ker (T : Subgroup G).subtype
      (T : Subgroup G).subtype_injective]
    exact (map_mono hZU).trans_eq (map_subgroupOf_eq_of_le D.le_sylow)
  obtain ⟨z,hz,_⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
    (IsExtraspecial.center_order_p 2 P)
  have hzG : (z.val:G)≠1 := by intro he; exact hz (Subtype.ext (Subtype.ext he))
  have hzC : (z.val:G)∈centerIn P := by
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem _ z.property
  have hzz : centerIn P=zpowers (z.val:G) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzC)
    rw [Nat.card_zpowers]
    have ho : orderOf (z.val:G)=2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ (hZU' hzC)) hzG
    rw [ho,centerIn_eq_map_center,card_map_of_injective P.subtype_injective,
      IsExtraspecial.center_order_p 2 P]
  refine ⟨π,hπ,hPT,hTP,hPc,hEx,hIc,(z.val:G),?_,hZU' hzC,hzz,hZT.symm.trans hzz,
    hCG.trans hzz,?_,hker,?_⟩
  · exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ (hZU' hzC)) hzG
  · intro y hy
    obtain ⟨w,hw,hwz⟩ := hZY hzC
    have hc := congrArg Subtype.val (mem_center_iff.mp hw (⟨y,hy⟩:Y))
    exact mem_centralizer_singleton_iff.mpr (hwz ▸ hc)
  · let f := normalQuotientAction N (center N)
    let j : (Y⧸N)→*MulAut (N⧸center N) := QuotientGroup.lift N f hker.ge
    have hj : Function.Injective j := (QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm
    refine ⟨j,hj,fun _ => rfl,?_⟩
    let q := QuotientGroup.mk' N
    let S₀ := T.subtype hTP
    let S := S₀.mapSurjective (QuotientGroup.mk'_surjective N)
    let eT : T≃*S₀ := (subgroupOfEquivOfLe hTP).symm
    let r : T→*S := (q.subgroupMap (S₀ : Subgroup Y)).comp eT.toMonoidHom
    have hr : Function.Surjective r := (q.subgroupMap_surjective _).comp eT.surjective
    have hrker : r.ker=π.ker := by
      ext x
      change ((q.subgroupMap (S₀ : Subgroup Y)) (eT x)=1) ↔ π x=1
      rw [Subtype.ext_iff]
      change (QuotientGroup.mk (⟨x.val,hTP x.property⟩:Y) : Y⧸N)=1 ↔ π x=1
      rw [QuotientGroup.eq_one_iff]
      change x.val∈P ↔ x∈π.ker
      change x.val∈π.ker.map (T : Subgroup G).subtype ↔ x∈π.ker
      constructor
      · rintro ⟨v,hv,hvx⟩
        exact (Subtype.ext hvx : v=x) ▸ hv
      · exact fun hx => mem_map_of_mem _ hx
    exact ⟨S,⟨(QuotientGroup.quotientKerEquivOfSurjective r hr).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hrker).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ))⟩⟩

end CFSG.Quasithin.Chapter12.Section07
