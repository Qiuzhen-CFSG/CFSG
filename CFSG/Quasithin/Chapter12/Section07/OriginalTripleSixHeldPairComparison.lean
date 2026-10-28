module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldTwoSymmetricFour
public import Theory.Representation.HexacodeAction.AffinePointElementary

/-!
# Comparing the two original central-involution parabolics

The endpoint maps retain the same extraspecial kernel. Their common original
Sylow subgroup has index three in each endpoint; once the original elementary
planes distinguish the endpoints, their intersection is precisely that Sylow.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem endpoint_card (P Q : Subgroup G) (hPQ : P≤Q)
    (hP : Nat.card P=128) (q : Q→*Equiv.Perm (Fin 4))
    (hq : Function.Surjective q) (hker : q.ker=P.subgroupOf Q) :
    Nat.card Q=3072 := by
  have hcard := card_eq_card_quotient_mul_card_subgroup q.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv,
    hker,Nat.card_congr (subgroupOfEquivOfLe hPQ).toEquiv,hP] at hcard
  have hfour : Nat.card (Equiv.Perm (Fin 4))=24 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hfour] at hcard
  exact hcard

private theorem common_sylow_intersection (T A B : Subgroup G)
    (hTA : T≤A) (hTB : T≤B) (hT : Nat.card T=1024)
    (hA : Nat.card A=3072) (hB : Nat.card B=3072) (hne : A≠B) :
    A⊓B=T := by
  have hi : T.relIndex A=3 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) T A bot_le hTA
    rw [relIndex_bot_left,relIndex_bot_left,hT,hA] at hm
    omega
  have hm := relIndex_mul_relIndex T (A⊓B) A (le_inf hTA hTB) inf_le_left
  rw [hi] at hm
  have hp : (T.relIndex (A⊓B) * (A⊓B).relIndex A).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,he⟩ | ⟨_,he⟩
  · have hAB : A≤B := (relIndex_eq_one.mp he).trans inf_le_right
    exact (hne (eq_of_le_of_card_ge hAB (by rw [hA,hB]))).elim
  · exact le_antisymm (relIndex_eq_one.mp he) (le_inf hTA hTB)

private theorem elementary64_unique_in_affine_point_core
    (T : Sylow 2 G) (M U : Subgroup G)
    (hTM : (T : Subgroup G)≤M) (hUM : U≤M)
    (c : U≃*Multiplicative hexacode)
    (E : M≃*Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms)
    (hEU : ∀ u : U, E (inclusion hUM u)=SemidirectProduct.inl (c u))
    (z : G) (hz : orderOf z=2) (hzU : z∈U)
    (hZT : centerIn (T : Subgroup G)=zpowers z)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWC : W≤(M⊓centralizer ({z} : Set G)).pCoreIn 2)
    (hW : Nat.card W=64) : W=U := by
  have hWQ : W≤M⊓centralizer ({z} : Set G) := hWC.trans (pCoreIn_le 2 _)
  let Q := M⊓centralizer ({z} : Set G)
  let zU : U := ⟨z,hzU⟩
  let v := (c zU).toAdd
  let f : M→*HexAutomorphisms := SemidirectProduct.rightHom.comp E.toMonoidHom
  have hfs : Function.Surjective f := SemidirectProduct.rightHom_surjective.comp E.surjective
  have fixed_iff (x : M) : Hexacode.action (f x) v=v ↔
      (x:G)∈centralizer ({z} : Set G) := by
    have ha : Hexacode.action (f x) v=v ↔
        E x*SemidirectProduct.inl (c zU)=SemidirectProduct.inl (c zU)*E x := by
      rw [SemidirectProduct.ext_iff]
      simp only [SemidirectProduct.mul_left,SemidirectProduct.left_inl,
        SemidirectProduct.right_inl,map_one,MulAut.one_apply,SemidirectProduct.mul_right,
        mul_one,one_mul,and_true]
      rw [mul_comm (c zU),mul_left_cancel_iff]
      rfl
    rw [←hEU zU,←map_mul,←map_mul,E.injective.eq_iff] at ha
    rw [ha,mem_centralizer_singleton_iff]
    exact Subtype.ext_iff
  have hv : v≠0 := by
    intro he
    have hc : c zU=1 := congrArg Multiplicative.ofAdd he
    have hz1 : z=1 := congrArg Subtype.val (c.injective (hc.trans c.map_one.symm))
    rw [hz1,orderOf_one] at hz
    omega
  let S := (T.subtype hTM).mapSurjective (f := f) hfs
  have hv4 : hammingNorm v.val=4 := Hexacode.weight_four_of_sylow_fixed S v hv (by
    intro g
    obtain ⟨x,hx,hxg⟩ := (show g.val∈((T.subtype hTM : Sylow 2 M) : Subgroup M).map f from g.property)
    rw [←hxg]
    apply (fixed_iff x).mpr
    have hzT : z∈centerIn (T : Subgroup G) := hZT.symm ▸ mem_zpowers z
    exact mem_centralizer_singleton_iff.mpr (hzT.2 x.val hx))
  have himage : (Q.subgroupOf M).map f=Hexacode.fullVectorStabilizer v := by
    apply le_antisymm
    · rintro g ⟨x,hx,rfl⟩
      exact (fixed_iff x).mpr hx.2
    · intro g hg
      obtain ⟨x,rfl⟩ := hfs g
      exact ⟨x,⟨x.property,(fixed_iff x).mp hg⟩,rfl⟩
  let W' := (W.subgroupOf M).map E.toMonoidHom
  let Q' := (Q.subgroupOf M).map E.toMonoidHom
  have hWM : W≤M := hWQ.trans inf_le_left
  let : IsElementaryAbelian 2 (W.subgroupOf M) := IsElementaryAbelian.subgroupOf hWM
  let : IsElementaryAbelian 2 W' := IsElementaryAbelian.map E.toMonoidHom
  have hQ' : Q'.map SemidirectProduct.rightHom=Hexacode.fullVectorStabilizer v := by
    rw [map_map]
    exact himage
  let C := Q.pCoreIn 2
  let C' := (C.subgroupOf M).map E.toMonoidHom
  have hCN : Q≤normalizer (C : Set G) := by
    simpa only [C,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 Q).le_normalizer_map Q.subtype
  have hn' : Q'≤normalizer (C' : Set _) := by
    apply le_normalizer_iff.mpr
    rintro x ⟨x,hx,rfl⟩ w ⟨w,hw,rfl⟩
    exact ⟨x*w*x⁻¹,le_normalizer_iff.mp hCN x.val hx w.val hw,by
      simp only [map_mul,map_inv]⟩
  have he := Hexacode.affine_point_elementary64_in_normal_two v hv4 Q' C' W' hQ'
    ((isPGroup_pCoreIn 2 Q).comap_subtype.map E.toMonoidHom)
    (map_mono (subgroupOf_mono M hWC))
    (map_mono (subgroupOf_mono M (pCoreIn_le 2 Q))) hn'
    (by rw [card_map_of_injective E.injective,
      Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv,hW])
  have hU' : (U.subgroupOf M).map E.toMonoidHom=SemidirectProduct.inl.range := by
    apply le_antisymm
    · rintro _ ⟨u,hu,rfl⟩
      exact ⟨c ⟨u.val,hu⟩,(hEU ⟨u.val,hu⟩).symm⟩
    · rintro _ ⟨v,rfl⟩
      obtain ⟨u,rfl⟩ := c.surjective v
      exact ⟨inclusion hUM u,u.property,hEU u⟩
  have hh : W.subgroupOf M=U.subgroupOf M := map_injective E.injective (he.trans hU'.symm)
  have hmap := congrArg (Subgroup.map M.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hWM,map_subgroupOf_eq_of_le hUM] using hmap

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- The two original central-involution parabolics are distinct and meet
exactly in the original Sylow subgroup. Their actual two-cores are distinct;
the same full extraspecial kernel is retained throughout. -/
theorem original_tripleSix_escaping_pair_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤Y ∧ Nat.card P=128 ∧ IsExtraspecial 2 P ∧
      Nonempty (P≃*DihedralCentralProductThree.Model) ∧
      Nat.card (U⊓P : Subgroup G)=16 ∧ Nat.card ((U.subgroupOf T).map π)=4 ∧
      ∃ z : G, orderOf z=2 ∧ z∈U ∧
        centerIn P=zpowers z ∧ centerIn (T : Subgroup G)=zpowers z ∧
        centralizer (P : Set G)=zpowers z ∧ Y≤centralizer ({z} : Set G) ∧
        normalizer (K : Set G)⊓centralizer ({z} : Set G)≤Y ∧
        let H := centralizer ({(t:G)} : Set G)
        let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
        let B := conjugateSpanBy Lt H
        ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
          ∃ hWe : IsElementaryAbelian 2 W, letI := hWe
          let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
          let I := normalizer (W : Set G)
          U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ U⊔W=R ∧
          Nat.card W=64 ∧ (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
          centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
          Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
          (U⊓P : Subgroup G)≠W⊓P ∧
          let Q := I⊓centralizer ({z} : Set G)
          Q≤Y ∧
            (∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q) ∧
            let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
            (∃ q₀ : Q₀→*Equiv.Perm (Fin 4), Function.Surjective q₀ ∧ q₀.ker=P.subgroupOf Q₀) ∧
            Q₀≠Q ∧ Q₀⊓Q=(T : Subgroup G) ∧ Q₀.pCoreIn 2≠Q.pCoreIn 2 := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩⟩ :=
    original_tripleSix_escaping_two_symmetricFour h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let M := normalizer (K : Set G)
  let Q₀ := M⊓centralizer ({z} : Set G)
  let Q₁ := normalizer (W : Set G)⊓centralizer ({z} : Set G)
  let := hWe
  obtain ⟨hTc,_,_,_,E,hEU,_,_⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  have hTM : (T : Subgroup G)≤M := by
    rw [show M=normalizer (K : Set G) from rfl,
      (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2]
    exact le_sup_right
  have hTC : (T : Subgroup G)≤centralizer ({z} : Set G) := by
    intro x hx
    have hzT : z∈centerIn (T : Subgroup G) := hZT.symm ▸ mem_zpowers z
    exact mem_centralizer_singleton_iff.mpr (hzT.2 x hx)
  have hTQ₀ : (T : Subgroup G)≤Q₀ := le_inf hTM hTC
  have hTQ₁ : (T : Subgroup G)≤Q₁ := le_inf (hTN.trans inf_le_right) hTC
  have hWQ₁ : W≤Q₁ := (hWR.trans hRT).trans hTQ₁
  have hWcore : W≤Q₁.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 W) hWQ₁ inf_le_left
  have hcorene : Q₀.pCoreIn 2≠Q₁.pCoreIn 2 := by
    intro he
    have hWC : W≤Q₀.pCoreIn 2 := hWcore.trans_eq he.symm
    have hWU := elementary64_unique_in_affine_point_core T M U hTM
      (D.le_component.trans K.le_normalizer) (tripleSixPointCoordinates D a)
      E hEU z hz hzU hZT W hWC hWc
    exact hneq (hWU ▸ rfl)
  have hne : Q₀≠Q₁ := fun he => hcorene (congrArg (pCoreIn 2) he)
  have hQ₀c : Nat.card Q₀=3072 := endpoint_card P Q₀ (hPT.trans hTQ₀) hPc q₀ hq₀ hq₀ker
  have hQ₁c : Nat.card Q₁=3072 := endpoint_card P Q₁ (hPT.trans hTQ₁) hPc q hq hqker
  have hint : Q₀⊓Q₁=(T : Subgroup G) := common_sylow_intersection
    (T : Subgroup G) Q₀ Q₁ hTQ₀ hTQ₁ hTc hQ₀c hQ₁c hne
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene⟩

end CFSG.Quasithin.Chapter12.Section07
