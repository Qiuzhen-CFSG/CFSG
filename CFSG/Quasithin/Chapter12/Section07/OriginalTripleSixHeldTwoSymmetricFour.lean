module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeSymmetricFour

/-!
# Both original point centralizers have the same marked extraspecial kernel

The first affine normalizer supplies its entire central-involution centralizer,
whose order is 3072. Its native embedding identifies the prescribed P, so its
S4 quotient and the proved opposite S4 quotient retain one common original
pi, P and z. No replacement of either kernel or ambient recognition is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem first_symmetricFour_from_affine_model
    (T : Sylow 2 G) (M U P : Subgroup G) [IsExtraspecial 2 P]
    (hTM : (T : Subgroup G)≤M) (hUM : U≤M) (hPT : P≤(T : Subgroup G))
    (hPc : Nat.card P=128)
    (c : U≃*Multiplicative hexacode)
    (E : M≃*Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms)
    (hEU : ∀ u : U, E (inclusion hUM u)=SemidirectProduct.inl (c u))
    (z : G) (hz : orderOf z=2) (hzU : z∈U)
    (hZP : centerIn P=zpowers z) (hZT : centerIn (T : Subgroup G)=zpowers z) :
    let Q := M⊓centralizer ({z} : Set G)
    ∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q := by
  let Q := M⊓centralizer ({z} : Set G)
  let zU : U := ⟨z,hzU⟩
  let v := (c zU).toAdd
  let f : M→*HexAutomorphisms := SemidirectProduct.rightHom.comp E.toMonoidHom
  have hfs : Function.Surjective f := SemidirectProduct.rightHom_surjective.comp E.surjective
  have hk : f.ker=U.subgroupOf M := by
    ext x
    change (E x).right=1 ↔ (x:G)∈U
    constructor
    · intro hx
      obtain ⟨u,hu⟩ := c.surjective (E x).left
      have he : E (inclusion hUM u)=E x := by
        rw [hEU,hu]
        apply SemidirectProduct.ext <;> simp [hx]
      have hev := congrArg Subtype.val (E.injective he)
      exact hev ▸ u.property
    · intro hx
      let u : U := ⟨x.val,hx⟩
      have he := congrArg SemidirectProduct.right (hEU u)
      exact he
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
  have hUQ : U≤Q := by
    refine le_inf hUM ?_
    intro u hu
    apply (fixed_iff (inclusion hUM ⟨u,hu⟩)).mp
    have he : f (inclusion hUM ⟨u,hu⟩)=1 := by
      change (inclusion hUM ⟨u,hu⟩ : M)∈f.ker
      rw [hk]
      exact hu
    rw [he,map_one]
    rfl
  have hUc : Nat.card U=64 := (Nat.card_congr c.toEquiv).trans
    ((Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode≃hexacode)).trans hexacode_card)
  have hQc : Nat.card Q=3072 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (Q.subgroupOf M) f
    rw [hk,inf_eq_right.mpr (subgroupOf_mono M hUQ),himage,
      Hexacode.fullWeightFourVectorStabilizer_card _ hv4,
      Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv,hUc,
      Nat.card_congr (subgroupOfEquivOfLe (show Q≤M from inf_le_left)).toEquiv] at hh
    exact hh.symm
  have hzP : z∈centerIn P := hZP.symm ▸ mem_zpowers z
  have hPQ : P≤Q := le_inf (hPT.trans hTM) (fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzP.2 x hx))
  let N := Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer
    Sporadic.Mathieu.M24LocalGeometry.standardSextet
  let eM : M≃*N := (E.trans sextetAffineEquiv).trans
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.sextetEquiv.symm
  let j : Q→*Sporadic.Mathieu.M24 := N.subtype.comp
    (eM.toMonoidHom.comp (inclusion (show Q≤M from inf_le_left)))
  have hj : Function.Injective j := N.subtype_injective.comp
    (eM.injective.comp (inclusion_injective inf_le_left))
  let P' := P.subgroupOf Q
  let eP : P'≃*P := subgroupOfEquivOfLe hPQ
  let : IsExtraspecial 2 P' := IsExtraspecial.of_mulEquiv eP.symm inferInstance
  have hP' : Nat.card P'=128 := (Nat.card_congr eP.toEquiv).trans hPc
  let zQ : Q := ⟨z,hPQ hzP.1⟩
  have hzQ : orderOf zQ=2 := (Subgroup.orderOf_coe zQ).symm.trans hz
  have hzQc : zQ∈center Q := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2)
  have hZP' : (center P').map P'.subtype=zpowers zQ := by
    apply map_injective Q.subtype_injective
    rw [map_embeddedCenter P' Q.subtype Q.subtype_injective,
      show P'.map Q.subtype=P from map_subgroupOf_eq_of_le hPQ,
      ←centerIn_eq_map_center,hZP,MonoidHom.map_zpowers]
    rfl
  exact Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.embedded_symmetricFour_quotient
    j hj hQc P' hP' zQ hzQ hzQc hZP'

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- Both original point centralizers map onto S4 with the same prescribed
extraspecial subgroup P as their full kernel. -/
theorem original_tripleSix_escaping_two_symmetricFour
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
            ∃ q₀ : Q₀→*Equiv.Perm (Fin 4), Function.Surjective q₀ ∧ q₀.ker=P.subgroupOf Q₀ := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,q,hq,hqker⟩ :=
    original_tripleSix_escaping_opposite_symmetricFour h structural D a t ht heven hout
  let := hEx
  let M := normalizer (K : Set G)
  have hTM : (T : Subgroup G)≤M := by
    rw [show M=normalizer (K : Set G) from rfl,
      (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2]
    exact le_sup_right
  obtain ⟨_,_,_,_,E,hEU,_,_⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  have hfirst := first_symmetricFour_from_affine_model T M U
    (π.ker.map (T : Subgroup G).subtype) hTM (D.le_component.trans K.le_normalizer)
    hPT hPc (tripleSixPointCoordinates D a) E hEU z hz hzU hZP hZT
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,⟨q,hq,hqker⟩,hfirst⟩

end CFSG.Quasithin.Chapter12.Section07
