module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeAffineModel
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelCharacteristic
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# The full opposite point centralizer preserves the original P

The actual full action constructs an affine embedding. The image of the
original Sylow group is a native Sylow group, so the same central involution
is native 2A. The proved uniqueness of the extraspecial kernel then applies
to the image of the original P. Pullback preserves that P and its marking;
there is no replacement subgroup or ambient Held recognition premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem kernel_centralizer_from_full_action
    (T : Sylow 2 G) (hTc : Nat.card T=1024)
    (W P : Subgroup G) [IsElementaryAbelian 2 W] [IsExtraspecial 2 P]
    (hPT : P≤(T : Subgroup G)) (hTI : (T : Subgroup G)≤normalizer (W : Set G))
    (hPc : Nat.card P=128) (z : G) (hz : orderOf z=2)
    (hZP : centerIn P=zpowers z) (hZT : centerIn (T : Subgroup G)=zpowers z)
    (hker : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      (actionHom ρ).ker=W.subgroupOf I)
    (b : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      ActionEquiv (imageRepresentation ρ) Hexacode.action) :
    normalizer (W : Set G)⊓centralizer ({z} : Set G)≤normalizer (P : Set G) := by
  obtain ⟨E,_,_⟩ := opposite_affine_of_full_action W hker b
  let I := normalizer (W : Set G)
  let H := Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer
    Sporadic.Mathieu.M24LocalGeometry.standardSextet
  let eI : I≃*H := (E.trans sextetAffineEquiv).trans
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.sextetEquiv.symm
  let f : I→*Sporadic.Mathieu.M24 := H.subtype.comp eI.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp eI.injective
  let S₀ := ((T : Subgroup G).subgroupOf I).map f
  have hSc : Nat.card S₀=1024 := by
    rw [card_map_of_injective hf,Nat.card_congr (subgroupOfEquivOfLe hTI).toEquiv,hTc]
  let S : Sylow 2 Sporadic.Mathieu.M24 := Sylow.ofCard S₀ (by
    rw [hSc,Sporadic.Mathieu.m24_order]; decide +kernel)
  have hzZT : z∈centerIn (T : Subgroup G) := hZT.symm ▸ mem_zpowers z
  have hzT : z∈(T : Subgroup G) := hzZT.1
  let zI : I := ⟨z,hTI hzT⟩
  have hzf : IsSylowCentralInvolution (f zI) := by
    refine ⟨?_,S,mem_map_of_mem f hzT,?_⟩
    · exact (orderOf_injective f hf zI).trans ((Subgroup.orderOf_coe zI).symm.trans hz)
    · rintro y ⟨x,hx,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      rw [←map_mul,←map_mul]
      apply congrArg f
      apply Subtype.ext
      exact hzZT.2 x.val hx
  let A := P.subgroupOf I
  have hPI : P≤I := hPT.trans hTI
  let Q := A.map f
  let eP : P≃*Q := (subgroupOfEquivOfLe hPI).symm.trans (A.equivMapOfInjective f hf)
  let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv eP inferInstance
  have hQc : Nat.card Q=128 := (Nat.card_congr eP.symm.toEquiv).trans hPc
  have hZA : (center A).map A.subtype=zpowers zI := by
    apply map_injective I.subtype_injective
    rw [map_embeddedCenter A I.subtype I.subtype_injective,
      show A.map I.subtype=P from map_subgroupOf_eq_of_le hPI,
      ←centerIn_eq_map_center,hZP,MonoidHom.map_zpowers]
    rfl
  have hZQ : (center Q).map Q.subtype=zpowers (f zI) := by
    rw [show Q=A.map f from rfl,←map_embeddedCenter A f hf,hZA,MonoidHom.map_zpowers]
  have hn := Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.centralizer_le_normalizer_of_conjugate_extraspecial_marking
    Q hQc (f zI) (Sporadic.Mathieu.M24ChapterHStabilizers.sylowCentral_class2A hzf) hZQ
  apply le_normalizer_iff.mpr
  intro x hx p hp
  let m : I := ⟨x,hx.1⟩
  have hfc : f m∈centralizer ({f zI} : Set Sporadic.Mathieu.M24) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (show m*zI=zI*m from
      Subtype.ext (mem_centralizer_singleton_iff.mp hx.2))
  let pI : I := ⟨p,hPI hp⟩
  have hpf : f pI∈Q := mem_map_of_mem _ hp
  have hcon := (hn hfc (f pI)).mp hpf
  obtain ⟨q,hq,he⟩ := hcon
  have he' : q=m*pI*m⁻¹ := hf (by simpa only [map_mul,map_inv] using he)
  have heG : q.val=x*p*x⁻¹ := congrArg Subtype.val he'
  have hqP : q.val∈P := hq
  rwa [heG] at hqP

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual opposite normalizer's full z-centralizer preserves the same
original dihedral quotient kernel P. -/
theorem original_tripleSix_escaping_opposite_kernel_centralizer
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
          I⊓centralizer ({z} : Set G)≤Y := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    _,_,_,_,_,_,_,_,_,_,_,_,_,_,_,b,_⟩ :=
    original_tripleSix_escaping_opposite_full_actor h structural D a t ht heven hout
  let := hWe
  let := hEx
  have hTc : Nat.card T=1024 :=
    (original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout).1
  have hn := kernel_centralizer_from_full_action T hTc W
    (π.ker.map (T : Subgroup G).subtype) hPT (hTN.trans inf_le_right) hPc z hz hZP hZT hker b
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hn⟩

end CFSG.Quasithin.Chapter12.Section07
