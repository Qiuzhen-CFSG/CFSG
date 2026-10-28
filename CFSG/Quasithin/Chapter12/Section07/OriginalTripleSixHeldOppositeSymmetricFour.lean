module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeKernelCentralizer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositePointModel
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelParabolicTransfer
import all CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeKernelCentralizer

/-!
# The original opposite point centralizer has the marked S4 quotient

Use one original point-model witness throughout. The proved same-P
centralizer comparison supplies normalization. Its actual affine embedding
and the native quotient identify the whole point centralizer modulo that
same P with S4, retaining the full kernel and original dihedral map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem opposite_symmetricFour_from_point_model
    (T : Sylow 2 G) (hTc : Nat.card T=1024)
    (W P : Subgroup G) [IsElementaryAbelian 2 W] [IsExtraspecial 2 P]
    (hPT : P≤(T : Subgroup G)) (hTI : (T : Subgroup G)≤normalizer (W : Set G))
    (hPc : Nat.card P=128) (hWc : Nat.card W=64)
    (z : G) (hz : orderOf z=2)
    (hZP : centerIn P=zpowers z) (hZT : centerIn (T : Subgroup G)=zpowers z)
    (hker : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      (actionHom ρ).ker=W.subgroupOf I)
    (b : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      ActionEquiv (imageRepresentation ρ) Hexacode.action)
    (zW : W) (hzW : (zW:G)=z)
    (hweight : hammingNorm (b.linearEquiv (Additive.ofMul zW)).val=4)
    (himage : let I := normalizer (W : Set G)
      let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
      ((I⊓centralizer ({z} : Set G)).subgroupOf I).map
        (b.groupEquiv.toMonoidHom.comp (actionHom ρ))=
          Hexacode.fullVectorStabilizer (b.linearEquiv (Additive.ofMul zW))) :
    let Q := normalizer (W : Set G)⊓centralizer ({z} : Set G)
    Q≤normalizer (P : Set G) ∧
      ∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q := by
  let I := normalizer (W : Set G)
  let Q := I⊓centralizer ({z} : Set G)
  have hn := kernel_centralizer_from_full_action T hTc W P hPT hTI hPc z hz hZP hZT hker b
  have hzP : z∈centerIn P := hZP.symm ▸ mem_zpowers z
  have hPQ : P≤Q := le_inf (hPT.trans hTI) (fun x hx =>
    mem_centralizer_singleton_iff.mpr (hzP.2 x hx))
  have hWQ : W≤Q := by
    refine le_inf W.le_normalizer ?_
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (mul_comm (⟨x,hx⟩ : W) zW)
    change x*(zW:G)=(zW:G)*x at hh
    rwa [hzW] at hh
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let f := b.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hk : f.ker=W.subgroupOf I := by
    rw [show f=b.groupEquiv.toMonoidHom.comp (actionHom ρ) from rfl,
      MonoidHom.ker_comp_of_injective _ _ b.groupEquiv.injective,hker]
  have hQc : Nat.card Q=3072 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (Q.subgroupOf I) f
    rw [hk,inf_eq_right.mpr (subgroupOf_mono I hWQ),himage,
      Hexacode.fullWeightFourVectorStabilizer_card _ hweight,
      Nat.card_congr (subgroupOfEquivOfLe W.le_normalizer).toEquiv,hWc,
      Nat.card_congr (subgroupOfEquivOfLe (show Q≤I from inf_le_left)).toEquiv] at hh
    exact hh.symm
  obtain ⟨E,_,_⟩ := opposite_affine_of_full_action W hker b
  let H := Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer
    Sporadic.Mathieu.M24LocalGeometry.standardSextet
  let eI : I≃*H := (E.trans sextetAffineEquiv).trans
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.sextetEquiv.symm
  let j : Q→*Sporadic.Mathieu.M24 := H.subtype.comp
    (eI.toMonoidHom.comp (inclusion (show Q≤I from inf_le_left)))
  have hj : Function.Injective j := H.subtype_injective.comp
    (eI.injective.comp (inclusion_injective inf_le_left))
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
  exact ⟨hn,Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.embedded_symmetricFour_quotient
    j hj hQc P' hP' zQ hzQ hzQc hZP'⟩

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- The whole original opposite point centralizer has the S4 quotient,
with the same original P as its full kernel. -/
theorem original_tripleSix_escaping_opposite_symmetricFour
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
          Q≤Y ∧ ∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    _,_,_,_,_,_,_,_,_,_,_,_,_,_,_,b,_,zW,hzW,hweight,himage,_⟩ :=
    original_tripleSix_escaping_opposite_point_model h structural D a t ht heven hout
  let := hWe
  let := hEx
  have hTc : Nat.card T=1024 :=
    (original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout).1
  have hn := opposite_symmetricFour_from_point_model T hTc W
    (π.ker.map (T : Subgroup G).subtype) hPT (hTN.trans inf_le_right) hPc hWc z hz hZP hZT hker b
      zW hzW hweight himage
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hn⟩

end CFSG.Quasithin.Chapter12.Section07
