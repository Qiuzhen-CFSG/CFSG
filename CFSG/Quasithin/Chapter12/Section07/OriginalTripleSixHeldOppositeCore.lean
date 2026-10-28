module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeParabolic
import Theory.Representation.HexacodeAction.AffinePlaneCentralizer
import Theory.GroupTheory.CentricRadicalCoreComparison
import Theory.Representation.NormalPSubgroupKernel
import Theory.Representation.BinaryInternalFixedSpaceCodimension.Irreducible

/-!
# The full opposite-plane centralizer and normalizer two-core

The full affine model makes W self-centralizing in the original Sylow.
Characteristic two and transfer then give C_G(W)=W. Irreducibility of the
actual normalizer action makes its entire two-core centralize W, so that
the original W is also O₂(N_G(W)). No affine recognition of this new
normalizer is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem opposite_plane_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWT : W≤(T : Subgroup G)) (hTW : (T : Subgroup G)≤normalizer (W : Set G))
    (hW : Nat.card W=64) (hI : Nat.card (U⊓W : Subgroup G)=16) :
    centralizer (W : Set G)=W := by
  let M := normalizer (K : Set G)
  let V := Multiplicative hexacode
  let A := V ⋊[hexAffineAction] HexAutomorphisms
  obtain ⟨_,_,_,_,E,hU,_,_⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  have hTM : (T : Subgroup G)≤M := D.sylow_normalizes_component
  have hUM : U≤M := D.le_component.trans K.le_normalizer
  have hWM : W≤M := hWT.trans hTM
  let W₀ := (W.subgroupOf M).map E.toMonoidHom
  let ι : V→*A := SemidirectProduct.inl
  have hUmap : (U.subgroupOf M).map E.toMonoidHom=ι.range := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨tripleSixPointCoordinates D a (⟨u,hu⟩:U),(hU ⟨u,hu⟩).symm⟩
    · rintro x ⟨v,rfl⟩
      let u := (tripleSixPointCoordinates D a).symm v
      refine ⟨inclusion hUM u,u.property,?_⟩
      change E (inclusion hUM u)=ι v
      rw [hU]
      exact congrArg ι ((tripleSixPointCoordinates D a).apply_symm_apply v)
  have hI₀ : Nat.card (W₀⊓ι.range : Subgroup A)=16 := by
    rw [←hUmap,←Subgroup.map_inf _ _ _ E.injective,card_map_of_injective E.injective]
    change Nat.card ((W⊓U).subgroupOf M)=16
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hWM)).toEquiv,inf_comm]
    exact hI
  let : IsElementaryAbelian 2 (W.subgroupOf M) := IsElementaryAbelian.subgroupOf hWM
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map _
  have hW₀ : Nat.card W₀=64 := by
    rw [card_map_of_injective E.injective,Nat.card_congr (subgroupOfEquivOfLe hWM).toEquiv]
    exact hW
  have hC₀ := Hexacode.affine_elementary_plane_centralizer W₀ hW₀ hI₀
  have hCT : (T : Subgroup G)⊓centralizer (W : Set G)≤W := by
    intro x hx
    let m : M := ⟨x,hTM hx.1⟩
    have hm : E m∈centralizer (W₀ : Set A) := by
      rintro _ ⟨w,hw,rfl⟩
      exact (map_mul E _ _).symm.trans
        ((congrArg E (Subtype.ext (hx.2 w.val hw))).trans (map_mul E _ _))
    rw [hC₀] at hm
    have hmW : m∈W.subgroupOf M := (mem_map_iff_mem (f := E.toMonoidHom) E.injective).mp hm
    exact hmW
  let I := normalizer (W : Set G)
  let N := W.subgroupOf I
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hWne : W≠⊥ := by intro he; rw [he,card_bot] at hW; omega
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
    (show IsTwoLocal I from ⟨W,hWne,IsElementaryAbelian.isPGroup 2 W,rfl⟩) hTW
  have hodd : pPrimeCore 2 I=⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (Chapter1.mem_He_iff.mp hHe)
  have hcent : (T.subtype hTW : Subgroup I)⊓centralizer (N : Set I)≤N := by
    intro x hx
    apply hCT
    refine ⟨hx.1,?_⟩
    intro w hw
    exact congrArg Subtype.val (hx.2 (⟨w,W.le_normalizer hw⟩:I) hw)
  have hCI : centralizer (N : Set I)≤N := by
    have hh := AlperinGoldschmidt.normal_p_centralizer_le (T.subtype hTW) N hcent
    change centralizer (N : Set I)≤pPrimeCore 2 I⊔N at hh
    rwa [hodd,bot_sup_eq] at hh
  apply le_antisymm
  · intro x hx
    exact hCI (show (⟨x,Subgroup.centralizer_le_normalizer _ hx⟩:I)∈centralizer (N : Set I) from
      fun w hw => Subtype.ext (hx w.val hw))
  · intro x hx w hw
    exact congrArg Subtype.val (mul_comm (⟨w,hw⟩:W) ⟨x,hx⟩)

theorem original_tripleSix_escaping_opposite_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (π : T→*DihedralGroup 4) [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128) :
    let P := π.ker.map (T : Subgroup G).subtype
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ U⊔W=R ∧
      U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      W≤R ∧ R≤(T : Subgroup G) ∧ Nat.card R=256 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓normalizer (W : Set G) ∧
      centralizer (W : Set G)=W ∧ (normalizer (W : Set G)).pCoreIn 2=W ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P := by
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨k,hk,S,W,_,hWR,hRT,hRc,hWe,hWc,_,hgen,hint,hZc,hTN,
    _,_,_,_,_,_,_,hLW,_,hirr,hIc,hZW,hneq⟩ :=
    original_tripleSix_escaping_opposite_parabolic h structural D a t ht heven hout π hP
  let := hWe
  let Bk := B.map (MulAut.conj k).toMonoidHom
  let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
  let I := normalizer (W : Set G)
  have hTW : (T : Subgroup G)≤I := hTN.trans inf_le_right
  have hCW := opposite_plane_centralizer h structural D a t ht heven hout W
    (hWR.trans hRT) hTW hWc (by rwa [hint])
  have hWne : W≠⊥ := by intro he; rw [he,card_bot] at hWc; omega
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let : ρ.IsIrreducible := (BinaryInternalFixedSpaceCodimension.irreducible_of_subgroup_minimal
    W I W.le_normalizer le_rfl hWne (fun J hJW hIJ => hirr J hJW ((sup_le hLW hTW).trans hIJ))).1
  have hpk : pCore 2 I≤ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hcore : I.pCoreIn 2=W := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      rw [←hCW]
      intro w hw
      have he := DFunLike.congr_fun (show ρ y=1 from hpk hy) (Additive.ofMul (⟨w,hw⟩:W))
      have hh := congrArg (fun v : Additive W => (v.toMul:G)) he
      change y.val*w*y.val⁻¹=w at hh
      calc w*y.val = (y.val*w*y.val⁻¹)*y.val := congrArg (fun x : G => x*y.val) hh.symm
           _ = y.val*w := by group
    · exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W) W.le_normalizer le_rfl
  exact ⟨k,hk,S,W,hWe,hWc,hgen,hint,hZc,hWR,hRT,hRc,hTN,hCW,hcore,hIc,hZW,hneq⟩

end CFSG.Quasithin.Chapter12.Section07
