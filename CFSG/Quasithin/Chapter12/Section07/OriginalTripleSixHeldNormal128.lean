module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFullAffine
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.SylowCore128

/-!
# An actual normal order-128 subgroup of the original escaping Sylow

The proved full affine normalizer embeds in the native sextet stabilizer.
Its original Sylow has order 1024 and is therefore an ambient native
Mathieu Sylow. Transporting the literal two-central kernel produces a
normal self-centralizing subgroup of the original T of order 128 and
center order two. The whole kernel is retained by an isomorphism.
Neither extraspecial plus type nor the original overgroup Y is assumed
or concluded at this stage.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_normal128
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ P : Subgroup G, P≤(T : Subgroup G) ∧
      (T : Subgroup G)≤normalizer (P : Set G) ∧ Nat.card P=128 ∧
      Nat.card (center P)=2 ∧ (T : Subgroup G)⊓centralizer (P : Set G)≤P ∧
      Nonempty (P≃*Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel) := by
  obtain ⟨hTc,_,_,_,E,_,_,_⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  let M := normalizer (K : Set G)
  let H := Sporadic.Mathieu.M24LocalGeometry.sextetStabilizer
    Sporadic.Mathieu.M24LocalGeometry.standardSextet
  let eM : M≃*H := (E.trans sextetAffineEquiv).trans
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.sextetEquiv.symm
  let f : M→*Sporadic.Mathieu.M24 := H.subtype.comp eM.toMonoidHom
  have hf : Function.Injective f := H.subtype_injective.comp eM.injective
  have hTM : (T : Subgroup G)≤M := by
    rw [show M=normalizer (K : Set G) from rfl,
      (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2]
    exact le_sup_right
  let S₀ := ((T : Subgroup G).subgroupOf M).map f
  have hSc : Nat.card S₀=1024 := by
    rw [card_map_of_injective hf,Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv,hTc]
  let S : Sylow 2 Sporadic.Mathieu.M24 := Sylow.ofCard S₀ (by
    rw [hSc,Sporadic.Mathieu.m24_order]; decide +kernel)
  let eT : T≃*S := (subgroupOfEquivOfLe hTM).symm.trans
    (((T : Subgroup G).subgroupOf M).equivMapOfInjective f hf)
  obtain ⟨Q,hQS,hSQ,hQc,hQZ,hQC,⟨eQ⟩⟩ :=
    Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.exists_normal_selfCentralizing_core128 S
  let : (Q.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hSQ
  let P₀ := (Q.subgroupOf S).comap eT.toMonoidHom
  let : P₀.Normal := inferInstance
  let eP : P₀≃*Q := {
    toFun := fun x => ⟨(eT x.val).val,x.property⟩
    invFun := fun y => ⟨eT.symm ⟨y.val,hQS y.property⟩,by
      change (eT (eT.symm ⟨y.val,hQS y.property⟩)).val∈Q
      rw [eT.apply_symm_apply]
      exact y.property⟩
    left_inv := fun x => Subtype.ext (eT.symm_apply_apply x.val)
    right_inv := fun y => by
      apply Subtype.ext
      change (eT (eT.symm ⟨y.val,hQS y.property⟩)).val=y.val
      rw [eT.apply_symm_apply]
    map_mul' := fun x y => by
      apply Subtype.ext
      change (eT (x.val*y.val)).val=(eT x.val).val*(eT y.val).val
      rw [map_mul]
      rfl }
  let P := P₀.map (T : Subgroup G).subtype
  let e₀ := P₀.equivMapOfInjective (T : Subgroup G).subtype (T : Subgroup G).subtype_injective
  have hPT : P≤(T : Subgroup G) := by rintro x ⟨y,_,rfl⟩; exact y.property
  have hTP : (T : Subgroup G)≤normalizer (P : Set G) := by
    intro x hx
    exact P₀.le_normalizer_map (T : Subgroup G).subtype
      (mem_map_of_mem _ (show (⟨x,hx⟩:T)∈normalizer (P₀ : Set T) by
        rw [normalizer_eq_top]; exact mem_top _))
  refine ⟨P,hPT,hTP,?_,?_,?_,⟨(e₀.symm.trans eP).trans eQ⟩⟩
  · exact (Nat.card_congr (e₀.symm.trans eP).toEquiv).trans hQc
  · exact (Nat.card_congr (centerCongr (e₀.symm.trans eP)).toEquiv).trans hQZ
  · intro x hx
    let xT : T := ⟨x,hx.1⟩
    have hxC : (eT xT).val∈centralizer (Q : Set Sporadic.Mathieu.M24) := by
      intro y hy
      let p := eP.symm (⟨y,hy⟩:Q)
      have hpc : (p.val : G)∈P := mem_map_of_mem _ p.property
      have hh : p.val*xT=xT*p.val := Subtype.ext (hx.2 p.val.val hpc)
      have he := congrArg (fun v : T => (eT v).val) hh
      have hp : (eT p.val).val=y := congrArg Subtype.val (eP.apply_symm_apply ⟨y,hy⟩)
      change (eT (p.val*xT)).val=(eT (xT*p.val)).val at he
      simp only [map_mul,Subgroup.coe_mul] at he
      simpa only [hp] using he
    have hxP : xT∈P₀ := hQC ⟨(eT xT).property,hxC⟩
    exact mem_map_of_mem _ hxP

end CFSG.Quasithin.Chapter12.Section07
