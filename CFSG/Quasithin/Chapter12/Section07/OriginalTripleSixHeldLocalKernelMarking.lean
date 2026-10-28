module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldNormal128
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.SylowDihedralKernelMarking
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelExtraspecial
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The original local centralizer preserves the full marked kernel

The original full affine normalizer supplies the actual native Sylow
embedding. Its native two-central quotient map transports to the original
T, retaining its entire kernel. The subgroup P is exactly the image of
that kernel in G, and its plus extraspecial structure and self-centralization
are transported through this same map.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_local_kernel_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤normalizer (P : Set G) ∧
        Nat.card P=128 ∧ IsExtraspecial 2 P ∧
        (T : Subgroup G)⊓centralizer (P : Set G)≤P ∧
        Nonempty (P≃*DihedralCentralProductThree.Model) ∧
        normalizer (K : Set G)⊓centralizer (centerIn P : Set G)≤normalizer (P : Set G) := by
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
  obtain ⟨ψ,hψ,hC,⟨eQ⟩,hmark⟩ :=
    Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.exists_sylow_dihedral_kernel_marked S
  let π := ψ.comp eT.toMonoidHom
  let P := π.ker.map (T : Subgroup G).subtype
  let eker : π.ker≃*ψ.ker := {
    toFun := fun x => ⟨eT x.val,x.property⟩
    invFun := fun y => ⟨eT.symm y.val,by
      change ψ (eT (eT.symm y.val))=1
      rw [eT.apply_symm_apply]
      exact y.property⟩
    left_inv := fun x => Subtype.ext (eT.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (eT.apply_symm_apply y.val)
    map_mul' := fun x y => Subtype.ext (eT.map_mul x.val y.val) }
  let eP := (π.ker.equivMapOfInjective (T : Subgroup G).subtype
    (T : Subgroup G).subtype_injective).symm.trans (eker.trans eQ)
  have hPT : P≤(T : Subgroup G) := by rintro x ⟨y,_,rfl⟩; exact y.property
  have hTP : (T : Subgroup G)≤normalizer (P : Set G) := by
    intro x hx
    exact π.ker.le_normalizer_map (T : Subgroup G).subtype
      (mem_map_of_mem _ (show (⟨x,hx⟩:T)∈normalizer (π.ker : Set T) by
        rw [normalizer_eq_top]; exact mem_top _))
  obtain ⟨eD⟩ := Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel_equiv_dihedral_three
  refine ⟨π,hψ.comp eT.surjective,hPT,hTP,?_,?_,?_,⟨eP.trans eD⟩,?_⟩
  · exact (Nat.card_congr eP.toEquiv).trans Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel_card
  · exact IsExtraspecial.of_mulEquiv eP.symm
      Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.kernel_extraspecial
  · intro x hx
    let xT : T := ⟨x,hx.1⟩
    have hxC : eT xT∈centralizer (ψ.ker : Set S) := by
      intro y hy
      let p := eker.symm (⟨y,hy⟩:ψ.ker)
      have hh : p.val*xT=xT*p.val := Subtype.ext
        (hx.2 p.val.val (mem_map_of_mem _ p.property))
      have he := congrArg eT hh
      have hp : eT p.val=y := congrArg Subtype.val (eker.apply_symm_apply ⟨y,hy⟩)
      simpa only [map_mul,hp] using he
    exact mem_map_of_mem _ (show xT∈π.ker from hC hxC)

  · let Q := ψ.ker.map (S : Subgroup Sporadic.Mathieu.M24).subtype
    let A := P.subgroupOf M
    have hPM : P≤M := hPT.trans hTM
    have hfT (x : T) : f (⟨x.val,hTM x.property⟩:M)=(eT x : Sporadic.Mathieu.M24) := rfl
    have hfP : A.map f=Q := by
      apply le_antisymm
      · rintro x ⟨p,hp,rfl⟩
        obtain ⟨v,hv,hvp⟩ := hp
        have hev : ψ (eT v)=1 := hv
        refine ⟨eT v,hev,?_⟩
        change (eT v : Sporadic.Mathieu.M24)=f p
        rw [←hfT]
        exact congrArg f (Subtype.ext hvp)
      · rintro x ⟨s,hs,rfl⟩
        let v := eT.symm s
        have hv : v∈π.ker := by
          change ψ (eT (eT.symm s))=1
          rw [eT.apply_symm_apply]
          exact hs
        refine ⟨⟨v.val,hTM v.property⟩,mem_map_of_mem _ hv,?_⟩
        rw [hfT]
        exact congrArg Subtype.val (eT.apply_symm_apply s)
    have hZP : ((center A).map A.subtype).map M.subtype=centerIn P := by
      rw [map_embeddedCenter A M.subtype M.subtype_injective,
        show A.map M.subtype=P from map_subgroupOf_eq_of_le hPM,centerIn_eq_map_center]
    apply le_normalizer_iff.mpr
    intro x hx p hp
    let m : M := ⟨x,hx.1⟩
    have hfc : f m∈centralizer ((center Q).map Q.subtype : Set Sporadic.Mathieu.M24) := by
      rw [←hfP,←map_embeddedCenter A f hf]
      rintro y ⟨u,hu,rfl⟩
      have huG : (u:G)∈centerIn P := hZP ▸ mem_map_of_mem _ hu
      have hh : u*m=m*u := Subtype.ext (hx.2 u.val huG)
      exact (map_mul f _ _).symm.trans ((congrArg f hh).trans (map_mul f _ _))
    have hfn : f m∈normalizer (Q : Set Sporadic.Mathieu.M24) := hmark hfc
    have hpM : p∈M := hPM hp
    have hpf : f (⟨p,hpM⟩:M)∈Q := hfP ▸ mem_map_of_mem _ hp
    have hcon := (hfn _).mp hpf
    rw [←hfP] at hcon
    obtain ⟨w,hw,he⟩ := hcon
    have he' : w=m*(⟨p,hpM⟩:M)*m⁻¹ := hf (by simpa only [map_mul,map_inv] using he)
    have heG : w.val=x*p*x⁻¹ := congrArg Subtype.val he'
    have hwP : w.val∈P := hw
    rw [heG] at hwP
    exact hwP

end CFSG.Quasithin.Chapter12.Section07
