module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairMarkedAction
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.UnfaithfulRecognition

/-! The original Held pair generates the whole normalizer, whose original
full-kernel quotient is the native PSL(3,2). -/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]

private theorem local_full_kernel_transport (P Q Y : Subgroup G) (hQY : Q≤Y)
    (f : Y→*Equiv.Perm (Fin 8)) (hf : f.ker=P.subgroupOf Y)
    (q : Q→*Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hk : q.ker=P.subgroupOf Q) :
    ∃ q' : Q.subgroupOf Y→*Equiv.Perm (Fin 4), Function.Surjective q' ∧
      q'.ker=(f.comp (Q.subgroupOf Y).subtype).ker := by
  let e := subgroupOfEquivOfLe hQY
  let q' := q.comp e.toMonoidHom
  refine ⟨q',hq.comp e.surjective,?_⟩
  ext x
  change q (e x)=1 ↔ f x.val=1
  rw [←q.mem_ker,hk,←f.mem_ker,hf]
  rfl

variable [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_pair_recognition
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ ∃ hTY : (T : Subgroup G)≤Y, Nat.card P=128 ∧ ∃ hEx : IsExtraspecial 2 P, letI := hEx
      
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
            Q₀≠Q ∧ Q₀⊓Q=(T : Subgroup G) ∧ Q₀.pCoreIn 2≠Q.pCoreIn 2 ∧
            let J := Q₀⊔Q
            J≤Y ∧ ChapterF.IsGoldschmidtTriple (Q₀.subgroupOf J) (Q.subgroupOf J) ∧
              (Q₀.subgroupOf J).pCoreIn 2≠(Q.subgroupOf J).pCoreIn 2 ∧ J.pCoreIn 2=P ∧
              Q₀.pCoreIn 2=P⊔U ∧ Q.pCoreIn 2=P⊔W ∧
              Nat.card ((W.subgroupOf T).map π)=4 ∧
              (U.subgroupOf T).map π≠(W.subgroupOf T).map π ∧
              ∃ e : (ExtraspecialSquare.form P).IsometryEquiv
                (ClassicalOrthogonal.formD 3 (ZMod 2)),
                ∃ f : Y→*Equiv.Perm (Fin 8), f.ker=P.subgroupOf Y ∧
                  (∀ (y : Y) (v : P⧸center P),
                    (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val
                      (e (Additive.ofMul v))=
                        e (Additive.ofMul (quotientAut (center P) (P.normalizerMonoidHom y) v))) ∧
                  (∀ y : Y, y.val∈U ∨ y.val∈W →
                    ∀ v, ClassicalOrthogonal.formD 3 (ZMod 2)
                      ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v-v)=0) ∧
                  ∃ d : DihedralGroup 4→*Equiv.Perm (Fin 8), Function.Injective d ∧
                    (∀ t : T, d (π t)=f (inclusion hTY t)) ∧
                    (∀ x : DihedralGroup 4, x≠1 → ∀ i, d x i≠i) ∧
                    ∃ c : Equiv.Perm (Fin 8),
                      ((T : Subgroup G).subgroupOf Y).map
                        ((MulAut.conj c).toMonoidHom.comp f)=
                          Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.twoGroup ∧
                      Q₀⊔Q=Y ∧ Nonempty ((Y⧸P.subgroupOf Y)≃*PSL(3,ZMod 2)) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark⟩ :=
    original_tripleSix_escaping_pair_marked_action h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
  let Q₁ := normalizer (W : Set G)⊓centralizer ({z} : Set G)
  let := hEx
  let := hWe
  let f' := (MulAut.conj c).toMonoidHom.comp f
  have hk' : f'.ker=P.subgroupOf Y :=
    (MonoidHom.ker_comp_of_injective f (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans hfk
  have hTQ₀ : (T : Subgroup G)≤Q₀ := hint.symm ▸ inf_le_left
  have hTQ₁ : (T : Subgroup G)≤Q₁ := hint.symm ▸ inf_le_right
  obtain ⟨q₀',hq₀',hk₀'⟩ := local_full_kernel_transport P Q₀ Y hMY f' hk' q₀ hq₀ hq₀ker
  obtain ⟨q₁',hq₁',hk₁'⟩ := local_full_kernel_transport P Q₁ Y hQY f' hk' q hq hqker
  have hne' : Q₀.subgroupOf Y≠Q₁.subgroupOf Y := by
    intro he
    have hm := congrArg (Subgroup.map Y.subtype) he
    rw [map_subgroupOf_eq_of_le hMY,map_subgroupOf_eq_of_le hQY] at hm
    exact hne hm
  have hmark' : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y).map f'=
      Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.twoGroup := by
    rw [Sylow.coe_subtype]
    exact hmark
  have hkerT : f'.ker≤((T.subtype hTY : Sylow 2 Y) : Subgroup Y) := by
    rw [hk',Sylow.coe_subtype]
    exact fun _ hx => hPT hx
  have hSA : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y)≤Q₀.subgroupOf Y := by
    rw [Sylow.coe_subtype]
    exact fun _ hx => hTQ₀ hx
  have hSB : ((T.subtype hTY : Sylow 2 Y) : Subgroup Y)≤Q₁.subgroupOf Y := by
    rw [Sylow.coe_subtype]
    exact fun _ hx => hTQ₁ hx
  obtain ⟨hgen',⟨E⟩⟩ := Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.unfaithful_representation_pair_recognition
    f' (T.subtype hTY) hmark' hkerT (Q₀.subgroupOf Y) (Q₁.subgroupOf Y)
    hSA hSB q₀' hq₀' hk₀' q₁' hq₁' hk₁' hne'
  have hwhole : Q₀⊔Q₁=Y := by
    have hm := congrArg (Subgroup.map Y.subtype) hgen'
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hMY,map_subgroupOf_eq_of_le hQY,
      ←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm
  have hrecognition : Nonempty ((Y⧸P.subgroupOf Y)≃*PSL(3,ZMod 2)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hk'.symm).trans E⟩
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition⟩

end CFSG.Quasithin.Chapter12.Section07
