module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeFullActor
public import Theory.Representation.HexacodeAction.SylowFixedVector

/-!
# The full opposite centralizer has the marked duad actor

The original central involution z is fixed by the entire retained T. Under
the proved full opposite action it is a nonzero Sylow-fixed hexacode vector,
hence has weight four. The actual image of C_{N_G(W)}(z), with its full W
kernel retained, is its entire vector stabilizer, marked as S2 times S4.
This constructs the original centralizer actor; normality of the same P
in that centralizer is a separate comparison and is not assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_point_model
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
          let Bk := B.map (MulAut.conj k).toMonoidHom
          let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
          let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
          let I := normalizer (W : Set G)
          let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
          let τ := imageRepresentation ρ
          let A := actionSubgroup ρ (P.subgroupOf I)
          let C := actionSubgroup ρ (L.subgroupOf I)
          let J := offenderSubgroup τ
          let F := generalizedFitting J
          U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ U⊔W=R ∧
          Nat.card W=64 ∧ (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
          centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
          (actionHom ρ).ker=W.subgroupOf I ∧
          Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
          (U⊓P : Subgroup G)≠W⊓P ∧
          Module.finrank (ZMod 2) (Additive W)=6 ∧
          (∀ Q : Sylow 2 (actionImage ρ), Nat.card Q=16) ∧
          Function.Injective τ ∧ τ.IsIrreducible ∧
          Nonempty (C≃*alternatingGroup (Fin 5)) ∧ C≤J ∧ fixedSpace τ C≠⊥ ∧
          IsElementaryAbelian 2 A ∧ Nat.card A=8 ∧
          Module.finrank (ZMod 2) (fixedSpace τ A)=1 ∧
          (∀ v : Additive W, v∈fixedSpace τ A ↔ (v.toMul:G)∈zpowers z) ∧
          IsQuasisimple F ∧
          Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (τ.comp J.subtype) F) ∧
          Nonempty (center F≃*Multiplicative (ZMod 3)) ∧
          Nonempty ((F ⧸ center F)≃*alternatingGroup (Fin 6)) ∧
          ∃ b : ActionEquiv τ Hexacode.action,
            (F.map J.subtype).map b.groupEquiv.toMonoidHom=Atlas.Codes.hexSign.ker ∧
            ∃ zW : W, (zW : G)=z ∧
              hammingNorm (b.linearEquiv (Additive.ofMul zW)).val=4 ∧
              ((I⊓centralizer ({z} : Set G)).subgroupOf I).map
                (b.groupEquiv.toMonoidHom.comp (actionHom ρ))=
                  Hexacode.fullVectorStabilizer (b.linearEquiv (Additive.ofMul zW)) ∧
              Nonempty (Hexacode.fullVectorStabilizer (b.linearEquiv (Additive.ofMul zW))≃*
                Theory.SpecificGroups.SymmetricSix.DuadProduct) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,hq,hc,hcenter,heq,b,hb⟩ :=
    original_tripleSix_escaping_opposite_full_actor h structural D a t ht heven hout
  let := hWe
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let f := b.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hfs : Function.Surjective f := b.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective
  have hzW : z∈W := hZW (hZP.symm ▸ mem_zpowers z)
  let zW : W := ⟨z,hzW⟩
  let v := b.linearEquiv (Additive.ofMul zW)
  have hv : v≠0 := by
    intro he
    have hh := b.linearEquiv.injective (he.trans b.linearEquiv.map_zero.symm)
    have hz1 : z=1 := congrArg (fun w : Additive W => (w.toMul:G)) hh
    rw [hz1,orderOf_one] at hz
    omega
  have fixed_iff (x : I) : Hexacode.action (f x) v=v ↔
      (x:G)∈centralizer ({z} : Set G) := by
    have ha := b.intertwines (actionHom ρ x) (Additive.ofMul zW)
    rw [imageRepresentation_actionHom] at ha
    change b.linearEquiv (ρ x (Additive.ofMul zW))=Hexacode.action (f x) v at ha
    rw [←ha]
    change b.linearEquiv (ρ x (Additive.ofMul zW))=b.linearEquiv (Additive.ofMul zW) ↔ _
    rw [b.linearEquiv.injective.eq_iff]
    constructor
    · intro he y hy
      have hyz : y=z := Set.mem_singleton_iff.mp hy
      subst y
      have hh := congrArg (fun w : Additive W => (w.toMul:G)) he
      change (x:G)*z*(x:G)⁻¹=z at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x:G)*z*(x:G)⁻¹=z
      rw [←hx z (Set.mem_singleton z),mul_inv_cancel_right]
  have hTI : (T : Subgroup G)≤I := hTN.trans inf_le_right
  let S0 := T.subtype hTI
  let S1 := S0.mapSurjective (f := f) hfs
  have hfix (g : S1) : Hexacode.action g v=v := by
    obtain ⟨x,hx,hxg⟩ := (show g.val∈(S0 : Subgroup I).map f from g.property)
    rw [←hxg]
    apply (fixed_iff x).mpr
    have hzT : z∈centerIn (T : Subgroup G) := hZT.symm ▸ mem_zpowers z
    intro y hy
    have hyz : y=z := Set.mem_singleton_iff.mp hy
    subst y
    exact (hzT.2 x.val hx).symm
  have hv4 := Hexacode.weight_four_of_sylow_fixed S1 v hv hfix
  have himage : ((I⊓centralizer ({z} : Set G)).subgroupOf I).map f=
      Hexacode.fullVectorStabilizer v := by
    apply le_antisymm
    · rintro g ⟨x,hx,rfl⟩
      exact (fixed_iff x).mpr hx.2
    · intro g hg
      obtain ⟨x,rfl⟩ := hfs g
      exact ⟨x,⟨x.property,(fixed_iff x).mp hg⟩,rfl⟩
  obtain ⟨e,_,_,_⟩ := Hexacode.fullWeightFourVectorStabilizer_model v hv4
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,hq,hc,hcenter,heq,b,hb,zW,rfl,hv4,himage,⟨e⟩⟩

end CFSG.Quasithin.Chapter12.Section07
