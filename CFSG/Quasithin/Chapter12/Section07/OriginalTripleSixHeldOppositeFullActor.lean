module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeCubicActor
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFullActor

/-!
# The full opposite-normalizer action in the original Held configuration

The actual six-space row sieve and cubic recognition construct a full
hexacode action equivalence for N_G(W)/W. Its Sylow order is exactly sixteen,
so the image is the full actor, not merely its even subgroup. The same
original pi, extraspecial P, opposite W, z, Y and action kernel are retained.
The next comparison concerns the marked z-centralizer and the same P;
no ambient Held identification or such comparison is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_full_actor
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
            (F.map J.subtype).map b.groupEquiv.toMonoidHom=Atlas.Codes.hexSign.ker := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,hq,⟨c⟩,⟨ec⟩,⟨eq⟩⟩ :=
    original_tripleSix_escaping_opposite_cubic_actor h structural D a t ht heven hout
  let := hWe
  let I := normalizer (W : Set G)
  let ρ := BinaryInternalFixedSpaceCodimension.representation W I le_rfl
  let τ := imageRepresentation ρ
  let J := offenderSubgroup τ
  let F := generalizedFitting J
  have hc : Nat.card (center F)=3 := by rw [Nat.card_congr ec.toEquiv]; simp
  obtain ⟨b,hb⟩ := ChapterB.SourceInduction.SylowSixteenSixSpace.full_actor_of_cubic_source
    τ hf hi hdim hq c hc eq default (hsyl default)
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hker,hWP,hZW,hneq,
    hdim,hsyl,hf,hi,heC,hCJ,hCfix,hAe,hAc,hAd,hline,hq,⟨c⟩,⟨ec⟩,⟨eq⟩,b,hb⟩

end CFSG.Quasithin.Chapter12.Section07
