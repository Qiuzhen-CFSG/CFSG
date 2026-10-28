module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldMarkedCentralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.RectangleAlignment
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.NoncentralFour
import all CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldAmbientExclusions

/-! The original pair of elementary sixty-fours and original point four
are identified inside the actual marked centralizer using one conjugator.
All earlier witnesses are retained, including the marked action and kernel. -/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open TransvectionFive TransvectionFive.UniquenessLinear
open TransvectionFive.UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_aligned_locals
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
                      Q₀⊔Q=Y ∧ Nonempty ((Y⧸P.subgroupOf Y)≃*PSL(3,ZMod 2)) ∧
                      let C := centralizer ({z} : Set G)
                      let Q := C.pCoreIn 2
                      Y.pCoreIn 2=P ∧ centerIn P<Q ∧ Q≤P ∧
                        C≤normalizer (Q : Set G) ∧
                        C⊓centralizer (Q : Set G)≤Q ∧ (Q=P ↔ C=Y) ∧ Nat.card Y=21504 ∧
                        (Q=P ∨ ∃ V : Submodule (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)),
                          V≠⊥ ∧ V≠⊤ ∧ 2*Nat.card V=Nat.card Q ∧
                          (∀ g∈f.range, ∀ v∈V,
                            (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g).val v∈V) ∧
                          ((∀ v∈V, ClassicalOrthogonal.formD 3 (ZMod 2) v=0) →
                            IsElementaryAbelian 2 Q)) ∧ Q=P ∧ C=Y ∧
                        Theory.GroupTheory.TransvectionFive.PointCoreFusion z ∧
                        ∃ V : Submodule (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)),
                          Nat.card V=8 ∧
                          (∀ g∈f.range, ∀ v∈V,
                            (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g).val v∈V) ∧
                          (∀ v∈V, ClassicalOrthogonal.formD 3 (ZMod 2) v=0) ∧
                          (∀ g∈f.range, (∀ v∈V,
                            (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g).val v=v) → g=1) ∧
                          ∃ A : Subgroup G, ∃ hA : IsElementaryAbelian 2 A, letI := hA
                            centerIn P≤A ∧ A≤P ∧ Nat.card A=16 ∧
                            Y≤normalizer (A : Set G) ∧ Y⊓centralizer (A : Set G)≤A ∧
                            ∃ F : TransvectionFive.MarkedCentralizer z, A=F.column ∧
                              (F.fusion F.plane).ncard=45 ∧
                              (F.fusion F.threeSpace).ncard=45 ∧ F.HeldNormalizerPattern ∧
                              ∃ c : centralizer ({z} : Set G),
                                (U.map (MulAut.conj (c:G)).toMonoidHom=F.plane ∧
                                  W.map (MulAut.conj (c:G)).toMonoidHom=F.threeSpace ∧
                                  ∃ i : Fin 6, (tripleSixPoint D a t).map
                                    (MulAut.conj (c:G)).toMonoidHom=planeFour F i) ∨
                                (U.map (MulAut.conj (c:G)).toMonoidHom=F.threeSpace ∧
                                  W.map (MulAut.conj (c:G)).toMonoidHom=F.plane ∧
                                  ∃ i : Fin 6, (tripleSixPoint D a t).map
                                    (MulAut.conj (c:G)).toMonoidHom=planeFour (oppositeMarking F) i) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,
    hcoreY,hZQ,hQP,hCN,hself,hiff,hYcard,himage,hQP',hCY,hfusion,V,hVc,hVi,hVs,hVf,A,hA,hZA,hAP,hAc,hYA,hselfA,F,hAF,hp45,ht45,hpattern⟩ :=
    original_tripleSix_escaping_marked_centralizer h structural D a t ht heven hout
  let := D.elementary
  let := hWe
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
  have hUW : U≠W := by intro he; exact hneq (congrArg (fun R : Subgroup G => R⊓_) he)
  obtain ⟨r,hr⟩ := UniquenessHeld.exists_simultaneous_rectangle_alignment F T
    (hTY.trans hYC) U W (hUR.trans hRT) (hWR.trans hRT) hUc hWc hUW
  have hpoint := tripleSixPoint_properties D a t ht
  have ht1 : (t:G)≠1 := fun he => ht (Subtype.ext he)
  have hCc : Nat.card (centralizer ({z} : Set G))=21504 := by rw [hCY]; exact hYcard
  obtain ⟨_,h9,_,_,_⟩ := original_tripleSix_escaping_ambient_exclusions
    h structural D a t ht heven hout
  have hpure : ∀ v∈tripleSixPoint D a t, v≠1 → ¬IsConj z v := by
    intro v hv hv1 hzv
    obtain ⟨x,_,hx⟩ := (tripleSixScalarResidual_point_transitive D a t).2
      t hpoint.1 ht1 v hv hv1
    have htv : IsConj (t:G) v := isConj_iff.mpr ⟨x,hx⟩
    have hcards := centralizer_card_of_conjugate (hzv.trans htv.symm)
    rw [hCc] at hcards
    rw [←hcards] at h9
    norm_num at h9
  let conjHom := (MulAut.conj (r:G)).toMonoidHom
  let Vt := (tripleSixPoint D a t).map conjHom
  have hVtc : Nat.card Vt=4 :=
    (card_map_of_injective (MulAut.conj (r:G)).injective).trans hpoint.2.2.1
  have hVtpure : ∀ v∈Vt, v≠1 → ¬IsConj z v := by
    rintro _ ⟨v,hv,rfl⟩ hv1 hzv
    have hvne : v≠1 := fun he => hv1 (he ▸ conjHom.map_one)
    have hvconj : IsConj v (conjHom v) := isConj_iff.mpr ⟨(r:G),rfl⟩
    exact hpure v hv hvne (hzv.trans hvconj.symm)
  have hVtU : Vt≤U.map conjHom := map_mono hpoint.2.1
  have halign :
      (U.map conjHom=F.plane ∧ W.map conjHom=F.threeSpace ∧ ∃ i, Vt=planeFour F i) ∨
      (U.map conjHom=F.threeSpace ∧ W.map conjHom=F.plane ∧ ∃ i, Vt=planeFour (oppositeMarking F) i) := by
    rcases hr with ⟨hrU,hrW⟩ | ⟨hrU,hrW⟩
    · obtain ⟨i,hi,_⟩ := UniquenessHeld.exists_unique_planeFour_of_pure_four
        F hp45 Vt (hVtU.trans_eq hrU) hVtc hVtpure
      exact Or.inl ⟨hrU,hrW,i,hi⟩
    · have ho : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard=45 := by
        simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using ht45
      have hVo : Vt≤(oppositeMarking F).plane := by rw [oppositeMarking_plane]; exact hVtU.trans_eq hrU
      obtain ⟨i,hi,_⟩ := UniquenessHeld.exists_unique_planeFour_of_pure_four
        (oppositeMarking F) ho Vt hVo hVtc hVtpure
      exact Or.inr ⟨hrU,hrW,i,hi⟩
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,
    hcoreY,hZQ,hQP,hCN,hself,hiff,hYcard,himage,hQP',hCY,hfusion,V,hVc,hVi,hVs,hVf,A,hA,hZA,hAP,hAc,hYA,hselfA,F,hAF,hp45,ht45,hpattern,r,halign⟩

end CFSG.Quasithin.Chapter12.Section07
