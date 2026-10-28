module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCentralizerCore
public import Theory.GroupTheory.ExtraspecialSquareTransport
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-! The actual centralizer core has a proper invariant square image unless
it equals P. The full original normalizer has order21504. -/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_core_square_image
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
                            IsElementaryAbelian 2 Q)) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,
    hcoreY,hZQ,hQP,hCN,hself,hiff⟩ :=
    original_tripleSix_escaping_centralizer_core h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let C := centralizer ({z} : Set G)
  let Q := C.pCoreIn 2
  let := hEx
  let := hWe
  have hYcard : Nat.card Y=21504 := by
    obtain ⟨eq⟩ := hrecognition
    have hc : Nat.card (Y⧸P.subgroupOf Y)=168 :=
      (Nat.card_congr eq.toEquiv).trans Matrix.PSL3Two.card_PSL
    have hcp : Nat.card (P.subgroupOf Y)=128 :=
      (Nat.card_congr (subgroupOfEquivOfLe P.le_normalizer).toEquiv).trans hPc
    rw [card_eq_card_quotient_mul_card_subgroup (P.subgroupOf Y),hc,hcp]
  have himage : Q=P ∨ ∃ V : Submodule (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)),
      V≠⊥ ∧ V≠⊤ ∧ 2*Nat.card V=Nat.card Q ∧
      (∀ g∈f.range, ∀ v∈V,
        (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g).val v∈V) ∧
      ((∀ v∈V, ClassicalOrthogonal.formD 3 (ZMod 2) v=0) → IsElementaryAbelian 2 Q) := by
    by_cases he : Q=P
    · exact Or.inl he
    · exact Or.inr (ExtraspecialSquare.exists_invariant_image P Q Y hQP le_rfl
        (hYC.trans hCN) hZQ he e f hfe)
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,
    hcoreY,hZQ,hQP,hCN,hself,hiff,hYcard,himage⟩

end CFSG.Quasithin.Chapter12.Section07
