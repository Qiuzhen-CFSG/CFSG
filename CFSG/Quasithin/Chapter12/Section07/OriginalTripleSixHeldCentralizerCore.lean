module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairRecognition
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NonsolvableTwoLocal

/-! The original involution centralizer core is properly above Z(P) and
contained in the same P. Its equality with P is equivalent to C_G(z)=Y. -/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_normalized (C : Subgroup G) : C≤normalizer (C.pCoreIn 2 : Set G) := by
  simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using (pCore 2 C).le_normalizer_map C.subtype

private theorem centralizer_core_bounds
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (P : Subgroup G) (z : G) (hz : orderOf z=2) (hPc : Nat.card P=128)
    (hPT : P≤(T : Subgroup G))
    (hTY : (T : Subgroup G)≤normalizer (P : Set G))
    (hYC : normalizer (P : Set G)≤centralizer ({z} : Set G))
    (hZ : centerIn P=zpowers z)
    (hcore : (normalizer (P : Set G)).pCoreIn 2=P) :
    let C := centralizer ({z} : Set G)
    let Q := C.pCoreIn 2
    centerIn P<Q ∧ Q≤P ∧ C≤normalizer (Q : Set G) ∧
      C⊓centralizer (Q : Set G)≤Q ∧ (Q=P ↔ C=normalizer (P : Set G)) := by
  let C := centralizer ({z} : Set G)
  let Q := C.pCoreIn 2
  have hTC : (T : Subgroup G)≤C := hTY.trans hYC
  have hCN : C≤normalizer (Q : Set G) := core_normalized C
  have hQT : Q≤(T : Subgroup G) := by
    have hh := pCoreIn_le_sylow C (T.subtype hTC)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] using hh
  have hQP : Q≤P := by
    rw [←hcore]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C) (hQT.trans hTY) (hYC.trans hCN)
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T hE (isTwoLocal_involution_centralizer hz) hTC
  have hself : C⊓centralizer (Q : Set G)≤Q := by
    intro x hx
    have hh : (⟨x,hx.1⟩:C)∈centralizer (pCore 2 C : Set C) := by
      intro y hy
      exact Subtype.ext (hx.2 y.val (mem_map_of_mem C.subtype hy))
    exact mem_map_of_mem C.subtype ((Chapter1.mem_He_iff.mp hHe) hh)
  have hZQ : zpowers z≤Q := by
    apply le_pCoreIn_of_normalizes
    · exact IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers,pow_one] using hz)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
    · have he : centralizer (zpowers z : Set G)=C := by rw [zpowers_eq_closure,centralizer_closure]
      exact he ▸ Subgroup.centralizer_le_normalizer _
  have hne : Q≠zpowers z := by
    intro he
    have hCP : C≤zpowers z := by
      rw [he] at hself
      have hc : C≤centralizer (zpowers z : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      exact (le_inf le_rfl hc).trans hself
    have hc := card_le_of_le ((hPT.trans hTC).trans hCP)
    rw [hPc,Nat.card_zpowers,hz] at hc
    omega
  refine ⟨?_,hQP,hCN,hself,?_⟩
  · rw [hZ]
    exact lt_of_le_of_ne hZQ (Ne.symm hne)
  · constructor
    · intro he
      apply le_antisymm ?_ hYC
      change Q=P at he
      exact he ▸ hCN
    · intro he
      simpa only [Q,C,he] using hcore

variable {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_centralizer_core
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
                        C⊓centralizer (Q : Set G)≤Q ∧ (Q=P ↔ C=Y) := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition⟩ :=
    original_tripleSix_escaping_pair_recognition h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let := hEx
  let := hWe
  have hcoreY : Y.pCoreIn 2=P := by
    change _=Y at hwhole
    exact (congrArg (fun L : Subgroup G => L.pCoreIn 2) hwhole).symm.trans hJP
  have hb := centralizer_core_bounds T (h.simpleQTKE.evenCharacteristic T)
    P z hz hPc hPT hTY hYC hZP hcoreY
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree,c,hmark,hwhole,hrecognition,hcoreY,hb⟩

end CFSG.Quasithin.Chapter12.Section07
