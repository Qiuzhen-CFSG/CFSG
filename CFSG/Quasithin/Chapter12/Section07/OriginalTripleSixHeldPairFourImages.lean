module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairSquareAction

/-!
# The original two four-groups in the same dihedral quotient

The images of the elementary64 planes are the normal fours of the two
symmetric-four quotients. Their full preimages are the literal local cores,
so the already-proved unequal cores give distinct four-groups in the same
original quotient T/P. The square action and its markings are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem elementary64_core_product
    (P E Q : Subgroup G) (hPQ : P≤Q) (hEQ : E≤Q)
    [IsElementaryAbelian 2 E] (hEN : Q≤normalizer (E : Set G))
    (hE : Nat.card E=64) (hI : Nat.card (E⊓P : Subgroup G)=16)
    (hp : IsPGroup 2 P) (q : Q→*Equiv.Perm (Fin 4))
    (hq : Function.Surjective q) (hk : q.ker=P.subgroupOf Q) :
    Q.pCoreIn 2=P⊔E := by
  let E₀ := E.subgroupOf Q
  let I := E₀.map q
  let : E₀.Normal := (normal_subgroupOf_iff_le_normalizer hEQ).mpr hEN
  let : I.Normal := Subgroup.Normal.map inferInstance q hq
  have hi : IsPGroup 2 I := (IsElementaryAbelian.isPGroup 2 E).comap_subtype.map q
  have hIc : Nat.card I=4 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map E₀ q
    have hEc : Nat.card E₀=64 := (Nat.card_congr (subgroupOfEquivOfLe hEQ).toEquiv).trans hE
    have hInt : Nat.card (E₀⊓q.ker : Subgroup Q)=16 := by
      rw [hk]
      change Nat.card ((E⊓P).subgroupOf Q)=16
      exact (Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hEQ)).toEquiv).trans hI
    rw [hInt,hEc] at hh
    change 16*Nat.card I=64 at hh
    omega
  have hIcore : I=pCore 2 (Equiv.Perm (Fin 4)) := by
    have hle : I≤pCore 2 (Equiv.Perm (Fin 4)) := le_sSup ⟨inferInstance,hi⟩
    apply eq_of_le_of_card_ge hle
    rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card,hIc]
  have he : pCore 2 Q=E₀⊔q.ker := by
    rw [←q.comap_pCore_of_ker_isPGroup hq (hk ▸ hp.comap_subtype),
      ←hIcore,comap_map_eq]
  change (pCore 2 Q).map Q.subtype=P⊔E
  rw [he,Subgroup.map_sup,hk,map_subgroupOf_eq_of_le hPQ,
    map_subgroupOf_eq_of_le hEQ,sup_comm]

omit [Finite G] in
private theorem dihedral_images_ne_of_core_products
    (T : Sylow 2 G) (π : T→*DihedralGroup 4)
    (U W : Subgroup G) (hUT : U≤(T : Subgroup G)) (hWT : W≤(T : Subgroup G))
    (hne : (π.ker.map (T : Subgroup G).subtype)⊔U≠
      (π.ker.map (T : Subgroup G).subtype)⊔W) :
    (U.subgroupOf T).map π≠(W.subgroupOf T).map π := by
  intro he
  have hh := congrArg (Subgroup.comap π) he
  rw [comap_map_eq,comap_map_eq] at hh
  have hm := congrArg (Subgroup.map (T : Subgroup G).subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hUT,
    map_subgroupOf_eq_of_le hWT] at hm
  exact hne (by simpa only [sup_comm] using hm)

variable {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_pair_four_images
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ (T : Subgroup G)≤Y ∧ Nat.card P=128 ∧ ∃ hEx : IsExtraspecial 2 P, letI := hEx
      
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
                  ∀ y : Y, y.val∈U ∨ y.val∈W →
                    ∀ v, ClassicalOrthogonal.formD 3 (ZMod 2)
                      ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v-v)=0 := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    e,f,hfk,hfe,hsing⟩ :=
    original_tripleSix_escaping_pair_square_action h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
  let Q₁ := normalizer (W : Set G)⊓centralizer ({z} : Set G)
  let := hEx
  let := D.elementary
  let := hWe
  have hTQ₀ : (T : Subgroup G)≤Q₀ := hint.symm ▸ inf_le_left
  have hTQ₁ : (T : Subgroup G)≤Q₁ := hint.symm ▸ inf_le_right
  have hWT : W≤(T : Subgroup G) := hWR.trans hRT
  have hQU : Q₀≤normalizer (U : Set G) := by
    rw [(original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.1]
    exact inf_le_left
  have hUc : Nat.card U=64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
  have hp : IsPGroup 2 P := IsExtraspecial.isPGroup 2 P
  have hcore₀ : Q₀.pCoreIn 2=P⊔U := elementary64_core_product P U Q₀
    (hPT.trans hTQ₀) (D.le_sylow.trans hTQ₀) hQU hUc hUP hp q₀ hq₀ hq₀ker
  have hcore₁ : Q₁.pCoreIn 2=P⊔W := elementary64_core_product P W Q₁
    (hPT.trans hTQ₁) (hWT.trans hTQ₁) inf_le_left hWc hWP hp q hq hqker
  have hWimage : Nat.card ((W.subgroupOf T).map π)=4 := by
    have hmap : (W.subgroupOf T⊓π.ker : Subgroup T).map (T : Subgroup G).subtype=W⊓P := by
      rw [Subgroup.map_inf _ _ _ (T : Subgroup G).subtype_injective,
        map_subgroupOf_eq_of_le hWT]
    have hInt : Nat.card (W.subgroupOf T⊓π.ker : Subgroup T)=16 := by
      rw [←card_map_of_injective (T : Subgroup G).subtype_injective,hmap,hWP]
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (W.subgroupOf T) π
    rw [hInt,Nat.card_congr (subgroupOfEquivOfLe hWT).toEquiv,hWc] at hh
    omega
  have himages : (U.subgroupOf T).map π≠(W.subgroupOf T).map π :=
    dihedral_images_ne_of_core_products T π U W D.le_sylow hWT
      (fun he => hcorene (hcore₀.trans (he.trans hcore₁.symm)))
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing⟩

end CFSG.Quasithin.Chapter12.Section07
