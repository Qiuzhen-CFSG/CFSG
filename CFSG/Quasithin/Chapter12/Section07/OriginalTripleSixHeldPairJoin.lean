module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairComparison
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The generated group of the original Held parabolics

The actual original endpoints meet in T. Their symmetric-four maps have a
common two-group kernel, so their quotients by their two-cores are S3. This
constructs the Goldschmidt triple in their actual join. Equality of that join
with the full extraspecial normalizer remains a separate recognition duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem symmetricThree_core_quotient
    {Q : Type*} [Group Q] [Finite Q] (q : Q→*Equiv.Perm (Fin 4))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker) :
    Nonempty ((Q⧸pCore 2 Q)≃*Equiv.Perm (Fin 3)) := by
  let e := q.pCoreQuotientEquiv hq hk
  let f := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom
  have hf := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective
  have he : f.ker=pCore 2 (Equiv.Perm (Fin 4)) :=
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩

private theorem pair_join_goldschmidt (T : Sylow 2 G) (A B : Subgroup G)
    (hi : A⊓B=(T : Subgroup G))
    (hA : Nonempty ((A⧸pCore 2 A)≃*Equiv.Perm (Fin 3)))
    (hB : Nonempty ((B⧸pCore 2 B)≃*Equiv.Perm (Fin 3))) :
    ChapterF.IsGoldschmidtTriple (A.subgroupOf (A⊔B)) (B.subgroupOf (A⊔B)) := by
  let J := A⊔B
  have hAJ : A≤J := le_sup_left
  have hBJ : B≤J := le_sup_right
  have hTJ : (T : Subgroup G)≤J := hi.symm ▸ inf_le_left.trans hAJ
  have quotient (C : Subgroup G) (hCJ : C≤J)
      (hc : Nonempty ((C⧸pCore 2 C)≃*Equiv.Perm (Fin 3))) :
      Nonempty (((C.subgroupOf J)⧸pCore 2 (C.subgroupOf J))≃*Equiv.Perm (Fin 3)) := by
    obtain ⟨e⟩ := hc
    let f := (subgroupOfEquivOfLe hCJ).toMonoidHom
    have hf : Function.Surjective f := (subgroupOfEquivOfLe hCJ).surjective
    have hk : IsPGroup 2 f.ker := by
      rw [(MonoidHom.ker_eq_bot_iff f).mpr (subgroupOfEquivOfLe hCJ).injective]
      exact IsPGroup.of_card (n := 0) (by simp)
    exact ⟨(f.pCoreQuotientEquiv hf hk).trans e⟩
  refine ⟨?_,quotient A hAJ hA,quotient B hBJ hB,T.subtype hTJ,?_⟩
  · rw [←subgroupOf_sup hAJ hBJ,subgroupOf_self]
  · change (A⊓B).subgroupOf J=(T : Subgroup G).subgroupOf J
    rw [hi]

private theorem normal_two_symmetricFour_cover_cases
    (P C Q : Subgroup G) (hPC : P≤C) (hCQ : C≤Q)
    (hCN : Q≤normalizer (C : Set G)) (hp : IsPGroup 2 C)
    (q : Q→*Equiv.Perm (Fin 4)) (hq : Function.Surjective q)
    (hk : q.ker=P.subgroupOf Q) : C=P ∨ C=Q.pCoreIn 2 := by
  let A := C.subgroupOf Q
  let N := A.map q
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hCQ).mpr hCN
  let : N.Normal := Subgroup.Normal.map inferInstance q hq
  have hn : IsPGroup 2 N := hp.comap_subtype.map q
  have hle : N≤pCore 2 (Equiv.Perm (Fin 4)) := le_sSup ⟨inferInstance,hn⟩
  have hker : q.ker≤A := hk ▸ subgroupOf_mono Q hPC
  have hpre : N.comap q=A := by rw [comap_map_eq,sup_eq_left.mpr hker]
  have cases := Theory.SpecificGroups.SymmetricSix.DuadCalculation.normal_subgroup_core N
    (Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq.symm ▸ hle)
  rcases cases with he | he
  · apply Or.inl
    have hh : A=P.subgroupOf Q := by
      rw [←hpre,he,MonoidHom.comap_bot,hk]
    have hm := congrArg (Subgroup.map Q.subtype) hh
    simpa only [A,map_subgroupOf_eq_of_le hCQ,
      map_subgroupOf_eq_of_le (hPC.trans hCQ)] using hm
  · apply Or.inr
    have hkp : IsPGroup 2 q.ker := hp.comap_subtype.to_le hker
    have hh : A=pCore 2 Q := by
      rw [←hpre,he,Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
      exact q.comap_pCore_of_ker_isPGroup hq hkp
    have hm := congrArg (Subgroup.map Q.subtype) hh
    simpa only [A,pCoreIn,map_subgroupOf_eq_of_le hCQ] using hm

private theorem pair_join_core_eq
    (T : Sylow 2 G) (P A B : Subgroup G) (hi : A⊓B=(T : Subgroup G))
    (hp : IsPGroup 2 P) (hPT : P≤(T : Subgroup G))
    (hN : A⊔B≤normalizer (P : Set G))
    (qA : A→*Equiv.Perm (Fin 4)) (hqA : Function.Surjective qA)
    (hkA : qA.ker=P.subgroupOf A)
    (qB : B→*Equiv.Perm (Fin 4)) (hqB : Function.Surjective qB)
    (hkB : qB.ker=P.subgroupOf B)
    (hne : A.pCoreIn 2≠B.pCoreIn 2) : (A⊔B).pCoreIn 2=P := by
  let J := A⊔B
  let C := J.pCoreIn 2
  have hTJ : (T : Subgroup G)≤J := hi.symm ▸ inf_le_left.trans le_sup_left
  have hCT : C≤(T : Subgroup G) := by
    rintro _ ⟨c,hc,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTJ) hc
  have hPC : P≤C := le_pCoreIn_of_normalizes hp (hPT.trans hTJ) hN
  have hCN : J≤normalizer (C : Set G) := by
    simpa only [C,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  have hCA : C≤A := hCT.trans (hi.symm ▸ inf_le_left)
  have hCB : C≤B := hCT.trans (hi.symm ▸ inf_le_right)
  rcases normal_two_symmetricFour_cover_cases P C A hPC hCA
    (le_sup_left.trans hCN) (isPGroup_pCoreIn 2 J) qA hqA hkA with he | he
  · exact he
  · rcases normal_two_symmetricFour_cover_cases P C B hPC hCB
      (le_sup_right.trans hCN) (isPGroup_pCoreIn 2 J) qB hqB hkB with hf | hf
    · exact hf
    · exact (hne (he.symm.trans hf)).elim

variable {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal original pair generates a Goldschmidt triple inside its actual
join, retaining the same extraspecial kernel and distinct local two-cores. -/
theorem original_tripleSix_escaping_pair_join
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
              (Q₀.subgroupOf J).pCoreIn 2≠(Q.subgroupOf J).pCoreIn 2 ∧ J.pCoreIn 2=P := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene⟩ :=
    original_tripleSix_escaping_pair_comparison h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
  let Q₁ := normalizer (W : Set G)⊓centralizer ({z} : Set G)
  let J := Q₀⊔Q₁
  let := hEx
  have hp : IsPGroup 2 P := IsExtraspecial.isPGroup 2 P
  have hq₀p : IsPGroup 2 q₀.ker := hq₀ker ▸ hp.comap_subtype
  have hqp : IsPGroup 2 q.ker := hqker ▸ hp.comap_subtype
  have ht := pair_join_goldschmidt T Q₀ Q₁ hint
    (symmetricThree_core_quotient q₀ hq₀ hq₀p) (symmetricThree_core_quotient q hq hqp)
  have hc : (Q₀.subgroupOf J).pCoreIn 2≠(Q₁.subgroupOf J).pCoreIn 2 := by
    intro he
    have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show Q₀≤J from le_sup_left),
      map_subgroupOf_eq_of_le (show Q₁≤J from le_sup_right)] at hh
    exact hcorene hh
  have hJcore : J.pCoreIn 2=P := pair_join_core_eq T P Q₀ Q₁ hint hp hPT
    (sup_le hMY hQY) q₀ hq₀ hq₀ker q hq hqker hcorene
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,sup_le hMY hQY,ht,hc,hJcore⟩

end CFSG.Quasithin.Chapter12.Section07
