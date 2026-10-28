module

public import Stellmacher.SectionThree.LemmaThreeOne

/-!
# Stellmacher (3.2): the local `PSet` generates the 2-prime residual

If `L` belongs to `LSet ⊤ S`, then `S` is the ambient image of a Sylow
2-subgroup `T` of `L`, `O₂(L)` is nontrivial, and `S ≠ O₂(L)`. This module
applies Stellmacher (3.1) to the finite group `L` and `T`, rules out its
empty-family alternative using `S ≠ O₂(L)`, and maps the resulting equality
back through `L.subtype`.

The main bookkeeping identifies the internal family from (3.1) with
`PSet L S`. Subgroups of `L` and their ambient images have corresponding
2-cores and unique maximal overgroups. Moreover every internal family member
contains `O₂(L)`: this core lies in the Sylow subgroup, remains normal after
restriction, and is nontrivial. Hence the extra nontrivial-core condition in
`PSet` is automatic. Reindexing the two joins through the subgroup-of/image
order equivalence gives the stated ambient equality.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (3.2), where
the result is stated as a direct consequence of (3.1).
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

universe u

private theorem twoPrimeResidualAmbient_top_eq
    {H : Type u} [Group H] [Finite H] :
    twoPrimeResidualAmbient (⊤ : Subgroup H) =
      ⨆ P : Sylow 2 H, (P : Subgroup H) := by
  unfold twoPrimeResidualAmbient twoPrimeResidualSubgroup
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun P ↦ ?_
    let Q : Sylow 2 H := P.mapSurjective
      (f := (⊤ : Subgroup H).subtype) (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    rw [← Sylow.coe_mapSurjective]
    exact le_iSup (fun R : Sylow 2 H ↦ (R : Subgroup H)) Q
  · refine iSup_le fun Q ↦ ?_
    let e : H ≃* (⊤ : Subgroup H) := Subgroup.topEquiv.symm
    let he : Function.Surjective e.toMonoidHom := e.surjective
    let P : Sylow 2 (⊤ : Subgroup H) := Q.mapSurjective he
    have hPmap : (P : Subgroup (⊤ : Subgroup H)).map
        (⊤ : Subgroup H).subtype = (Q : Subgroup H) := by
      dsimp only [P]
      rw [Sylow.coe_mapSurjective, Subgroup.map_map]
      have hcomp : (⊤ : Subgroup H).subtype.comp e.toMonoidHom =
          MonoidHom.id H := by ext x; rfl
      rw [hcomp, Subgroup.map_id]
    rw [← hPmap]
    exact le_iSup (fun R : Sylow 2 (⊤ : Subgroup H) ↦
      (R : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype) P

private theorem map_internal_ambient
    {G : Type u} [Group G] (L : Subgroup G) (P : Subgroup L)
    (M : Subgroup P) :
    let eP : P ≃* P.map L.subtype :=
      P.equivMapOfInjective L.subtype L.subtype_injective
    (M.map eP.toMonoidHom).map (P.map L.subtype).subtype =
      (M.map P.subtype).map L.subtype := by
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem twoCoreAmbient_map_subtype
    {G : Type u} [Group G] (L : Subgroup G) (P : Subgroup L) :
    twoCoreAmbient (P.map L.subtype) =
      (twoCoreAmbient P).map L.subtype := by
  let eP : P ≃* P.map L.subtype :=
    P.equivMapOfInjective L.subtype L.subtype_injective
  have hcore : (pCore 2 P).map eP.toMonoidHom =
      pCore 2 (P.map L.subtype) := pCore_map_iso 2 eP
  unfold twoCoreAmbient
  rw [← hcore, map_internal_ambient]

private theorem uniqueMaximal_map_subtype
    {G : Type u} [Group G] {S : Subgroup G}
    (L : Subgroup G) (T P : Subgroup L)
    (hTmap : T.map L.subtype = S) :
    IsUniqueMaximalContaining T P ↔
      IsUniqueMaximalContaining S (P.map L.subtype) := by
  let eP : P ≃* P.map L.subtype :=
    P.equivMapOfInjective L.subtype L.subtype_injective
  constructor
  · rintro ⟨M, hMcoatom, hTM, hMunique⟩
    refine ⟨M.map eP.toMonoidHom,
      (OrderIso.isCoatom_iff eP.mapSubgroup M).2 hMcoatom, ?_, ?_⟩
    · rw [map_internal_ambient, ← hTmap]
      exact Subgroup.map_mono hTM
    · intro N hNcoatom hSN
      let M' : Subgroup P := N.map eP.symm.toMonoidHom
      have hM'coatom : IsCoatom M' :=
        (OrderIso.isCoatom_iff eP.symm.mapSubgroup N).2 hNcoatom
      have hforward : M'.map eP.toMonoidHom = N := by
        dsimp only [M']
        rw [Subgroup.map_map]
        simp
      have hTM' : T ≤ M'.map P.subtype := by
        apply Subgroup.map_subtype_le_map_subtype.mp
        rw [hTmap, ← map_internal_ambient L P M', hforward]
        exact hSN
      have hM'eq : M' = M := hMunique M' hM'coatom hTM'
      rw [← hforward, hM'eq]
  · rintro ⟨N, hNcoatom, hSN, hNunique⟩
    let M : Subgroup P := N.map eP.symm.toMonoidHom
    have hMcoatom : IsCoatom M :=
      (OrderIso.isCoatom_iff eP.symm.mapSubgroup N).2 hNcoatom
    have hforward : M.map eP.toMonoidHom = N := by
      dsimp only [M]
      rw [Subgroup.map_map]
      simp
    refine ⟨M, hMcoatom, ?_, ?_⟩
    · apply Subgroup.map_subtype_le_map_subtype.mp
      rw [hTmap, ← map_internal_ambient L P M, hforward]
      exact hSN
    · intro M' hM'coatom hTM'
      let N' : Subgroup (P.map L.subtype) := M'.map eP.toMonoidHom
      have hN'coatom : IsCoatom N' :=
        (OrderIso.isCoatom_iff eP.mapSubgroup M').2 hM'coatom
      have hSN' : S ≤ N'.map (P.map L.subtype).subtype := by
        dsimp only [N']
        rw [map_internal_ambient, ← hTmap]
        exact Subgroup.map_mono hTM'
      have hN'eq : N' = N := hNunique N' hN'coatom hSN'
      apply eP.mapSubgroup.injective
      change M'.map eP.toMonoidHom = M.map eP.toMonoidHom
      dsimp only [N'] at hN'eq
      exact hN'eq.trans hforward.symm

private theorem isSylowSubgroupIn_of_between
    {G : Type u} [Group G] [Finite G]
    (U S P : Subgroup G) (hSP : S ≤ P) (hPU : P ≤ U)
    (hSylow : IsSylowSubgroupIn S U) :
    IsSylowSubgroupIn S P := by
  obtain ⟨T, hTmap⟩ := hSylow
  let PU : Subgroup U := P.subgroupOf U
  have hTlePU : (T : Subgroup U) ≤ PU := by
    intro t ht
    have htS : (t : G) ∈ S := by
      rw [← hTmap]
      exact ⟨t, ht, rfl⟩
    exact hSP htS
  let TU : Sylow 2 PU := T.subtype hTlePU
  let e : PU ≃* P := Subgroup.subgroupOfEquivOfLe hPU
  let he : Function.Surjective e.toMonoidHom := e.surjective
  let TP : Sylow 2 P := TU.mapSurjective he
  refine ⟨TP, ?_⟩
  dsimp only [TP]
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : P.subtype.comp e.toMonoidHom =
      U.subtype.comp PU.subtype := by ext x; rfl
  rw [hcomp, ← Subgroup.map_map,
    show (TU : Subgroup PU) = (T : Subgroup U).subgroupOf PU by
      exact Sylow.coe_subtype T hTlePU,
    Subgroup.map_subgroupOf_eq_of_le hTlePU, hTmap]

private theorem twoCoreAmbient_mono_of_normal
    {G : Type u} [Group G]
    (L E : Subgroup G) (hEL : E ≤ L)
    (hcoreE : twoCoreAmbient L ≤ E) :
    twoCoreAmbient L ≤ twoCoreAmbient E := by
  let K : Subgroup E := (twoCoreAmbient L).subgroupOf E
  have hcoreLleL : twoCoreAmbient L ≤ L :=
    Subgroup.map_subtype_le (pCore 2 L)
  have hcoreNormalL : ((twoCoreAmbient L).subgroupOf L).Normal := by
    unfold twoCoreAmbient
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hLnorm : L ≤ Subgroup.normalizer (twoCoreAmbient L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreLleL).1 hcoreNormalL
  have hKnormal : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreE).2
      (hEL.trans hLnorm)
  have hcoreP : IsPGroup 2 (twoCoreAmbient L) :=
    (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  let eK : K ≃* twoCoreAmbient L :=
    Subgroup.subgroupOfEquivOfLe hcoreE
  have hKp : IsPGroup 2 K := hcoreP.of_equiv eK.symm
  have hKle : K ≤ pCore 2 E := le_sSup ⟨hKnormal, hKp⟩
  calc
    twoCoreAmbient L = K.map E.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hcoreE).symm
    _ ≤ (pCore 2 E).map E.subtype := Subgroup.map_mono hKle
    _ = twoCoreAmbient E := rfl

private theorem internalFamily_iff_pSet
    {G : Type u} [Group G] [Finite G]
    (S L : Subgroup G) (T : Sylow 2 L)
    (hTmap : (T : Subgroup L).map L.subtype = S)
    (hSylowL : IsSylowSubgroupIn S L)
    (hcoreLne : twoCoreAmbient L ≠ ⊥)
    (P : Subgroup L) :
    ((T : Subgroup L) ≤ P ∧
      (T : Subgroup L) ≠ twoCoreAmbient P ∧
      IsUniqueMaximalContaining (T : Subgroup L) P) ↔
      P.map L.subtype ∈ PSet L S := by
  let E : Subgroup G := P.map L.subtype
  have hEL : E ≤ L := Subgroup.map_subtype_le P
  constructor
  · rintro ⟨hTP, hTne, hUnique⟩
    have hSE : S ≤ E := by
      rw [← hTmap]
      exact Subgroup.map_mono hTP
    have hSylowE : IsSylowSubgroupIn S E :=
      isSylowSubgroupIn_of_between L S E hSE hEL hSylowL
    have hcoreLleT : pCore 2 L ≤ (T : Subgroup L) :=
      (pCore_isPGroup (p := 2) (G := L)).le_sylow_of_normal T
    have hcoreLleS : twoCoreAmbient L ≤ S := by
      calc
        twoCoreAmbient L = (pCore 2 L).map L.subtype := rfl
        _ ≤ (T : Subgroup L).map L.subtype :=
          Subgroup.map_mono hcoreLleT
        _ = S := hTmap
    have hcoreLleEcore : twoCoreAmbient L ≤ twoCoreAmbient E :=
      twoCoreAmbient_mono_of_normal L E hEL (hcoreLleS.trans hSE)
    have hcoreEne : twoCoreAmbient E ≠ ⊥ := by
      intro hEbot
      apply hcoreLne
      exact le_bot_iff.mp (hcoreLleEcore.trans_eq hEbot)
    have hSne : S ≠ twoCoreAmbient E := by
      intro hSeq
      apply hTne
      apply Subgroup.map_subtype_inj.mp
      rw [hTmap, ← twoCoreAmbient_map_subtype]
      exact hSeq
    exact ⟨⟨hEL, hSylowE, hcoreEne, hSne⟩,
      (uniqueMaximal_map_subtype L (T : Subgroup L) P hTmap).1 hUnique⟩
  · rintro ⟨⟨_hEL, hSylowE, _hcoreEne, hSne⟩, hUnique⟩
    have hSE : S ≤ E := by
      obtain ⟨Q, hQmap⟩ := hSylowE
      rw [← hQmap]
      exact Subgroup.map_subtype_le (Q : Subgroup E)
    have hTP : (T : Subgroup L) ≤ P := by
      apply Subgroup.map_subtype_le_map_subtype.mp
      rw [hTmap]
      exact hSE
    have hTne : (T : Subgroup L) ≠ twoCoreAmbient P := by
      intro hTeq
      apply hSne
      calc
        S = (T : Subgroup L).map L.subtype := hTmap.symm
        _ = (twoCoreAmbient P).map L.subtype :=
          congrArg (fun Q : Subgroup L ↦ Q.map L.subtype) hTeq
        _ = twoCoreAmbient E :=
          (twoCoreAmbient_map_subtype L P).symm
    exact ⟨hTP, hTne,
      (uniqueMaximal_map_subtype L (T : Subgroup L) P hTmap).2 hUnique⟩

public theorem lemma_three_two
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (L : Subgroup G) (hL : L ∈ LSet (⊤ : Subgroup G) S) :
    twoPrimeResidualAmbient L =
      ⨆ P : {P : Subgroup G // P ∈ PSet L S}, (P : Subgroup G) := by
  obtain ⟨T, hTmap⟩ := hL.2.1
  have hTne : (T : Subgroup L) ≠ ⊥ := by
    intro hTbot
    apply h.nontrivial_two_subgroup.1
    rw [← hTmap, hTbot, Subgroup.map_bot]
  let _ : Nontrivial T :=
    (Subgroup.nontrivial_iff_ne_bot (T : Subgroup L)).2 hTne
  have hEvenT : Even (Nat.card T) := by
    obtain ⟨n, hnpos, hcard⟩ :=
      T.isPGroup'.nontrivial_iff_card.mp inferInstance
    rw [hcard]
    exact (by decide : Even (2 : ℕ)).pow_of_ne_zero (Nat.ne_of_gt hnpos)
  have hEvenL : Even (Nat.card L) :=
    hEvenT.trans_dvd (Subgroup.card_subgroup_dvd_card (T : Subgroup L))
  let hLocal : Hypotheses L (T : Subgroup L) :=
    { even_order := hEvenL
      nontrivial_two_subgroup := ⟨hTne, T.isPGroup'⟩ }
  let F : Set (Subgroup L) :=
    {P | (T : Subgroup L) ≤ P ∧
      (T : Subgroup L) ≠ twoCoreAmbient P ∧
      IsUniqueMaximalContaining (T : Subgroup L) P}
  have hthree := lemma_three_one T hLocal F rfl
  have hresidual : twoPrimeResidualAmbient (⊤ : Subgroup L) =
      ⨆ P : {P : Subgroup L // P ∈ F}, (P : Subgroup L) := by
    rcases hthree with hcore | hresidual
    · exfalso
      apply hL.2.2.2
      calc
        S = (T : Subgroup L).map L.subtype := hTmap.symm
        _ = (pCore 2 L).map L.subtype :=
          congrArg (fun Q : Subgroup L ↦ Q.map L.subtype) hcore.2
        _ = twoCoreAmbient L := rfl
    · exact hresidual
  have hresidualMap :
      (twoPrimeResidualAmbient (⊤ : Subgroup L)).map L.subtype =
        twoPrimeResidualAmbient L := by
    rw [twoPrimeResidualAmbient_top_eq]
    rfl
  have hmapped :=
    congrArg (fun Q : Subgroup L ↦ Q.map L.subtype) hresidual
  rw [Subgroup.map_iSup] at hmapped
  calc
    twoPrimeResidualAmbient L =
        (twoPrimeResidualAmbient (⊤ : Subgroup L)).map L.subtype :=
      hresidualMap.symm
    _ = ⨆ P : {P : Subgroup L // P ∈ F},
        (P : Subgroup L).map L.subtype := hmapped
    _ = ⨆ P : {P : Subgroup G // P ∈ PSet L S},
        (P : Subgroup G) := by
      apply le_antisymm
      · refine iSup_le fun P ↦ ?_
        have hPmem : P.val.map L.subtype ∈ PSet L S := by
          apply (internalFamily_iff_pSet S L T hTmap hL.2.1
            hL.2.2.1 P.val).1
          exact P.property
        exact le_iSup
          (fun Q : {Q : Subgroup G // Q ∈ PSet L S} ↦
            (Q : Subgroup G))
          ⟨P.val.map L.subtype, hPmem⟩
      · refine iSup_le fun E ↦ ?_
        let P : Subgroup L := E.val.subgroupOf L
        have hPmap : P.map L.subtype = E.val :=
          Subgroup.map_subgroupOf_eq_of_le E.property.1.1
        have hPmem : P ∈ F := by
          apply (internalFamily_iff_pSet S L T hTmap hL.2.1
            hL.2.2.1 P).2
          rw [hPmap]
          exact E.property
        have hle := le_iSup
          (fun Q : {Q : Subgroup L // Q ∈ F} ↦
            (Q : Subgroup L).map L.subtype)
          ⟨P, hPmem⟩
        simpa only [hPmap] using hle

end Stellmacher.SectionThree
