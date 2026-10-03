module

public import Stellmacher.SectionFour.BaumannConfiguration
public import Stellmacher.CharacteristicTwoNormal
public import Stellmacher.OmegaOneCenterMap

/-!
# The normal supplement used in Stellmacher (4.6)

For the critical pair supplied by the Baumann configuration, write
`E = O²(Pstar)O₂(C)`, with `O₂(C)` Sylow in `E`. This module
constructs native Sylow witnesses inside `Pstar` and `E` and proves
the hypotheses needed to apply the Section Two normal-supplement transfer.
It also proves that `E` is solvable, has even order, and has characteristic 2.

The residual and the fixed Sylow generate `Pstar`. The latter normalizes
both the residual and `O₂(C)`, so `E` is normal in `Pstar`.
Characteristic 2 descends to this normal subgroup. The central involutions
of the fixed Sylow lie in the center of `C`, hence in `O₂(C)`.
Injective omega-center transport and the subgroup-image equivalence
translate these facts to the native Sylow witnesses.

Source: `refs/latex/stellmacher-n-group.tex`, second paragraph of (4.6),
preparing the application of (2.3). The assumptions are the corresponding
proved outputs of `exists_baumann_configuration`.
-/

open scoped Pointwise

namespace Stellmacher.SectionFour

private theorem le_normalizer_core
    {G : Type*} [Group G] (D : Subgroup G) :
    D ≤ Subgroup.normalizer (twoCoreAmbient D : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- The residual-core product in the Baumann configuration has all
normal-supplement and standing local hypotheses needed for (2.3). -/
public theorem baumann_normal_supplement_data
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    (E.subgroupOf Pstar).Normal ∧
    Group.IsSolvable (E.subgroupOf Pstar) ∧
    IsCharacteristicTwoType (E.subgroupOf Pstar) ∧
    Even (Nat.card (E.subgroupOf Pstar)) ∧
    ∃ (SP : Sylow 2 Pstar) (QE : Sylow 2 (E.subgroupOf Pstar)),
      (SP : Subgroup Pstar).map Pstar.subtype = (S : Subgroup G) ∧
      (((QE : Subgroup (E.subgroupOf Pstar)).map (E.subgroupOf Pstar).subtype).map
        Pstar.subtype) = twoCoreAmbient (cSubgroup S) ∧
      E.subgroupOf Pstar ⊔ (SP : Subgroup Pstar) = ⊤ ∧
      (QE : Subgroup (E.subgroupOf Pstar)).map (E.subgroupOf Pstar).subtype ≤
        (SP : Subgroup Pstar) ∧
      SectionTwo.zSubgroup SP ≤
        (QE : Subgroup (E.subgroupOf Pstar)).map (E.subgroupOf Pstar).subtype ∧
      (SP : Subgroup Pstar) ≤ Subgroup.normalizer
        ((((QE : Subgroup (E.subgroupOf Pstar)).map
          (E.subgroupOf Pstar).subtype) : Subgroup Pstar) : Set Pstar) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SP, hSP⟩ := hpair.2.1.1.2.1
  have hSPstar : (S : Subgroup G) ≤ Pstar := by
    rw [← hSP]
    exact Subgroup.map_subtype_le _
  have hSPleft : (S : Subgroup G) ≤ P := by
    obtain ⟨T, hT⟩ := hpair.1.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hSC : (S : Subgroup G) ≤ cSubgroup S := hSPleft.trans hPC
  let Q := twoCoreAmbient (cSubgroup S)
  let A := twoResidualAmbient Pstar
  have hQS : Q ≤ (S : Subgroup G) := by
    let T := S.subtype hSC
    have hTm : (T : Subgroup (cSubgroup S)).map (cSubgroup S).subtype =
        (S : Subgroup G) := Subgroup.map_subgroupOf_eq_of_le hSC
    rw [← hTm]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := cSubgroup S)).le_sylow_of_normal T)
  have hSNQ : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) :=
    hSC.trans (le_normalizer_core _)
  have hEeq : E = A ⊔ Q := by
    apply le_antisymm
    · intro x hx
      change x ∈ (E : Set G) at hx
      rw [hE] at hx
      obtain ⟨a, ha, q, hq, rfl⟩ := hx
      exact (A ⊔ Q).mul_mem ((le_sup_left : A ≤ A ⊔ Q) ha)
        ((le_sup_right : Q ≤ A ⊔ Q) hq)
    · apply sup_le
      · intro a ha
        have hm : a ∈ (A : Set G) * (Q : Set G) := ⟨a, ha, 1, Q.one_mem, mul_one a⟩
        rwa [← hE] at hm
      · intro q hq
        have hm : q ∈ (A : Set G) * (Q : Set G) := ⟨1, A.one_mem, q, hq, one_mul q⟩
        rwa [← hE] at hm
  have hAP : A ≤ Pstar := Subgroup.map_subtype_le _
  have hAN : (A.subgroupOf Pstar).Normal := by
    rw [show A = (twoResidualSubgroup Pstar).map Pstar.subtype from rfl,
      subgroupOf_map_subtype_eq]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal (fun N ↦ Subgroup.normal_iInf_normal (fun hN ↦ hN.1))
  have hPNA : Pstar ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hAN
  have hSNE : (S : Subgroup G) ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEeq]
    exact (le_inf (hSPstar.trans hPNA) hSNQ).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup A Q)
  have hfact : A ⊔ (S : Subgroup G) = Pstar :=
    SectionThree.twoResidual_sup_sylowImage ⟨SP, hSP⟩
  have hPNE : Pstar ≤ Subgroup.normalizer (E : Set G) := by
    rw [← hfact]
    exact sup_le ((hEeq ▸ (le_sup_left : A ≤ A ⊔ Q)).trans Subgroup.le_normalizer) hSNE
  have hEN : (E.subgroupOf Pstar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mpr hPNE
  let _ : (E.subgroupOf Pstar).Normal := hEN
  have hsolvE : Group.IsSolvable (E.subgroupOf Pstar) := by
    let _ : Group.IsSolvable Pstar := hsolv
    infer_instance
  have hcharE : IsCharacteristicTwoType (E.subgroupOf Pstar) :=
    characteristicTwo_normal_subgroup hsolv hchar (E.subgroupOf Pstar)
  obtain ⟨TQ, hTQ⟩ := hSyl
  change (TQ : Subgroup E).map E.subtype = Q at hTQ
  let e : E.subgroupOf Pstar ≃* E := Subgroup.subgroupOfEquivOfLe hEP
  let QE : Sylow 2 (E.subgroupOf Pstar) :=
    TQ.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQEm : (((QE : Subgroup (E.subgroupOf Pstar)).map
      (E.subgroupOf Pstar).subtype).map Pstar.subtype) = Q := by
    change (((TQ : Subgroup E).map e.symm.toMonoidHom).map
      (E.subgroupOf Pstar).subtype).map Pstar.subtype = Q
    rw [Subgroup.map_map, Subgroup.map_map]
    exact hTQ
  have hQE : Q ≤ E := by
    rw [← hTQ]
    exact Subgroup.map_subtype_le _
  have hQp : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := cSubgroup S)).map (cSubgroup S).subtype
  have hQne : Q ≠ ⊥ := twoCore_cSubgroup_ne_bot S heven
  let _ : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.mp inferInstance
  have htwoQ : 2 ∣ Nat.card Q := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hevenE : Even (Nat.card (E.subgroupOf Pstar)) := by
    rw [Nat.card_congr e.toEquiv]
    exact even_iff_two_dvd.mpr (htwoQ.trans (Subgroup.card_dvd_of_le hQE))
  refine ⟨hEN, hsolvE, hcharE, hevenE, SP, QE, hSP, hQEm, ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective Pstar.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEP, hSP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply le_antisymm (sup_le hEP hSPstar)
    rw [← hfact]
    exact sup_le ((hEeq ▸ (le_sup_left : A ≤ A ⊔ Q)).trans le_sup_left) le_sup_right
  · exact (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp (by rwa [hQEm, hSP])
  · have hZQ : zSubgroup S ≤ Q := by
      have hZS : zSubgroup S ≤ (S : Subgroup G) := fun z hz ↦
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
      have hZC : zSubgroup S ≤ cSubgroup S := hZS.trans hSC
      have hZN : ((zSubgroup S).subgroupOf (cSubgroup S)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hZC).mpr
          (Subgroup.centralizer_le_normalizer _)
      have hZp : IsPGroup 2 ((zSubgroup S).subgroupOf (cSubgroup S)) :=
        (S.isPGroup'.to_le hZS).comap_of_injective (cSubgroup S).subtype
          (cSubgroup S).subtype_injective
      rw [← Subgroup.map_subgroupOf_eq_of_le hZC]
      exact Subgroup.map_mono (le_sSup ⟨hZN, hZp⟩)
    apply (Subgroup.map_le_map_iff_of_injective Pstar.subtype_injective).mp
    rw [hQEm]
    change (omegaOneCenterAmbient (SP : Subgroup Pstar)).map Pstar.subtype ≤ Q
    rw [← omegaOneCenterAmbient_map_injective Pstar.subtype Pstar.subtype_injective, hSP]
    exact hZQ
  · intro s hs
    apply Subgroup.mem_normalizer_iff.mpr
    intro q
    have hsG : (s : G) ∈ (S : Subgroup G) := by rw [← hSP]; exact ⟨s, hs, rfl⟩
    have hh := (Subgroup.mem_normalizer_iff.mp (hSNQ hsG)) (q : G)
    have hmem : ∀ x : Pstar,
        x ∈ (QE : Subgroup (E.subgroupOf Pstar)).map (E.subgroupOf Pstar).subtype ↔
        (x : G) ∈ Q := by
      intro x
      constructor
      · intro hx
        rw [← hQEm]
        exact ⟨x, hx, rfl⟩
      · intro hx
        rw [← hQEm] at hx
        obtain ⟨y, hy, heq⟩ := hx
        have hyx : y = x := Pstar.subtype_injective heq
        exact hyx ▸ hy
    rw [hmem, hmem]
    exact hh

end Stellmacher.SectionFour
