module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.CoprimeCores

/-!
# The recursive quotient cores

The normal odd complement and elementary Sylow action identify the two-core with A. Passing to the quotient yields trivial two-core and a cardinal-preserving image of the local odd commutator as the full odd core.

The standing Section 1 hypotheses and subgroup/cardinality conditions are
explicit. This is the recursive proof used for the restricted conclusion
`m(S) ≤ 1`; the unrestricted source-facing theorem is not used.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.17–19,
and its offender application in (1.7).
-/

open scoped BigOperators Pointwise commutatorElement

namespace Stellmacher.SectionOne.SmallMProof

universe u

open RankOneThreeGroupAssembly

private theorem local_pCore_eq_A
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S)
    (hAmax : oneAmax (G := G) (V := V) S A) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    pCore 2 H = A_H := by
  classical
  let C_WA := oddCore G ⊓ Subgroup.centralizer (A : Set G)
  let W_A := ⁅C_WA, S⁆
  let H := W_A ⊔ S
  let N : Subgroup H := W_A.subgroupOf H
  let S_H : Subgroup H := S.subgroupOf H
  let A_H : Subgroup H := A.subgroupOf H
  have hAS : A ≤ S := hAmax.1
  have hWAleH : W_A ≤ H := le_sup_left
  have hSleH : S ≤ H := le_sup_right
  have hWAleBig : W_A ≤ C_WA ⊔ S := Subgroup.commutator_le_sup _ _
  have hHleBig : H ≤ C_WA ⊔ S := sup_le hWAleBig le_sup_right
  have hBigNorm := commutator_normal_in_sup C_WA S
  have hWA_normalizer : C_WA ⊔ S ≤ Subgroup.normalizer (W_A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWAleBig).1 hBigNorm
  let : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWAleH).2
      (hHleBig.trans hWA_normalizer)
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  have hWAleOdd : W_A ≤ oddCore G := by
    let : (oddCore G).Normal := pPrimeCore_normal
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.commutator_le_left (oddCore G) S)
  have hWAcop : Nat.Coprime 2 (Nat.card W_A) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hWAleOdd)
      pPrimeCore_coprime_card
  obtain ⟨n, hScard⟩ := hS_elem.isPGroup 2 S |>.exists_card_eq
  have hWAScop : Nat.Coprime (Nat.card W_A) (Nat.card S) := by
    rw [hScard]
    exact hWAcop.symm.pow_right n
  have hdisjWAS : Disjoint W_A S :=
    Subgroup.disjoint_of_coprime_natCard hWAScop
  have hdisjNS : Disjoint N S_H := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxS
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisjWAS hxN hxS
  have hcodNS : N ⊔ S_H = ⊤ := by
    simpa [N, S_H, H] using
      (Subgroup.codisjoint_subgroupOf_sup W_A S).eq_top
  have hcompNS : N.IsComplement' S_H := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjNS
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ N ⊔ S_H := by rw [hcodNS]; trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := S_H)).1 hx with
      ⟨n, hn, s, hs, hns⟩
    exact ⟨n, hn, s, hs, hns⟩
  have hNcard : Nat.card N = Nat.card W_A :=
    natCard_subgroupOf_eq W_A H hWAleH
  have hNcop : Nat.Coprime 2 (Nat.card N) := by rwa [hNcard]
  have hS_H_elem : IsElementaryAbelian 2 S_H := by
    let : IsElementaryAbelian 2 S := hS_elem
    exact IsElementaryAbelian.subgroupOf hSleH
  have hS_H_p : IsPGroup 2 S_H := hS_H_elem.isPGroup 2 S_H
  have hScentA : S ≤ Subgroup.centralizer (A : Set G) := by
    let : IsElementaryAbelian 2 S := hS_elem
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm
        ⟨s, hs⟩ ⟨a, hAS ha⟩)).symm
  have hSnormalA : S ≤ Subgroup.normalizer (A : Set G) :=
    hScentA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hSnormInf : S ⊓ Subgroup.normalizer (A : Set G) = S :=
    inf_eq_left.2 hSnormalA
  have hcentAmbient : S ⊓ Subgroup.centralizer (W_A : Set G) = A := by
    have hthird := hAmax.2.2.1
    change S ⊓ Subgroup.centralizer
      ((⁅C_WA, S ⊓ Subgroup.normalizer (A : Set G)⁆ : Subgroup G) : Set G) = A at hthird
    simpa [W_A, hSnormInf] using hthird
  have hcentLocal : S_H ⊓ Subgroup.centralizer (N : Set H) = A_H := by
    ext x
    constructor
    · rintro ⟨hxS, hxC⟩
      have hxCG : (x : G) ∈ Subgroup.centralizer (W_A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        let wN : N := ⟨⟨w, hWAleH hw⟩, hw⟩
        have hxComm := (Subgroup.mem_centralizer_iff.mp hxC) wN wN.property
        exact congrArg Subtype.val hxComm
      have hxInf : (x : G) ∈ S ⊓ Subgroup.centralizer (W_A : Set G) :=
        ⟨hxS, hxCG⟩
      rwa [hcentAmbient] at hxInf
    · intro hxA
      have hxAamb : (x : G) ∈ A := hxA
      have hxInf : (x : G) ∈ S ⊓ Subgroup.centralizer (W_A : Set G) := by
        rw [hcentAmbient]
        exact hxAamb
      refine ⟨hxInf.1, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro w hw
      have hcommG := (Subgroup.mem_centralizer_iff.mp hxInf.2) (w : G) hw
      exact Subtype.ext hcommG
  exact pCore_eq_of_normal_coprime_complement
    N S_H A_H hcompNS hS_H_p hNcop
      (fun x hx => hAS hx) hcentLocal

public theorem local_quotient_pCore_eq_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S)
    (hAmax : oneAmax (G := G) (V := V) S A) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAmax.1
    pCore 2 (H ⧸ A_H) = ⊥ := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAmax.1
  have hcore : pCore 2 H = A_H :=
    local_pCore_eq_A S A hS_elem hAmax
  have hA_p : IsPGroup 2 A_H := by
    let : IsElementaryAbelian 2 S := hS_elem
    have hS_H_elem : IsElementaryAbelian 2 (S.subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (show S ≤ H from le_sup_right)
    have hA_H_le : A_H ≤ S.subgroupOf H := fun x hx => hAmax.1 hx
    exact (hS_H_elem.isPGroup 2 (S.subgroupOf H)).to_le hA_H_le
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := H) (p := 2) A_H hA_p
  calc
    pCore 2 (H ⧸ A_H) = A_H.map (QuotientGroup.mk' A_H) := by
      rw [← hmap, hcore]
    _ = ⊥ := QuotientGroup.map_mk'_self (N := A_H)

public theorem local_quotient_oddCore_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S) (hAS : A ≤ S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let S_H := S.subgroupOf H
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAS
    let Pbar := S_H.map (QuotientGroup.mk' A_H)
    oddCore (H ⧸ A_H) =
        (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
      Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
        Nat.card W_A ∧
      oddCore (H ⧸ A_H) = ⁅oddCore (H ⧸ A_H), Pbar⁆ := by
  classical
  let C_WA := oddCore G ⊓ Subgroup.centralizer (A : Set G)
  let W_A := ⁅C_WA, S⁆
  let H := W_A ⊔ S
  let N : Subgroup H := W_A.subgroupOf H
  let S_H : Subgroup H := S.subgroupOf H
  let A_H : Subgroup H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAS
  let q : H →* H ⧸ A_H := QuotientGroup.mk' A_H
  let Pbar := S_H.map q
  have hWAleH : W_A ≤ H := le_sup_left
  have hSleH : S ≤ H := le_sup_right
  have hWAleBig : W_A ≤ C_WA ⊔ S := Subgroup.commutator_le_sup _ _
  have hHleBig : H ≤ C_WA ⊔ S := sup_le hWAleBig le_sup_right
  have hBigNorm := commutator_normal_in_sup C_WA S
  have hWA_normalizer : C_WA ⊔ S ≤ Subgroup.normalizer (W_A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWAleBig).1 hBigNorm
  let : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWAleH).2
      (hHleBig.trans hWA_normalizer)
  have hWAleOdd : W_A ≤ oddCore G := by
    let : (oddCore G).Normal := pPrimeCore_normal
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.commutator_le_left (oddCore G) S)
  have hWAcop : Nat.Coprime 2 (Nat.card W_A) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hWAleOdd)
      pPrimeCore_coprime_card
  obtain ⟨n, hScard⟩ := hS_elem.isPGroup 2 S |>.exists_card_eq
  have hWAScop : Nat.Coprime (Nat.card W_A) (Nat.card S) := by
    rw [hScard]
    exact hWAcop.symm.pow_right n
  have hdisjWAS : Disjoint W_A S :=
    Subgroup.disjoint_of_coprime_natCard hWAScop
  have hdisjNS : Disjoint N S_H := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxS
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisjWAS hxN hxS
  have hcodNS : N ⊔ S_H = ⊤ := by
    simpa [N, S_H, H] using
      (Subgroup.codisjoint_subgroupOf_sup W_A S).eq_top
  have hcompNS : N.IsComplement' S_H := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjNS
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ N ⊔ S_H := by rw [hcodNS]; trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := N) (t := S_H)).1 hx with
      ⟨n, hn, s, hs, hns⟩
    exact ⟨n, hn, s, hs, hns⟩
  have hNcard : Nat.card N = Nat.card W_A :=
    natCard_subgroupOf_eq W_A H hWAleH
  have hNcop : Nat.Coprime 2 (Nat.card N) := by rwa [hNcard]
  have hS_H_elem : IsElementaryAbelian 2 S_H := by
    let : IsElementaryAbelian 2 S := hS_elem
    exact IsElementaryAbelian.subgroupOf hSleH
  have hS_H_p : IsPGroup 2 S_H := hS_H_elem.isPGroup 2 S_H
  have hScentA : S ≤ Subgroup.centralizer (A : Set G) := by
    let : IsElementaryAbelian 2 S := hS_elem
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm
        ⟨s, hs⟩ ⟨a, hAS ha⟩)).symm
  have hSnormalA : S ≤ Subgroup.normalizer (A : Set G) :=
    hScentA.trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hNormalizerA_normalizes_cent :
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).1 inferInstance
  let : (oddCore G).Normal := pPrimeCore_normal
  have hSnormC : S ≤ Subgroup.normalizer (C_WA : Set G) := by
    refine (le_inf
      (Subgroup.le_normalizer_of_normal (H := oddCore G))
      (hSnormalA.trans hNormalizerA_normalizes_cent)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable G := h.G_solvable
  have hCsolv : Group.IsSolvable C_WA := inferInstance
  have hCcop2 : Nat.Coprime 2 (Nat.card C_WA) :=
    Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (show C_WA ≤ oddCore G from inf_le_left))
      pPrimeCore_coprime_card
  have hSCcop : Nat.Coprime (Nat.card S) (Nat.card C_WA) := by
    rw [hScard]
    exact hCcop2.pow_left n
  have hWidem : ⁅W_A, S⁆ = W_A := by
    exact commutator_idempotent_of_solvable_coprime C_WA S hSnormC hCsolv hSCcop
  have hNSidem : ⁅N, S_H⁆ = N := by
    apply Subgroup.map_injective H.subtype_injective
    rw [commutator_subgroupOf_map_eq H S W_A hSleH hWAleH]
    rw [Subgroup.map_subgroupOf_eq_of_le hWAleH, hWidem]
  have hcore : oddCore (H ⧸ A_H) = N.map q := by
    exact pPrimeCore_quotient_eq_map_of_normal_coprime_complement
      N S_H A_H (fun x hx => hAS hx) hcompNS hS_H_p hNcop
  have hmapcard : Nat.card (N.map q) = Nat.card W_A := by
    rw [natCard_map_mk'_eq_of_le_isComplement' S_H N A_H
      (fun x hx => hAS hx) hcompNS.symm, hNcard]
  refine ⟨hcore, hmapcard, ?_⟩
  change oddCore (H ⧸ A_H) = ⁅oddCore (H ⧸ A_H), Pbar⁆
  rw [hcore]
  rw [← Subgroup.map_commutator, hNSidem]

end Stellmacher.SectionOne.SmallMProof
