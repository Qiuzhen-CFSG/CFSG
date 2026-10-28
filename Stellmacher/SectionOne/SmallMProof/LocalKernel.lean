module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction

/-!
# The kernel of the local fixed-space action

The P-times-Q lemma kills the local odd centralizer. Maximal-offender fixed-space centralizers then identify the whole kernel on C_V(A) with A, making the quotient action faithful.

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

private theorem local_kernel_eq_A
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hA_elem : IsElementaryAbelian 2 A) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAmax.1
    let _ : IsInvariant H V (FixedPoints.subgroup A_H V) :=
      fixedPoints_isInvariant_of_normal A_H
    fixingSubgroup H
        (Set.univ : Set (FixedPoints.subgroup A_H V)) = A_H := by
  classical
  let C_WA := oddCore G ⊓ Subgroup.centralizer (A : Set G)
  let W_A := ⁅C_WA, S⁆
  let H := W_A ⊔ S
  let N : Subgroup H := W_A.subgroupOf H
  let S_H : Subgroup H := S.subgroupOf H
  let A_H : Subgroup H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAmax.1
  let V_A := FixedPoints.subgroup A_H V
  let : IsInvariant H V V_A := fixedPoints_isInvariant_of_normal A_H
  let K : Subgroup H := fixingSubgroup H (Set.univ : Set V_A)
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
  have hNAcard : Nat.card N = Nat.card W_A := by
    exact natCard_subgroupOf_eq W_A H hWAleH
  have hNcop : Nat.Coprime 2 (Nat.card N) := by
    rwa [hNAcard]
  have hS_H_elem : IsElementaryAbelian 2 S_H := by
    let : IsElementaryAbelian 2 S := hS_elem
    exact IsElementaryAbelian.subgroupOf hSleH
  have hS_H_p : IsPGroup 2 S_H := hS_H_elem.isPGroup 2 S_H
  have hS_H_index : ¬ 2 ∣ S_H.index := by
    rw [hcompNS.index_eq_card]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime 2)).1 hNcop
  let S_syl : Sylow 2 H := hS_H_p.toSylow hS_H_index
  have hNKbot : N ⊓ K = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxWA : (x : G) ∈ W_A := hx.1
      have hxFix : (x : G) ∈
          fixingSubgroup G (FixedPoints.subgroup A V : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v hv
        let vA : FixedPoints.subgroup A V := ⟨v, hv⟩
        have hvAH : ∀ a : A_H, (a : H) • v = v := by
          intro a
          exact (FixedPoints.mem_subgroup (M := A) (a := v)).1 hv
            ⟨(a : G), a.property⟩
        let vAH : V_A :=
          ⟨v, (FixedPoints.mem_subgroup (M := A_H) (a := v)).2 hvAH⟩
        have hxv := ((mem_fixingSubgroup_iff H).mp hx.2) vAH (Set.mem_univ vAH)
        exact congrArg (fun z : V_A => (z : V)) hxv
      have hxBot : (x : G) ∈
          W_A ⊓ fixingSubgroup G
            (FixedPoints.subgroup A V : Set V) := ⟨hxWA, hxFix⟩
      have hlocal := local_odd_centralizer_eq_bot_of_p_times_q
        h S A hS_elem hAS hA_elem
      change W_A ⊓ fixingSubgroup G
          (FixedPoints.subgroup A V : Set V) = ⊥ at hlocal
      rw [hlocal] at hxBot
      simpa using hxBot
    · exact bot_le
  have hq_inj : Function.Injective
      ((QuotientGroup.mk' N).domRestrict K) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    exact (Subgroup.subgroupOf_eq_bot).2 (by
      rw [Subgroup.disjoint_def]
      intro x hxN hxK
      have hx : x ∈ N ⊓ K := ⟨hxN, hxK⟩
      rw [hNKbot] at hx
      simpa using hx)
  have hQp : IsPGroup 2 (H ⧸ N) := by
    exact hS_H_p.of_equiv hcompNS.symm.QuotientMulEquiv.symm
  have hKp : IsPGroup 2 K :=
    hQp.of_injective ((QuotientGroup.mk' N).domRestrict K) hq_inj
  let : K.Normal := by
    rw [show K = (MulDistribMulAction.toMulAut H V_A).ker by
      simpa [K] using (fixingSubgroup_univ_eq_ker_toMulAut (G := V_A) (A := H))]
    infer_instance
  have hKleS_H : K ≤ S_H := by
    simpa [S_syl] using hKp.le_sylow_of_normal S_syl
  apply le_antisymm
  · intro x hxK
    have hxS : (x : G) ∈ S := hKleS_H hxK
    have hxFix : (x : G) ∈
        fixingSubgroup G (FixedPoints.subgroup A V : Set V) := by
      rw [mem_fixingSubgroup_iff]
      intro v hv
      let vA : FixedPoints.subgroup A V := ⟨v, hv⟩
      have hvAH : ∀ a : A_H, (a : H) • v = v := by
        intro a
        exact (FixedPoints.mem_subgroup (M := A) (a := v)).1 hv
          ⟨(a : G), a.property⟩
      let vAH : V_A :=
        ⟨v, (FixedPoints.mem_subgroup (M := A_H) (a := v)).2 hvAH⟩
      have hxv := ((mem_fixingSubgroup_iff H).mp hxK) vAH (Set.mem_univ vAH)
      exact congrArg (fun z : V_A => (z : V)) hxv
    have hxInf : (x : G) ∈
        S ⊓ fixingSubgroup G
          (FixedPoints.subgroup A V : Set V) := ⟨hxS, hxFix⟩
    have hAfix := hAmax.2.2.2
    change S ⊓ fixingSubgroup G
        (FixedPoints.subgroup A V : Set V) = A at hAfix
    rw [hAfix] at hxInf
    exact hxInf
  · intro x hxA
    rw [mem_fixingSubgroup_iff]
    intro v _hv
    apply Subtype.ext
    exact (FixedPoints.mem_subgroup (M := A_H) (a := (v : V))).1 v.property
      ⟨x, hxA⟩

public theorem local_quotient_action_faithful
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hA_elem : IsElementaryAbelian 2 A) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAmax.1
    fixingSubgroup (H ⧸ A_H)
        (Set.univ : Set (FixedPoints.subgroup A_H V)) = ⊥ := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAmax.1
  let : IsInvariant H V (FixedPoints.subgroup A_H V) :=
    fixedPoints_isInvariant_of_normal A_H
  apply quotient_fixedPoints_action_faithful_of_kernel_eq A_H
  exact local_kernel_eq_A h S A hS_elem hAmax hA_elem

end Stellmacher.SectionOne.SmallMProof
