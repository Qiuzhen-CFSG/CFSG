module

public import Stellmacher.SectionOne.SmallMProof.QuotientAction
public import Stellmacher.SectionOne.SmallMProof.LocalKernel
public import Stellmacher.SectionOne.SmallMProof.LocalCores

/-!
# Standing hypotheses and Sylow subgroups in the local group

Subgroups and quotient images retain elementary abelianness. The local quotient is solvable, of even order, faithful on the fixed module and has trivial two-core; the original Sylow subgroup induces its Sylow two-subgroup.

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

public theorem isElementaryAbelian_of_le
    {G : Type u} [Group G] {S A : Subgroup G}
    (hS : IsElementaryAbelian 2 S) (hA : A ≤ S) :
    IsElementaryAbelian 2 A := by
  let : IsElementaryAbelian 2 S := hS
  refine {
    toIsMulCommutative := {
      is_comm := ⟨?_⟩ }
    exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm
        ⟨a, hA a.property⟩ ⟨b, hA b.property⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro a
    apply Subtype.ext
    have ha := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S)
      (⟨a, hA a.property⟩ : S)
    simpa using congrArg Subtype.val ha

public theorem local_quotient_hypotheses
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S A : Subgroup G)
    (hS_elem : IsElementaryAbelian 2 S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2)
    (hScard : 4 ≤ Nat.card S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    let _ : A_H.Normal := local_A_normal S A hS_elem hAmax.1
    let V_A := FixedPoints.subgroup A_H V
    let _ : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
    Hypotheses (H ⧸ A_H) V_A := by
  classical
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  let : A_H.Normal := local_A_normal S A hS_elem hAmax.1
  let V_A := FixedPoints.subgroup A_H V
  let : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  have hAlt : A < S := by
    refine lt_of_le_of_ne hAmax.1 ?_
    intro hEq
    rw [hEq] at hAcard
    omega
  obtain ⟨s, hsS, hsA⟩ := SetLike.exists_of_lt hAlt
  let sH : H := ⟨s, (show S ≤ H from le_sup_right) hsS⟩
  have hsHnotA : sH ∉ A_H := hsA
  have hs2 : s ^ 2 = 1 := by
    let : IsElementaryAbelian 2 S := hS_elem
    exact elemPow_eq_one_of_isElementaryAbelian s hsS
  have hsH2 : sH ^ 2 = 1 := by
    apply Subtype.ext
    exact hs2
  let sbar : H ⧸ A_H := QuotientGroup.mk' A_H sH
  have hsbar_ne : sbar ≠ 1 := by
    intro hsbar
    exact hsHnotA ((QuotientGroup.eq_one_iff sH).mp hsbar)
  have hsbar2 : sbar ^ 2 = 1 := by
    simpa [sbar] using congrArg (QuotientGroup.mk' A_H) hsH2
  have hsbar_order : orderOf sbar = 2 := orderOf_eq_prime hsbar2 hsbar_ne
  have hquot_even : Even (Nat.card (H ⧸ A_H)) := by
    rw [even_iff_two_dvd, ← hsbar_order]
    exact orderOf_dvd_natCard sbar
  let : Group.IsSolvable G := h.G_solvable
  exact {
    G_solvable := inferInstance
    G_even := hquot_even
    action_faithful := local_quotient_action_faithful h S A hS_elem hAmax
      (isElementaryAbelian_of_le hS_elem hAmax.1)
    twoCore_eq_bot := local_quotient_pCore_eq_bot S A hS_elem hAmax }

public theorem local_sylow_exists
    {G : Type u} [Group G] [Finite G]
    (S A : Subgroup G) (hS_elem : IsElementaryAbelian 2 S) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    ∃ P : Sylow 2 H, (P : Subgroup H) = S.subgroupOf H := by
  classical
  let C_WA := oddCore G ⊓ Subgroup.centralizer (A : Set G)
  let W_A := ⁅C_WA, S⁆
  let H := W_A ⊔ S
  let N : Subgroup H := W_A.subgroupOf H
  let S_H : Subgroup H := S.subgroupOf H
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
  let P : Sylow 2 H := hS_H_p.toSylow (by
    rw [hcompNS.index_eq_card]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hNcop)
  exact ⟨P, rfl⟩

end Stellmacher.SectionOne.SmallMProof
