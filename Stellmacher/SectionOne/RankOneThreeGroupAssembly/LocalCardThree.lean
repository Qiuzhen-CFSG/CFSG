module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalLifts
public import Stellmacher.SectionOne.SmallMProof.CoprimeCores

/-!
# Local commutators for an elementary actor of order four

When the actor `S` has order four, the recursive local hypothesis forces
each maximal-offender local commutator `[C_W(A),S]` to have order three.
The quotient's factor family cannot be empty, since that would make the
image of `S` in `S/A` trivial. A lifted factor has a coordinate of order
four inside `S`, hence that coordinate equals `S`. Its coordinate
commutator is therefore the whole local commutator, by coprime
commutator idempotence.

This gives the local cyclic groups used to centralize the odd action
kernel in Stellmacher (1.6), journal p.18. The only recursion used is the
explicit proved local-data interface, not the unrestricted source theorem.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u

public theorem local_commutator_card_three_of_card_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Subgroup G)
    (hS : IsElementaryAbelian 2 S) (hScard : Nat.card S = 4)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) S)
    (A : Subgroup G) (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2) :
    Nat.card (⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ : Subgroup G) = 3 := by
  classical
  let C := oddCore G ⊓ Subgroup.centralizer (A : Set G)
  let W_A := ⁅C, S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  obtain ⟨hA_H, P, Fs, hP, _, _, hFs, hprod, _, hlift⟩ :=
    local_hypothesis_gives_derived_factor_lifts S A hlocal hAmax hAcard
  let _ : A_H.Normal := hA_H
  have hFsnonempty : Fs.Nonempty := by
    by_contra hnone
    have hFsempty := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hPbot : (P : Subgroup (H ⧸ A_H)) = ⊥ := by
      apply le_antisymm _ bot_le
      have hp := hprod.1
      rw [hFsempty] at hp
      simp only [iSup_of_empty] at hp
      simpa using (le_sup_right : (P : Subgroup (H ⧸ A_H)) ≤
        oddCore (H ⧸ A_H) ⊔ (P : Subgroup (H ⧸ A_H))) |>.trans hp.le
    have hSker : S.subgroupOf H ≤ (QuotientGroup.mk' A_H).ker :=
      (Subgroup.map_eq_bot_iff (H := S.subgroupOf H)).mp (hP.symm.trans hPbot)
    have hSA : S ≤ A := by
      intro s hs
      have hsH : (⟨s, (le_sup_right : S ≤ H) hs⟩ : H) ∈ S.subgroupOf H := hs
      have ha := hSker hsH
      rw [QuotientGroup.ker_mk'] at ha
      exact ha
    have hcard := Subgroup.card_le_of_le hSA
    rw [hScard, hAcard] at hcard
    omega
  obtain ⟨E, hE⟩ := hFsnonempty
  obtain ⟨F, _, _, _, hFcard, _, _, I, _, hIS, hIcard,
    _, _, _, _, _, hcomm, _⟩ := hlift E hE
  have hIeq : I = S := Subgroup.eq_of_le_of_card_ge hIS (by rw [hIcard, hScard])
  have hSnormC : S ≤ Subgroup.normalizer (C : Set G) := by
    let _ : IsMulCommutative S := hS.toIsMulCommutative
    have hSnormA : S ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAmax.1).mp inferInstance
    have hnormCent : Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (A : Set G))).mp inferInstance
    let _ : (oddCore G).Normal := pPrimeCore_normal
    exact (le_inf Subgroup.le_normalizer_of_normal (hSnormA.trans hnormCent)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCodd : Nat.Coprime 2 (Nat.card C) :=
    (pPrimeCore_coprime_card (G := G) (p := 2)).of_dvd_right
      (Subgroup.card_dvd_of_le (show C ≤ oddCore G from inf_le_left))
  have hcop : Nat.Coprime (Nat.card S) (Nat.card C) := by
    rw [hScard]
    exact hCodd.pow_left 2
  let _ : Group.IsSolvable G := h.G_solvable
  have hidem : ⁅W_A, S⁆ = W_A :=
    SmallMProof.commutator_idempotent_of_solvable_coprime C S hSnormC inferInstance hcop
  change ⁅W_A, I⁆ = F at hcomm
  rw [hIeq, hidem] at hcomm
  change Nat.card W_A = 3
  rw [hcomm]
  exact hFcard

end Stellmacher.SectionOne.RankOneThreeGroupAssembly

