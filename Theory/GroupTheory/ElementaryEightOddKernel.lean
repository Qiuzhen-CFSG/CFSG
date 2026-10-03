module

public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupAction.SubgroupConjugation

/-!
# Absorbing an odd kernel through elementary-eight centralizers

Suppose an elementary abelian group E of order eight normalizes an odd-order
subgroup N. If M contains the ambient centralizer of every four-subgroup of E,
then N lies in M. In particular this applies to an odd normal kernel N.

Use the intrinsic conjugation action of E on N. Coprime fixed-point generation
expresses N as the join of fixed subgroups for actor subgroups Y with cyclic
quotient. Such a quotient has order at most two, so Y has order at least four
and contains a four-subgroup V. Its fixed subgroup centralizes V and hence
lies in M.

This is the rank-three odd-kernel absorption argument in the local analysis
of Thompson N-groups; the fixed-generation input is the source-neutral form
of Feit–Thompson background Proposition (1.16)(b).
-/

namespace Subgroup

/-- Centralizers of the fours of an elementary eight absorb every odd subgroup
normalized by that eight. -/
public theorem le_of_odd_normalized_by_elementary_eight
    {G : Type*} [Group G] [Finite G] (N E M : Subgroup G)
    (hEN : E ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N))
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 8)
    (hcentral : ∀ V : Subgroup G, V ≤ E → IsElementaryAbelian 2 V →
      Nat.card V = 4 → centralizer (V : Set G) ≤ M) : N ≤ M := by
  let _ : IsElementaryAbelian 2 E := hE
  let _ : CommGroup E := IsMulCommutative.instCommGroup
  let _ : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  let _ : MulDistribMulAction E N := conjMulDistribMulActionOfLeNormalizer E N hEN
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := N) (A := E) 2 hodd.coprime_two_left
  have htop : (⊤ : Subgroup N) ≤ M.comap N.subtype := by
    rw [← hgen]
    refine iSup₂_le fun Y hY => ?_
    have hquot : Nat.card (E ⧸ Y) ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      rw [← hY.exponent_eq_card]
      exact (Group.exponent_quotient_dvd Y).trans
        (IsElementaryAbelian.exponent_dvd_p 2 E)
    have hlarge : 2 ^ 2 ≤ Nat.card Y := by
      have hprod := card_eq_card_quotient_mul_card_subgroup Y
      rw [hcard] at hprod
      nlinarith
    obtain ⟨D, hDY, hDcard⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      Nat.prime_two (IsElementaryAbelian.isPGroup 2 E) hlarge
    let _ : IsElementaryAbelian 2 D := {
      exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
        (IsElementaryAbelian.exponent_dvd_p 2 E) }
    have hVelem : IsElementaryAbelian 2 (D.map E.subtype) := IsElementaryAbelian.map_subtype
    have hVcard : Nat.card (D.map E.subtype) = 4 := by
      rw [card_map_of_injective E.subtype_injective, hDcard]
      norm_num
    intro x hx
    apply hcentral (D.map E.subtype) (map_subtype_le D) hVelem hVcard
    apply mem_centralizer_iff.mpr
    rintro v ⟨d, hd, rfl⟩
    have hfix := congrArg Subtype.val (hx (⟨d, hDY hd⟩ : Y))
    change (d : G) * (x : G) * (d : G)⁻¹ = (x : G) at hfix
    exact (mul_inv_eq_iff_eq_mul).mp hfix
  intro x hx
  exact htop (mem_top (⟨x, hx⟩ : N))

/-- An odd normal kernel is contained in any subgroup containing the centralizers
of all four-subgroups of an elementary eight. -/
public theorem le_of_odd_normal_elementary_eight_centralizers
    {G : Type*} [Group G] [Finite G] (N E M : Subgroup G) [N.Normal]
    (hodd : Odd (Nat.card N)) (hE : IsElementaryAbelian 2 E)
    (hcard : Nat.card E = 8)
    (hcentral : ∀ V : Subgroup G, V ≤ E → IsElementaryAbelian 2 V →
      Nat.card V = 4 → centralizer (V : Set G) ≤ M) : N ≤ M :=
  le_of_odd_normalized_by_elementary_eight N E M (le_normalizer_of_normal (H := N))
    hodd hE hcard hcentral

end Subgroup
