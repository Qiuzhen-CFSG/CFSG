module

public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupAction.SubgroupConjugation
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Normal odd subgroups and four-groups in involution-centralizer cores

Let K be an odd subgroup normal in C, and let V be a four-subgroup of C.
If V lies in the two-core of each of its nonidentity elements' ambient
centralizers, then K centralizes V. For v in V, normality puts
[C_K(v), O₂(C_G(v)) ∩ C] in K and in a two-group, so it is trivial.
The second group contains V by hypothesis.
The three involution-fixed subgroups generate K by the Klein-four
coprime-action theorem.

This is the normal odd-complement reduction used in Thompson VI, printed
p.630. The required core containments are separate local hypotheses.
-/

namespace Subgroup

/-- A normal odd subgroup centralizes a four-group contained in the two-cores
of the ambient centralizers of its three involutions. -/
public theorem normal_odd_centralizes_four_of_le_involution_cores
    {G : Type*} [Group G] [Finite G]
    (C K V : Subgroup G) [IsKleinFour V]
    (hCN : C ≤ normalizer (K : Set G))
    (hodd : Odd (Nat.card K)) (hVC : V ≤ C)
    (hcore : ∀ v ∈ V, v ≠ 1 →
      V ≤ (pCore 2 (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype) :
    K ≤ centralizer (V : Set G) := by
  let _ : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hfixed (v : G) (hv : v ∈ V) (hv1 : v ≠ 1) :
      K ⊓ centralizer ({v} : Set G) ≤ centralizer (V : Set G) := by
    let H := centralizer ({v} : Set G)
    let R := (pCore 2 H).map H.subtype
    let D := K ⊓ H
    let F := R ⊓ C
    have hRtwo : IsPGroup 2 R := pCore_isPGroup.map H.subtype
    have hHN : H ≤ normalizer (R : Set G) := by
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 H).le_normalizer_map H.subtype
    have hKR : K ⊓ R = ⊥ := by
      obtain ⟨n, hn⟩ := hRtwo.exists_card_eq
      exact (disjoint_of_coprime_natCard (by
        rw [hn]
        exact hodd.coprime_two_right.pow_right n)).eq_bot
    have hDF : ⁅D, F⁆ = ⊥ := by
      apply bot_unique
      rw [← hKR]
      apply le_inf
      · exact (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hCN))
      · rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hHN))
    exact (commutator_eq_bot_iff_le_centralizer.mp hDF).trans
      (centralizer_le (le_inf (hcore v hv hv1) hVC))
  let _ : MulDistribMulAction V K :=
    conjMulDistribMulActionOfLeNormalizer V K (hVC.trans hCN)
  let action : V →* MulAut K := MulDistribMulAction.toMulAut V K
  have square (v : V) : v ^ 2 = 1 := by
    simpa only [IsKleinFour.exponent_two] using Monoid.pow_exponent_eq_one v
  have invol (v : V) : Function.Involutive (action v) := by
    intro k
    change (action v * action v) k = k
    rw [← map_mul, ← pow_two, square v, map_one]
    rfl
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsKleinFour.card_four]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : V)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := V)
    (by simp only [ENat.card_eq_coe_natCard, IsKleinFour.card_four]; decide) 1 a
  have hab : a * b ≠ 1 := by
    intro heq
    apply hba
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using square a)
    exact (eq_inv_of_mul_eq_one_right heq).trans hai
  have hcomm : Commute (action a) (action b) := by
    change action a * action b = action b * action a
    rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := V)).comm a b]
  have fixed_mem (v : V) (hv : v ≠ 1) (k : K) (hk : action v k = k) :
      (k : G) ∈ centralizer (V : Set G) := by
    apply hfixed v v.property (fun heq => hv (Subtype.ext heq))
    refine ⟨k.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hh := congrArg K.subtype hk
    change (v : G) * (k : G) * (v : G)⁻¹ = (k : G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  intro k hk
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ :=
    MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card hodd (action a) (action b)
      (invol a) (invol b) hcomm (⟨k, hk⟩ : K)
  have hz' : action (a * b) z = z := by simpa only [map_mul] using hz
  have heq' := congrArg K.subtype heq
  change k = (x : G) * (y : G) * (z : G) at heq'
  rw [heq']
  exact mul_mem (mul_mem (fixed_mem a ha x hx) (fixed_mem b hb y hy))
    (fixed_mem (a * b) hab z hz')

end Subgroup
