module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Geometry

/-!
# Intransitive Sylow overgroups in the natural M₂₂ action

A Sylow two-subgroup fixes a hexad, since there are 77 hexads, and contains
its pointwise kernel of order sixteen. The free action of that kernel outside
the hexad gives an orbit of size at least sixteen. An intransitive overgroup
therefore has another orbit of size at most six. Every orbit has even size.
A two-point orbit supplies a preserved pair; a larger small orbit lies in the
hexad and determines it by the Steiner property.

This proves the intransitive part of the geometric coverage needed for
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), using the genuine
degree-22 permutation action and no maximal-subgroup table.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

/-- An odd number of hexads ensures that every Sylow two-subgroup fixes one. -/
theorem sylow_preserves_hexad (U : Sylow 2 M22) :
    ∃ B ∈ m22Blocks, (U : Subgroup M22) ≤ stabilizer M22 B := by
  let A : SubMulAction U (Finset (Fin 22)) :=
    { carrier := (m22Blocks : Set (Finset (Fin 22)))
      smul_mem' := fun g B hB => m22_smul_block_mem g.val B hB }
  have hcard : Nat.card A = 77 := by
    change Nat.card {B // B ∈ m22Blocks} = 77
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, m22Blocks_cardinality]
  obtain ⟨B, hB⟩ := U.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card A
    (by rw [hcard]; decide)
  refine ⟨B.val, B.property, ?_⟩
  intro g hg
  exact congrArg Subtype.val ((mem_fixedPoints.mp hB) (⟨g, hg⟩ : U))

/-- Every orbit of an ambient Sylow overgroup has even length. -/
theorem orbit_card_even (X : Subgroup M22)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) (x : Fin 22) :
    2 ∣ (orbit X x).ncard := by
  let : IsPretransitive M22 (Fin 22) := m22_isPretransitive
  obtain ⟨U, hU⟩ := hU
  have hodd : ¬ 2 ∣ X.index := fun h => U.not_dvd_index
    (h.trans (Subgroup.index_dvd_of_le hU))
  let L := stabilizer M22 x
  have hiL : L.index = 22 := by
    rw [index_stabilizer_of_transitive]
    simp
  have hdvd : 22 ∣ (X ⊓ L).index :=
    by simpa only [hiL] using
      (Subgroup.index_dvd_of_le (show X ⊓ L ≤ L from inf_le_right))
  rw [← Subgroup.relIndex_mul_index (show X ⊓ L ≤ X from inf_le_left),
    Subgroup.inf_relIndex_left] at hdvd
  change 22 ∣ (stabilizer X x).index * X.index at hdvd
  rw [index_stabilizer] at hdvd
  exact ((Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp
    ((by decide : 2 ∣ 22).trans hdvd)).resolve_right hodd


private theorem large_orbit {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hK : m22HexadPointwiseKernel B ≤ X)
    (a : Fin 22) (ha : a ∉ B) : 16 ≤ (orbit X a).ncard := by
  let f : m22HexadPointwiseKernel B → orbit X a := fun u =>
    ⟨u.val • a, mem_orbit a (⟨u.val, hK u.property⟩ : X)⟩
  have hi : Function.Injective f := by
    intro u v he
    have he' : u.val • a = v.val • a := congrArg Subtype.val he
    have hfix : (v.val⁻¹ * u.val) • a = a := by
      rw [mul_smul, he', inv_smul_smul]
    have hmem : v.val⁻¹ * u.val ∈ m22HexadPointwiseKernel B :=
      (m22HexadPointwiseKernel B).mul_mem
        ((m22HexadPointwiseKernel B).inv_mem v.property) u.property
    have hone : v.val⁻¹ * u.val = 1 := by
      by_contra hne
      exact ha ((kernel_fixed_iff hB hmem hne a).mp hfix)
    exact Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hn := Nat.card_le_card_of_injective f hi
  rwa [m22HexadPointwiseKernel_card hB, Nat.card_coe_set_eq] at hn

/-- The intransitive part of geometric coverage uses only the full Sylow subgroup. -/
theorem coverage_of_not_pretransitive (X : Subgroup M22)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X)
    (hnt : ¬ IsPretransitive X (Fin 22)) :
    (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S) := by
  classical
  obtain ⟨U, hUX⟩ := hU
  obtain ⟨B, hB, hUB⟩ := sylow_preserves_hexad U
  have hK : m22HexadPointwiseKernel B ≤ X :=
    (kernel_le_of_sylow hB U hUB).trans hUX
  have hne : B ≠ Finset.univ := by
    intro he
    have hc := m22Block_card B hB
    rw [he] at hc
    norm_num at hc
  obtain ⟨a, ha⟩ := not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hne)
  obtain ⟨b, hb⟩ : ∃ b : Fin 22, b ∉ orbit X a := by
    by_contra! h
    apply hnt
    constructor
    intro x y
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (h x)
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (h y)
    exact ⟨k * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hk]⟩
  have hsub : orbit X b ⊆ (orbit X a)ᶜ := by
    intro z hz hza
    exact hb (orbit_eq_iff.mp ((orbit_eq_iff.mpr hz).symm.trans (orbit_eq_iff.mpr hza)))
  have hsmall : (orbit X b).ncard ≤ 6 := by
    have hl := large_orbit hB X hK a ha
    have hc := Set.ncard_mono hsub
    rw [Set.ncard_compl, Nat.card_fin] at hc
    omega
  let S := (orbit X b).toFinset
  have hcard : S.card = (orbit X b).ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hpos : 0 < S.card := hcard ▸ (Set.ncard_pos).mpr ⟨b, mem_orbit_self b⟩
  have heven : 2 ∣ S.card := hcard ▸ orbit_card_even X ⟨U, hUX⟩ b
  have hXS : X ≤ stabilizer M22 S := by
    intro g hg
    apply mem_stabilizer_finset'.mpr
    intro y hy
    exact Set.mem_toFinset.mpr
      (mem_orbit_of_mem_orbit (⟨g, hg⟩ : X) (Set.mem_toFinset.mp hy))
  by_cases htwo : S.card = 2
  · exact Or.inr ⟨S, htwo, hXS⟩
  left
  have hSB : S ⊆ B := small_invariant_subset_hexad hB S (by omega) (hK.trans hXS)
  refine ⟨B, hB, ?_⟩
  intro g hg
  apply mem_stabilizer_iff.mpr
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 3) (by omega)
  have hgS : g • S = S := hXS hg
  have hSB' : S ⊆ g • B := by
    rw [← hgS]
    exact Finset.smul_finset_subset_smul_finset hSB
  exact m22Blocks_eq_of_common_triple T (g • B) B hT (m22_smul_block_mem g B hB)
    hB (hTS.trans hSB') (hTS.trans hSB)

end Sporadic.Mathieu.M22SolvableSylow
