module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Theory.GroupTheory.PCorePrimeToIndex

/-!
# The local overlap and seed fusion in type HS

The full automorphism action on V is transitive on its seven nonidentity
elements. The marked involution z centralizes V, hence lies in the abelian
normalizer core; its square is one, so the omega calculation places it in V.
Orbit--stabilizer now gives |C_G(z) ∩ N_G(V)| = 1536 and local indices 5 and 7.

A Sylow two-subgroup of that overlap maps to Sylow subgroups of both local
groups, with common ambient image of order 512. These are local Sylow
statements; no ambient Sylow assertion or recognition is assumed. The odd
local indices also place both embedded two-cores in the overlap, the local
arrangement needed before constructing the L₃(4) subgroup.

Source: Aschbacher--Smith, the exact HS1--HS2 hypotheses preceding I.4.8,
printed p.418. The linear transport and counting arguments here are direct
consequences of those hypotheses.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem elementary_aut_transitive {E : Type*} [Group E]
    [IsElementaryAbelian 2 E] (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul x) hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul y) hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨MulEquiv.toAdditive.symm g.toAddEquiv, ?_⟩
  have hh := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
  have hxy : g (Additive.ofMul x) = Additive.ofMul y := by
    change (1 : ZMod 2) • Additive.ofMul y = g ((1 : ZMod 2) • Additive.ofMul x) at hh
    simpa only [one_smul] using hh.symm
  exact congrArg Additive.toMul hxy

/-- The actual seed normalizer fuses any two nonidentity seed elements. -/
theorem TypeAt.seed_transitive (h : TypeAt z V) (x y : V) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : normalizer (V : Set G), g • x = y := by
  let := h.elementary
  obtain ⟨a, ha⟩ := elementary_aut_transitive x y hx hy
  obtain ⟨g, hg⟩ := h.seed_action_surjective a
  exact ⟨g, (congrArg (fun f : MulAut V => f x) hg).trans ha⟩

/-- The marked centralizer involution belongs to the original seed. -/
theorem TypeAt.involution_mem_seed (h : TypeAt z V) : z ∈ V := by
  have hzC : z ∈ centralizer (V : Set G) := by
    intro v hv
    obtain ⟨q, _, he⟩ := h.seed_le_core hv
    rw [← he]
    exact mem_centralizer_singleton_iff.mp q.property
  rw [h.seed_centralizer] at hzC
  obtain ⟨r, hr, he⟩ := hzC
  change (r : G) = z at he
  have hr2 : (⟨r, hr⟩ : pCore 2 (normalizer (V : Set G))) ^ (2^1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) ^ 2 = 1
    rw [he, ← h.involution]
    exact pow_orderOf_eq_one z
  have hw : r ∈ V.subgroupOf (normalizer (V : Set G)) := by
    rw [h.seed_eq_omega_normalizer_core]
    exact ⟨⟨r, hr⟩, subset_closure hr2, rfl⟩
  exact he ▸ (show (r : G) ∈ V from hw)

/-- Every nontrivial seed orbit consists of all seven nonidentity elements. -/
theorem TypeAt.seed_orbit (h : TypeAt z V) (x : V) (hx : x ≠ 1) :
    MulAction.orbit (normalizer (V : Set G)) x = {y : V | y ≠ 1} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩ he
    apply hx
    exact (V.normalizerMonoidHom g).injective
      (he.trans (V.normalizerMonoidHom g).map_one.symm)
  · exact fun hy => h.seed_transitive x y hx hy

/-- The nontrivial orbit of the actual normalizer has length seven. -/
theorem TypeAt.seed_orbit_card (h : TypeAt z V) (x : V) (hx : x ≠ 1) :
    Nat.card (MulAction.orbit (normalizer (V : Set G)) x) = 7 := by
  classical
  let := Fintype.ofFinite V
  rw [h.seed_orbit x hx, Nat.card_eq_fintype_card]
  change Fintype.card {y : V // ¬ y = 1} = 7
  rw [Fintype.card_subtype_compl, Fintype.card_unique (α := {y : V // y = 1}),
    ← Nat.card_eq_fintype_card, h.seed_card]

/-- Each seed involution has normalizer-centralizer order 1536. -/
theorem TypeAt.seed_point_centralizer_card (h : TypeAt z V) (x : V) (hx : x ≠ 1) :
    Nat.card ((involutionCentralizer (x : G)).subgroupOf
      (normalizer (V : Set G))) = 1536 := by
  have hs : MulAction.stabilizer (normalizer (V : Set G)) x =
      (involutionCentralizer (x : G)).subgroupOf (normalizer (V : Set G)) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    exact mul_inv_eq_iff_eq_mul
  have hc := (MulAction.stabilizer (normalizer (V : Set G)) x).index_mul_card
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, h.seed_orbit_card x hx,
    hs, h.normalizer_card] at hc
  omega

/-- The literal local groups intersect in a subgroup of order 1536. -/
theorem TypeAt.local_intersection_card (h : TypeAt z V) :
    Nat.card (involutionCentralizer z ⊓ normalizer (V : Set G) : Subgroup G) = 1536 := by
  have hz : (⟨z, h.involution_mem_seed⟩ : V) ≠ 1 := by
    intro he
    have hze := congrArg Subtype.val he
    change z = 1 at hze
    have hh := h.involution
    rw [hze, orderOf_one] at hh
    contradiction
  have hc := h.seed_point_centralizer_card ⟨z, h.involution_mem_seed⟩ hz
  change Nat.card ((involutionCentralizer z).subgroupOf (normalizer (V : Set G))) = 1536 at hc
  rwa [← card_subtype (normalizer (V : Set G))
    ((involutionCentralizer z).subgroupOf (normalizer (V : Set G))),
    subgroupOf_map_subtype] at hc

/-- The overlap has index five in the centralizer and seven in the normalizer. -/
theorem TypeAt.local_intersection_indices (h : TypeAt z V) :
    (involutionCentralizer z ⊓ normalizer (V : Set G)).relIndex
      (involutionCentralizer z) = 5 ∧
    (involutionCentralizer z ⊓ normalizer (V : Set G)).relIndex
      (normalizer (V : Set G)) = 7 := by
  have hH := ((involutionCentralizer z ⊓ normalizer (V : Set G)).subgroupOf
    (involutionCentralizer z)).index_mul_card
  have hM := ((involutionCentralizer z ⊓ normalizer (V : Set G)).subgroupOf
    (normalizer (V : Set G))).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show involutionCentralizer z ⊓
    normalizer (V : Set G) ≤ involutionCentralizer z from inf_le_left)).toEquiv,
    h.local_intersection_card, h.centralizer_card] at hH
  rw [Nat.card_congr (subgroupOfEquivOfLe (show involutionCentralizer z ⊓
    normalizer (V : Set G) ≤ normalizer (V : Set G) from inf_le_right)).toEquiv,
    h.local_intersection_card, h.normalizer_card] at hM
  change (involutionCentralizer z ⊓ normalizer (V : Set G)).relIndex
    (involutionCentralizer z) * 1536 = 7680 at hH
  change (involutionCentralizer z ⊓ normalizer (V : Set G)).relIndex
    (normalizer (V : Set G)) * 1536 = 10752 at hM
  omega

/-- The local groups have compatible Sylow two-subgroups of order 512. -/
theorem TypeAt.exists_common_local_sylow (h : TypeAt z V) :
    ∃ (S : Sylow 2 (involutionCentralizer z))
      (T : Sylow 2 (normalizer (V : Set G))),
      (S : Subgroup (involutionCentralizer z)).map (involutionCentralizer z).subtype =
        (T : Subgroup (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype ∧
      Nat.card S = 512 := by
  let J := involutionCentralizer z ⊓ normalizer (V : Set G)
  let P : Sylow 2 J := Classical.choice inferInstance
  have hc : Nat.card P = 512 := by
    rw [P.card_eq_multiplicity, show Nat.card J = 1536 from h.local_intersection_card]
    decide +kernel
  let jH : J →* involutionCentralizer z := inclusion inf_le_left
  let jM : J →* normalizer (V : Set G) := inclusion inf_le_right
  let S := (P : Subgroup J).map jH
  let T := (P : Subgroup J).map jM
  have hcS : Nat.card S = 512 := (card_map_of_injective (inclusion_injective inf_le_left)).trans hc
  have hcT : Nat.card T = 512 := (card_map_of_injective (inclusion_injective inf_le_right)).trans hc
  have hiS : S.index = 15 := by
    have hh := S.card_mul_index
    rw [hcS, h.centralizer_card] at hh
    omega
  have hiT : T.index = 21 := by
    have hh := T.card_mul_index
    rw [hcT, h.normalizer_card] at hh
    omega
  refine ⟨(P.isPGroup'.map jH).toSylow (by rw [hiS]; decide),
    (P.isPGroup'.map jM).toSylow (by rw [hiT]; decide), ?_, hcS⟩
  change S.map (involutionCentralizer z).subtype = T.map (normalizer (V : Set G)).subtype
  rw [show S = (P : Subgroup J).map jH from rfl,
    show T = (P : Subgroup J).map jM from rfl, map_map, map_map]
  rfl

/-- Both embedded local two-cores lie in the original overlap. -/
theorem TypeAt.local_cores_le_intersection (h : TypeAt z V) :
    (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype ≤
      involutionCentralizer z ⊓ normalizer (V : Set G) ∧
    (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype ≤
      involutionCentralizer z ⊓ normalizer (V : Set G) := by
  constructor
  · let K := (involutionCentralizer z ⊓ normalizer (V : Set G)).subgroupOf
      (involutionCentralizer z)
    have hi : ¬ 2 ∣ K.index := by
      change ¬ 2 ∣ (involutionCentralizer z ⊓ normalizer (V : Set G)).relIndex
        (involutionCentralizer z)
      rw [(h.local_intersection_indices).1]
      decide
    have hle := (pCore_le_map_pCore_of_prime_not_dvd_index K hi).trans (map_subtype_le _)
    rintro x ⟨q, hq, rfl⟩
    exact hle hq
  · intro x hx
    have hc : x ∈ centralizer (V : Set G) := h.seed_centralizer.symm ▸ hx
    exact ⟨mem_centralizer_singleton_iff.mpr (hc z (h.involution_mem_seed)).symm,
      map_subtype_le _ hx⟩

end CFSG.Quasithin.HigmanSims
