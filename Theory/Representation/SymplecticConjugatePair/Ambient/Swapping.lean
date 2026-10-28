module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Basic
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.IndexNormal

/-!
# Summand interchange in a binary paired action

An action permuting two nonzero complementary summands has an index-two
summand stabilizer once an interchange occurs. A two-subgroup preserving
the first summand fixes a nonzero vector in it, so a larger subgroup
containing an interchange cannot have the same fixed space.

For an elementary abelian actor containing a swapping involution, the fixed
codimension is at least 4n. An explicit centralizer two-rank bound n+1 then
excludes the actor from the (F−1) inequality. The centralizer bound and the
summand permutation assertion are independent model obligations.

Source: Aschbacher–Smith H.7, printed p.389 of `refs/quasithin.pdf`.
-/

@[expose] public section

namespace SymplecticConjugatePair.Ambient
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F] [Finite F]
variable (ρ : Representation (ZMod 2) G (Space F))

private theorem mem_stabilizer_of_maps (U : Submodule (ZMod 2) (Space F)) (g : G)
    (h : ∀ v ∈ U, ρ g v ∈ U) : g ∈ subspaceStabilizer ρ U := by
  have hle : U.map (ρ g) ≤ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have he : U.map (ρ g) = U := Submodule.eq_of_le_of_finrank_eq hle
    (LinearEquiv.finrank_map_eq (linearAction ρ g) U)
  intro v
  constructor
  · intro hv
    rw [← he] at hv
    obtain ⟨w, hw, hew⟩ := hv
    exact (ρ.apply_bijective g).1 hew ▸ hw
  · exact h v

omit [Finite F] in
lemma swapping_not_mem_stabilizer {s : G} (hs : SwapsSummands ρ s) :
    s ∉ summandStabilizer ρ := by
  intro h
  have hz : firstSummand (F := F) = ⊥ := by
    apply bot_unique
    intro v hv
    have hU := (h v).mpr hv
    have hW := hs.1 v hv
    have he := Submodule.disjoint_def.mp summands_isCompl.disjoint (ρ s v) hU hW
    exact (ρ.apply_bijective s).1 (he.trans (map_zero (ρ s)).symm)
  exact firstSummand_ne_bot hz

lemma summandStabilizer_index_two (hp : PermutesSummands ρ)
    (hs : ∃ s, SwapsSummands ρ s) : (summandStabilizer ρ).index = 2 := by
  obtain ⟨s, hs⟩ := hs
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨s, swapping_not_mem_stabilizer ρ hs, ?_⟩
  intro g
  rcases hp g with hg | hg
  · exact Or.inr hg.1
  · left
    apply mem_stabilizer_of_maps
    intro v hv
    rw [map_mul, Module.End.mul_apply]
    exact hs.2 _ (hg.1 v hv)

omit [Finite F] in
lemma swaps_of_not_mem_stabilizer (hp : PermutesSummands ρ)
    {s : G} (hs : s ∉ summandStabilizer ρ) : SwapsSummands ρ s :=
  (hp s).resolve_left (fun h => hs h.1)

lemma fixedSpace_ne_of_swapping {A B : Subgroup G} (hB : IsPGroup 2 B)
    (hBN : B ≤ summandStabilizer ρ)
    {s : G} (hsA : s ∈ A) (hs : SwapsSummands ρ s) :
    fixedSpace ρ A ≠ fixedSpace ρ B := by
  intro heq
  let U : Subrepresentation (ρ.comp B.subtype) :=
    { toSubmodule := firstSummand
      apply_mem_toSubmodule := fun b v hv => (hBN b.property v).mpr hv }
  let _ : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr firstSummand_ne_bot
  obtain ⟨u, hune, hufix⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector U.toRepresentation hB
  have huB : (u : Space F) ∈ fixedSpace ρ B := by
    intro b
    exact congrArg Subtype.val (hufix b)
  have huA : (u : Space F) ∈ fixedSpace ρ A := heq ▸ huB
  have hsu : ρ s u = u := huA ⟨s, hsA⟩
  have huW : (u : Space F) ∈ secondSummand := hsu ▸ hs.1 u u.property
  apply hune
  apply Subtype.ext
  change (u : Space F) = 0
  exact Submodule.disjoint_def.mp (summands_isCompl (F := F)).disjoint
    (u : Space F) (show (u : Space F) ∈ firstSummand from u.property) huW

omit [Finite F] in
lemma swapping_fixedSpace (s : G) (hs : s^2 = 1) (hswap : SwapsSummands ρ s) :
    fixedSpace ρ (Subgroup.zpowers s) = LinearMap.range (ρ s - LinearMap.id) :=
  swapping_fixedSpace_eq_displacement ρ summands_isCompl s hs hswap.1 hswap.2

lemma swapping_codim {n : ℕ} (hF : Nat.card F = 2^n)
    (s : G) (hs : s^2 = 1) (hswap : SwapsSummands ρ s) :
    fixedCodim ρ (Subgroup.zpowers s) = 4*n :=
  swapping_fixedCodim_of_card ρ hF s hs hswap.1 hswap.2

variable [Finite G]
lemma rank_le_of_centralizer {A : Subgroup G} (hA : IsElementaryTwo A)
    {s : G} (hsA : s ∈ A) {r : ℕ}
    (hc : primeRank 2 (Subgroup.centralizer ({s} : Set G)) ≤ r) : rank A ≤ r := by
  let _ : IsElementaryAbelian 2 A := hA.2
  let C := Subgroup.centralizer ({s} : Set G)
  have hAC : A ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = s := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm (⟨s, hsA⟩ : A) ⟨x, hx⟩)
  let _ : IsElementaryAbelian 2 (A.subgroupOf C) := IsElementaryAbelian.subgroupOf hAC
  have hcard := (primeRank_le_iff_elementary_card_le C).mp hc
    (A.subgroupOf C) inferInstance
  have he : Nat.card (A.subgroupOf C) = Nat.card A := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAC]
  rw [he, hA.card_eq_two_pow_rank] at hcard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard

lemma not_offender_of_swapping {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {A : Subgroup G} (hA : IsElementaryTwo A) {s : G} (hsA : s ∈ A)
    (hswap : SwapsSummands ρ s)
    (hc : primeRank 2 (Subgroup.centralizer ({s} : Set G)) ≤ n+1) :
    rank A + 1 < fixedCodim ρ A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  have hs2 : s^2 = 1 := elemPow_eq_one_of_isElementaryAbelian s hsA
  have hlow : 4*n ≤ fixedCodim ρ A := by
    have hf : fixedSpace ρ A ≤ fixedSpace ρ (Subgroup.zpowers s) := by
      intro v hv a
      exact hv ⟨a, (Subgroup.zpowers_le.mpr hsA) a.property⟩
    have hd := Submodule.finrank_mono hf
    have h1 := fixedCodim_add_finrank ρ A
    have h2 := fixedCodim_add_finrank ρ (Subgroup.zpowers s)
    rw [swapping_codim ρ hF s hs2 hswap] at h2
    omega
  have hr := rank_le_of_centralizer hA hsA hc
  omega
end SymplecticConjugatePair.Ambient
