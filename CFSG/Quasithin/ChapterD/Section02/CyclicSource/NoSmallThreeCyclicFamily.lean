module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFamily
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicStructure
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicSupport
public import Theory.GroupTheory.ThreePointActionKernel

/-!
# The small cubic-family reduction in D.2.28–29

Every minimum involution normalizes its cubic three-core commutator,
whose moved space has dimension four. Thus a conjugacy-invariant family
of at most two such subgroups in [O₃,G] consists of normal subgroups and
feeds the proved normal-cubic endpoint. The source SQTK cover and cyclic
local commutators also restrict [O₃,G] to order three or nine; its cubic
case is another direct application of that endpoint.

The remaining order-nine family is the three-point action treated by the
moving branch. Source: Aschbacher–Smith D.2.26–29, pp.191–192.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem CoreHypotheses.smallSupport_fourSpace_in_commutator
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ)
    (hc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    ⁅pCore 3 G,zpowers t⁆ ≤ ⁅pCore 3 G,⊤⁆ ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G,zpowers t⁆) = 4 ∧
      t ∈ normalizer (⁅pCore 3 G,zpowers t⁆ : Subgroup G) := by
  refine ⟨commutator_mono le_rfl le_top,?_,
    normalizer_commutator_ge_right _ _ (mem_zpowers t)⟩
  rcases h.local_threeCore_alternatives hq hfive hNo ht with h3 | h27
  · exact h3.2
  · have hh := h27.2.1
    omega

private theorem smallSupport_nonempty (h : CoreHypotheses ρ) :
    (smallSupportInvolutions ρ).Nonempty := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  refine ⟨t,ht,?_⟩
  change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
  rw [←fixedCodim_zpowers_eq_displacement_rank,he]
  exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le

/-- Every member of a restricted four-space family of size at most two is
normal: each source generator normalizes its own local commutator. -/
theorem CoreHypotheses.small_fourSpace_family_normal
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hcard : Nat.card {D : Subgroup G | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4} ≤ 2) :
    ∀ D : Subgroup G, D ≤ ⁅pCore 3 G,⊤⁆ → Nat.card D = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4 → D.Normal := by
  let S : Set (Subgroup G) := {D | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4}
  have hn := normal_of_small_conjugacy_family S (by
    intro D hD g
    have hY : D ∈ fourSpaceThreeFactors ρ :=
      ⟨hD.1.trans (commutator_le_left _ _),hD.2⟩
    exact ⟨(map_mono hD.1).trans_eq (Normal.map_conj_eq _ g),
      (fourSpaceThreeFactors_conjugate ρ hY g).2⟩)
    hcard (smallSupportInvolutions ρ) h.smallSupport_generated (by
      intro t ht
      have hf := h.smallSupport_fourSpace_in_commutator hq hfive hNo t ht (hcyc t ht)
      exact ⟨⁅pCore 3 G,zpowers t⁆,⟨hf.1,hcyc t ht,hf.2.1⟩,hf.2.2⟩)
  exact fun D hDE hD hW => hn D ⟨hDE,hD,hW⟩

/-- The source no-small-three cyclic branch is finished when its family of
four-space cubic actors in [O₃,G] has at most two members. -/
theorem Hypotheses.small_fourSpace_family_localGeneration
    (h : Hypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hcard : Nat.card {D : Subgroup G | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4} ≤ 2) :
    Nonempty (LocalGeneration ρ) := by
  obtain ⟨t,ht⟩ := smallSupport_nonempty h.toCoreHypotheses
  have hf := h.toCoreHypotheses.smallSupport_fourSpace_in_commutator hq hfive hNo
    t ht (hcyc t ht)
  let D := ⁅pCore 3 G,zpowers t⁆
  let : D.Normal := h.toCoreHypotheses.small_fourSpace_family_normal
    hq hfive hNo hcyc hcard D hf.1 (hcyc t ht) hf.2.1
  exact h.normal_cubic_localGeneration hq hfive hNo hcyc D
    (commutator_le_left _ _) (hcyc t ht) hf.2.1

/-- The original cyclic local branch leaves only a cubic or an order-nine
global commutator. -/
theorem CoreHypotheses.threeCore_commutator_card_three_or_nine
    (h : CoreHypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G) = 3 ∨
      Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G) = 9 := by
  have hb := (h.threeCore_commutator_le_omega_of_cyclic hH f honto hfive hcyc).2
  have hp : IsPGroup 3 (⁅pCore 3 G,⊤⁆ : Subgroup G) :=
    pCore_isPGroup.to_le (commutator_le_left _ _)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  obtain ⟨t,ht⟩ := smallSupport_nonempty h
  have hle := card_le_of_le (show ⁅pCore 3 G,zpowers t⁆ ≤ ⁅pCore 3 G,⊤⁆ from
    commutator_mono le_rfl le_top)
  rw [hcyc t ht,hn] at hle
  have hnle : n ≤ 2 := by
    by_contra hh
    have hlo : 27 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ (3 : ℕ)) (by omega : 3 ≤ n)
    rw [hn] at hb
    omega
  interval_cases n
  · norm_num at hle
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (by simpa using hn)

/-- A cubic global commutator is the required normal four-space actor. -/
theorem Hypotheses.threeCore_commutator_cubic_localGeneration
    (h : Hypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hc : Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G) = 3) :
    Nonempty (LocalGeneration ρ) := by
  obtain ⟨t,ht⟩ := smallSupport_nonempty h.toCoreHypotheses
  have hf := h.toCoreHypotheses.smallSupport_fourSpace_in_commutator hq hfive hNo
    t ht (hcyc t ht)
  have he : ⁅pCore 3 G,zpowers t⁆ = ⁅pCore 3 G,⊤⁆ :=
    eq_of_le_of_card_ge hf.1 (by rw [hcyc t ht,hc])
  apply h.normal_cubic_localGeneration hq hfive hNo hcyc ⁅pCore 3 G,⊤⁆
    (commutator_le_left _ _) hc
  exact he ▸ hf.2.1

end CFSG.Quasithin.ChapterD.CyclicSource
