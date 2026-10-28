module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
public import Theory.GroupTheory.CubicCommutatorCyclicFixed

/-!
# The abelian three-core in the cyclic local-commutator branch

The original SQTK cover gives cyclic involution centralizers in O₃. When
each small-support involution has a cubic three-core commutator, coprime
decomposition makes O₃ abelian of rank at most two. The original generating
family then makes [O₃,G] elementary abelian, contained in Ω₁(O₃), of order
at most nine. All groups and inclusions are those of the source actor.

Source: Aschbacher–Smith D.2.26–29, printed pp.191–192. These group-theoretic
consequences do not require an additional module or ratio-two assumption.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The cyclic local alternative makes the original three-core abelian and its global commutator elementary. -/
theorem CoreHypotheses.threeCore_structure_of_cyclic_commutators (h : CoreHypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    IsMulCommutative (pCore 3 G) ∧ primeRank 3 (pCore 3 G) ≤ 2 ∧
      IsElementaryAbelian 3 (⁅pCore 3 G,⊤⁆ : Subgroup G) := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  have hsmall : t ∈ smallSupportInvolutions ρ := by
    refine ⟨ht,?_⟩
    change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
    rw [←fixedCodim_zpowers_eq_displacement_rank,he]
    have hd := (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le
    exact_mod_cast hd
  have hstruct := threeGroup_structure_of_cubic_commutator_cyclic_fixed
    (pCore 3 G) pCore_isPGroup t ht (by rw [normalizer_eq_top]; exact mem_top _)
    (hcyc t hsmall) (h.involution_threeCore_centralizer_cyclic hH f honto hfive t ht)
  let : IsMulCommutative (pCore 3 G) := hstruct.1
  exact ⟨hstruct.1,hstruct.2.2.2.2,
    commutator_elementary_of_generated_cubic (pCore 3 G) (smallSupportInvolutions ρ)
      h.smallSupport_generated hcyc⟩

/-- Each selected involution gives the literal disjoint central displacement and fixed factors. -/
theorem CoreHypotheses.smallSupport_threeCore_split (h : CoreHypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    {t : G} (ht : t ∈ smallSupportInvolutions ρ)
    (hcyc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    pCore 3 G = ⁅pCore 3 G,zpowers t⁆ ⊔ (pCore 3 G ⊓ centralizer ({t} : Set G)) ∧
    Disjoint ⁅pCore 3 G,zpowers t⁆ (pCore 3 G ⊓ centralizer ({t} : Set G)) ∧
    ⁅pCore 3 G,zpowers t⁆ ≤ centralizer (pCore 3 G : Set G) := by
  have hs := threeGroup_structure_of_cubic_commutator_cyclic_fixed
    (pCore 3 G) pCore_isPGroup t ht.1 (by rw [normalizer_eq_top]; exact mem_top _)
    hcyc (h.involution_threeCore_centralizer_cyclic hH f honto hfive t ht.1)
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1⟩

/-- The actual global commutator lies in the elementary omega subgroup and has order at most nine. -/
theorem CoreHypotheses.threeCore_commutator_le_omega_of_cyclic (h : CoreHypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    ⁅pCore 3 G,⊤⁆ ≤ (omega₁ (pCore 3 G) (p := 3)).map (pCore 3 G).subtype ∧
      Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G) ≤ 9 := by
  have hs := h.threeCore_structure_of_cyclic_commutators hH f honto hfive hcyc
  let D : Subgroup G := ⁅pCore 3 G,⊤⁆
  have hD : D ≤ pCore 3 G := commutator_le_left _ _
  let : IsElementaryAbelian 3 D := hs.2.2
  let : IsElementaryAbelian 3 (D.subgroupOf (pCore 3 G)) :=
    IsElementaryAbelian.subgroupOf hD
  have he : (D.subgroupOf (pCore 3 G)).map (pCore 3 G).subtype = D := by
    rw [subgroupOf_map_subtype,inf_eq_left.mpr hD]
  constructor
  · change D ≤ _
    rw [←he]
    exact map_mono elementaryAbelian_le_omega₁
  · have hc := (primeRank_le_iff_elementary_card_le (pCore 3 G)).mp hs.2.1
      (D.subgroupOf (pCore 3 G)) inferInstance
    have hh : Nat.card (D.subgroupOf (pCore 3 G)) = Nat.card D := by
      calc
        _ = Nat.card ((D.subgroupOf (pCore 3 G)).map (pCore 3 G).subtype) :=
          (card_map_of_injective (pCore 3 G).subtype_injective).symm
        _ = Nat.card D := congrArg (fun W : Subgroup G => Nat.card W) he
    change Nat.card D ≤ 9
    simpa only [hh, Nat.reducePow] using hc

end CFSG.Quasithin.ChapterD.CyclicSource
