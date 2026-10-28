module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.PCoreFrattiniIndex
public import Theory.GroupTheory.PGroup.ExtraspecialCyclicProduct
public import Theory.GroupTheory.InvolutionPowerFusion

/-!
# Weak closure inside a core with large cyclic tail

Suppose the actual odd-core quotient's two-core is a central product of an
extraspecial eight and a cyclic factor of order at least eight. The cyclic
factor is its center. Its Frattini quotient has order at most eight, so the
solvable quotient's faithful Frattini action bounds the core's Sylow index
by two. Hence every Sylow fourth power lies in the cyclic core center.

The central involution has a fourth root in that center, commuting with
every core element. Transporting this root along an ambient conjugacy and
back into the original Sylow subgroup inside the involution centralizer
forces the conjugacy to fix the involution. This proves weak closure in
the core preimage, without an assumed core-order or Sylow-index bound.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.392–393;
`refs/original/n-group-global/odd-core-rank-two-source/normal-four-case-split.md`.
The Frattini calculation supplies the local structure needed for the
source's fourth-power argument. Simplicity, nonsolvability, and the width
exclusion are not needed for this particular implication.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The actual core preimage has cyclic center of the same order as its
nontrivial cyclic Hall factor. -/
public theorem omegaCorePreimage_center_cyclic_tail
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) :
    IsCyclic (center (omegaCorePreimage S)) ∧
      Nat.card (center (omegaCorePreimage S)) = Nat.card D := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  have hcenter := center_eq_cyclic_factor_of_extraspecial_of_cyclic_center
    pCore_isPGroup A D hD hc hgen
  let e := centerCongr (omegaCorePreimageEquiv S)
  refine ⟨e.isCyclic.mpr inferInstance, ?_⟩
  exact (Nat.card_congr e.toEquiv).trans (congrArg (fun U : Subgroup (pCore 2 (OmegaQuotient S)) => Nat.card U) hcenter)

/-- Fourth powers in the cyclic core center suffice for ambient weak closure
of the central involution inside the core preimage. -/
public theorem omegaCorePreimage_weakly_closed_of_cyclic_tail_fourth_powers
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D]
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D)
    (hfourth : ∀ x : S,
      x ^ 4 ∈ (center (omegaCorePreimage S)).map (omegaCorePreimage S).subtype) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  have hD : D ≠ ⊥ := by
    intro heq
    rw [heq, card_bot] at hlarge
    omega
  obtain ⟨hcyc, hcard⟩ :=
    omegaCorePreimage_center_cyclic_tail hrank S E hunique hnormal A D hD hc hgen
  let : IsCyclic (center (omegaCorePreimage S)) := hcyc
  intro z t hzC hz ht hconj
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
    (by simpa only [hz] using pow_orderOf_eq_one z) (center_le_centralizer _ hzC)
  exact S.eq_of_isConj_of_fourth_powers_in_cyclic_center (omegaCorePreimage S)
    (hcard ▸ hlarge) hfourth z hzC hz
    (four_le_omegaCorePreimage hN hrank S hZ E hE hzE) t ht hconj


/-- The extraspecial-eight/cyclic decomposition puts every Sylow fourth
power in the actual core center; the needed index bound is derived. -/
public theorem omegaCorePreimage_fourth_power_mem_center_of_cyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hA : Nat.card A = 8)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) (x : S) :
    x ^ 4 ∈ (center (omegaCorePreimage S)).map (omegaCorePreimage S).subtype := by
  let : Group.IsSolvable (OmegaQuotient S) := omegaQuotient_solvable hN S hZ
  have hdim := card_frattini_quotient_le_eight_of_extraspecial_eight_cyclic
    pCore_isPGroup A D hA hgen
  have hiQ := (omegaQuotientSylow S).relIndex_pCore_le_two_of_frattini_card_le_eight
    (omegaQuotient_centralizer_pCore_le hN S hZ) hdim
  have hi : (omegaCorePreimage S).index ≤ 2 := by
    rwa [index_omegaCorePreimage]
  apply fourth_power_mem_mapped_center_of_index_le_two (omegaCorePreimage S) hi _ x
  intro r
  apply mem_center_iff.mpr
  intro s
  apply (omegaCorePreimageEquiv S).injective
  rw [map_mul, map_mul, map_pow]
  exact mem_center_iff.mp
    (square_mem_center_of_extraspecial_cyclic_product A D hc hgen
      (omegaCorePreimageEquiv S r)) (omegaCorePreimageEquiv S s)

/-- A cyclic tail of order at least eight forces weak closure of the central
Sylow involution in the actual core preimage. No index or core-order bound
is assumed. -/
public theorem omegaCorePreimage_weakly_closed_of_large_cyclic_tail
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] [IsCyclic D] (hA : Nat.card A = 8)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hgen : A ⊔ D = ⊤) (hlarge : 8 ≤ Nat.card D) :
    ∀ z t : S, z ∈ center S → orderOf z = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  apply omegaCorePreimage_weakly_closed_of_cyclic_tail_fourth_powers
    hN hrank S hZ E hE hunique hnormal A D hc hgen hlarge
  intro x
  exact omegaCorePreimage_fourth_power_mem_center_of_cyclic_tail hN S hZ A D hA hc hgen x

end Stellmacher.Recognition.NormalFourCentralOmegaTwo