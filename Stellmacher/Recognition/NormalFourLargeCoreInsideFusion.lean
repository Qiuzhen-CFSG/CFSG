module

public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Theory.GroupTheory.NormalFourExtraspecialCyclicFusion

/-!
# Excluding fusion into the extraspecial core of order thirty-two

The actual core preimage is extraspecial and contains the normal four. If
its Sylow quotient is cyclic of order four, the unique central involution
is weakly closed in the entire Sylow subgroup, hence in the core preimage.

The proof uses the elementary rank bound to turn fusion in the normal four
into transitive automorphisms of its centralizer. The intrinsic
three-involution theorem bounds squares there, contradicting the cyclic-four
quotient. Thus the involution orbit assumption and ambient simplicity are
unnecessary for this stronger conclusion.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389, the exclusion
of fusion into the quaternion-dihedral core (the appeal to 1.3–1.5).
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- With cyclic Sylow quotient of order four over the actual large core, the
central Sylow involution is weakly closed in the entire Sylow subgroup. -/
public theorem omegaCorePreimage_large_core_weak_closure
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4)
    (hcyclic : IsCyclic (S ⧸ omegaCorePreimage S))
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (t : S) (hconj : IsConj (z : G) (t : G)) : t = z := by
  obtain ⟨hExtra, hcard⟩ := omegaCorePreimage_large_core_structure S hH
  let : IsExtraspecial 2 (omegaCorePreimage S) := hExtra
  let : IsCyclic (S ⧸ omegaCorePreimage S) := hcyclic
  exact S.eq_of_isConj_of_extraspecial_cyclic_four_quotient hrank hZ E hE hunique
    (omegaCorePreimage S) (by omega)
    (four_le_omegaCorePreimage hN hrank S hZ E hE) hindex z hz hzc t hconj

/-- In particular, an involution in the actual core preimage cannot be fused
to a different central Sylow involution. -/
public theorem omegaCorePreimage_large_core_inside_fusion_exclusion
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 4)
    (hcyclic : IsCyclic (S ⧸ omegaCorePreimage S)) :
    ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z := by
  intro z t hz hzc _ht _htK hconj
  exact omegaCorePreimage_large_core_weak_closure hN hrank S hZ E hE hunique
    hH hindex hcyclic z hz hzc t hconj

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
