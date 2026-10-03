module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.Fitting.PCoreSylowIndex
public import Theory.GroupTheory.PGroup.BinaryHallFactorAutomorphisms
public import Theory.GroupTheory.PGroup.LargeHallCentralProductAutomorphisms

/-!
# Structural index reduction for a nonnormal four-group

In the actual odd-core quotient of the central-omega normalizer, the
two-core is self-centralizing and the quotient is solvable. Consequently
an odd automorphism bound for the core gives a Sylow index dividing three,
and the action on three cosets bounds the original core preimage's index
by two. For a central product with a large noncyclic Hall tail, the
characteristic rotation product and its second omega detect odd
automorphisms on a nonabelian subgroup of order sixteen with cyclic
centralizer. The resulting automorphism bound completes the index reduction.
This step does not require intrinsic width one; no characteristicity of
the displayed factors or bound on the core order is assumed.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, p.392, the paragraph
beginning “Suppose H = T” and the start of Case 1.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- An odd automorphism bound gives the index of the actual quotient Sylow. -/
public theorem omegaQuotientSylow_index_dvd_three_of_odd_automorphisms
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (haut : ∀ U : Subgroup (MulAut (pCore 2 (OmegaQuotient S))),
      Odd (Nat.card U) → Nat.card U ∣ 3) :
    (omegaQuotientSylow S : Subgroup (OmegaQuotient S)).index ∣ 3 :=
  (omegaQuotientSylow S).index_dvd_three_of_pCore_odd_automorphisms
    (omegaQuotient_solvable hN S hZ)
    (omegaQuotient_centralizer_pCore_le hN S hZ) haut

/-- The odd automorphism bound controls the actual core preimage in the
original Sylow, without any assumption on the core order. -/
public theorem omegaCorePreimage_index_le_two_of_odd_automorphisms
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (haut : ∀ U : Subgroup (MulAut (pCore 2 (OmegaQuotient S))),
      Odd (Nat.card U) → Nat.card U ∣ 3) :
    (omegaCorePreimage S).index ≤ 2 := by
  rw [index_omegaCorePreimage]
  exact (omegaQuotientSylow S).relIndex_pCore_le_two_of_odd_automorphisms
    (omegaQuotient_solvable hN S hZ)
    (omegaQuotient_centralizer_pCore_le hN S hZ) haut

/-- A large noncyclic Hall tail bounds the core preimage's index by two.
The characteristic-subgroup construction for odd automorphisms applies
without an intrinsic width exclusion. -/
public theorem omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D) :
    (omegaCorePreimage S).index ≤ 2 := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic hrank S E hunique hnormal
  apply omegaCorePreimage_index_le_two_of_odd_automorphisms hN S hZ
  exact odd_automorphism_card_dvd_three_of_large_hall_central_product
    pCore_isPGroup A D hA hD hn hc hg hlarge

set_option linter.unusedVariables false in
/-- The structural index bound with the full hypotheses of the intrinsic
width-one branch. Width one is retained for the subsequent tail exclusion,
but the index reduction itself holds without it. -/
public theorem omegaCorePreimage_index_le_two_of_width_one_large_noncyclic_tail
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (fourImage S E).Normal)
    (hwidth : ∀ A D : Subgroup (pCore 2 (OmegaQuotient S)),
      A.Normal → D.Normal → IsExtraspecial 2 A → IsBinaryHallFactor D →
      D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))) → A ⊔ D = ⊤ →
      Nat.card A ≠ 32)
    (A D : Subgroup (pCore 2 (OmegaQuotient S))) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set (pCore 2 (OmegaQuotient S))))
    (hg : A ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D) :
    (omegaCorePreimage S).index ≤ 2 :=
  omegaCorePreimage_index_le_two_of_large_noncyclic_tail
    hN hrank S hZ E hunique hnormal A D hA hD hn hc hg hlarge

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
