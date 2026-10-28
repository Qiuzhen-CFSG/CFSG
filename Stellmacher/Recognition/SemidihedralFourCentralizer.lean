module
public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Theory.SpecificGroups.GL2.ThreeFourCentralizer
public import Theory.GroupTheory.SelfCentralizingImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Four-group centralizer orders in the semidihedral N2 branch

Let T be a four-group containing an involution x. If the odd core of
N = C_G(x) centralizes T, then C_G(T) has order four times that core.

The checked recognition theorem identifies N/O(N) with GL₂(3). The
four-group embeds through the odd-order kernel and is self-centralizing
in the quotient. Thus the image of C_G(T) is precisely that four-group;
the assumed centralization puts the entire kernel in C_G(T), giving the
order formula. No triviality of the odd core is assumed or used.

Source: Alperin–Brauer–Gorenstein, III.8 Proposition 5, article p.117;
`refs/original/n-group-global/semidihedral-source/README.md`.
-/

namespace Stellmacher.Recognition
open Subgroup Matrix
/-- A four-group centralized by the odd core has centralizer order four
 times the odd-core order. -/
public theorem fourCentralizer_card_of_simple_nTwo
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (hcentral : (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ≤ centralizer (T : Set G)) :
    Nat.card (centralizer (T : Set G)) =
      4 * Nat.card (pPrimeCore 2 (centralizer ({x} : Set G))) := by
  let N := centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  let A := T.subgroupOf N
  have hCN : centralizer (T : Set G) ≤ N :=
    centralizer_le (Set.singleton_subset_iff.mpr hxT)
  have hTN : T ≤ N := T.le_centralizer.trans hCN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hTN
  have hA : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans hT
  obtain ⟨e⟩ := involutionCentralizer_oddCoreQuotient_equiv_gl2_three_of_simple_nTwo
    S hS hN x hx
  let eF : ABG.GL2 3 1 ≃* GL (Fin 2) (ZMod 3) :=
    Units.mapEquiv (GaloisField.equivZmodP 3).toRingEquiv.mapMatrix.toMulEquiv
  let f : N →* GL (Fin 2) (ZMod 3) :=
    (e.trans eF).toMonoidHom.comp (QuotientGroup.mk' O)
  have hfker : f.ker = O := by
    ext a
    change eF (e (QuotientGroup.mk' O a)) = 1 ↔ a ∈ O
    rw [← eF.map_one, eF.injective.eq_iff, ← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff a
  have hfodd : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact pPrimeCore_coprime_card
  have hinj : Function.Injective (f.comp A.subtype) :=
    injective_comp_subtype_of_coprime_ker f hfodd A (IsElementaryAbelian.isPGroup 2 A)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAf : Nat.card (A.map f) = 4 := by
    rw [← hA]
    apply Nat.card_image_of_injOn
    intro a ha b hb hab
    exact congrArg Subtype.val (hinj (show f.comp A.subtype ⟨a, ha⟩ =
      f.comp A.subtype ⟨b, hb⟩ from hab))
  have hker : f.ker ≤ centralizer (A : Set N) := by
    rw [hfker]
    intro a ha b hb
    apply Subtype.ext
    exact hcentral (mem_map_of_mem N.subtype ha) b hb
  have hc := card_centralizer_of_selfCentralizing_image f A hinj hker
    (Matrix.GeneralLinearGroup.three_four_centralizer (A.map f) hAf)
  rw [hA, hfker] at hc
  have heq : centralizer (A : Set N) = (centralizer (T : Set G)).subgroupOf N := by
    ext a
    constructor
    · intro ha b hb
      exact congrArg Subtype.val (ha ⟨b, hTN hb⟩ hb)
    · intro ha b hb
      exact Subtype.ext (ha b hb)
  rw [heq, Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at hc
  exact hc
end Stellmacher.Recognition
