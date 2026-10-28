module

public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Moving central Sylow involutions in characteristic two

The normal closure of a central elementary Sylow seed lies in the center of
the two-core, hence is elementary abelian. If an involution seed is moved by
the ambient group and that closure has order at most four, its order is four:
order two would make the seed central. This constructs the actual four-group,
retaining its original generator and normal closure.

Source application: Aschbacher--Smith 2.5.12, printed pp.557--558, using
B.2.14(2), printed p.78.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The elementary closure part of B.2.14 for any central elementary Sylow seed. -/
theorem central_sylow_normalClosure_elementary
    (P : Sylow 2 G) (Z : Subgroup G) [IsElementaryAbelian 2 Z]
    (hc : Z ≤ centralizer (P : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    IsElementaryAbelian 2 (normalClosure (Z : Set G)) ∧
      normalClosure (Z : Set G) ≤ pCore 2 G := by
  have hZC : Z ≤ centralizer (pCore 2 G : Set G) :=
    hc.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hQ : normalClosure (Z : Set G) ≤ pCore 2 G :=
    normalClosure_le_normal (hZC.trans hchar)
  have hC : normalClosure (Z : Set G) ≤ centralizer (pCore 2 G : Set G) :=
    normalClosure_le_normal hZC
  let : IsMulCommutative (normalClosure (Z : Set G)) :=
    le_centralizer_iff_isMulCommutative.mp (hC.trans (centralizer_le hQ))
  exact ⟨IsElementaryAbelian.normalClosure_of_isMulCommutative Z, hQ⟩

/-- A moving involution with a rank-two elementary closure generates a normal four. -/
theorem moving_involution_normalClosure_four
    (P : Sylow 2 G) (z : G) (hz : orderOf z = 2)
    (hc : zpowers z ≤ centralizer (P : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hmove : z ∉ center G)
    (hcard : Nat.card (normalClosure (zpowers z : Set G)) ≤ 4) :
    IsKleinFour (normalClosure (zpowers z : Set G)) ∧
      normalClosure (zpowers z : Set G) ≤ pCore 2 G := by
  let Z := zpowers z
  let E := normalClosure (Z : Set G)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.zpowers_of_pow_eq_one
    (by rw [← hz]; exact pow_orderOf_eq_one z)
  obtain ⟨he, hQ⟩ := central_sylow_normalClosure_elementary P Z hc hchar
  let : IsElementaryAbelian 2 E := he
  have hZE : Z ≤ E := le_normalClosure
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers, hz]
  have hdiv : 2 ∣ Nat.card E := hZcard ▸ card_dvd_of_le hZE
  have hge : 2 ≤ Nat.card E := hZcard ▸ Subgroup.card_le_of_le hZE
  have hne : Nat.card E ≠ 2 := by
    intro hecard
    have heq : Z = E := eq_of_le_of_card_ge hZE (by omega)
    have hn : (zpowers z).Normal := by
      change Z.Normal
      rw [heq]
      infer_instance
    let := hn
    apply hmove
    rw [mem_center_iff]
    intro g
    have hg : g ∈ normalizer (zpowers z : Set G) := le_normalizer_of_normal (mem_top g)
    rw [normalizer_zpowers_eq_centralizer_of_order_two z hz,
      mem_centralizer_singleton_iff] at hg
    exact hg
  change Nat.card E ≤ 4 at hcard
  have hecard : Nat.card E = 4 := by omega
  have hEne : E ≠ ⊥ := by intro hh; simp [hh] at hecard
  let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot _).mpr hEne
  exact ⟨⟨hecard, IsElementaryAbelian.exponent_eq_prime⟩, hQ⟩

end Theory.GroupTheory
