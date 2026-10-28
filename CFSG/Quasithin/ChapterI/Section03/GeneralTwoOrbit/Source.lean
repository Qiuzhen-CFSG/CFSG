module

public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Actions
public import CFSG.Quasithin.ChapterI.Section03.LayerBalance

/-!
# Unconditional GLS II 5.22 at the prime two

The proved two-star fixed-point theorem, the odd-residual identification and
the unconditional Sylow-automorphism theorem discharge the universal two-layer
balance premise of `GeneralTwoOrbit`. Applying its structural proof gives the
single component orbit, both relative normal closures and subnormal closures,
and the original seed as a two-component of the orbit's fixed subgroup.
Every invariant normal subgroup contained in the orbit product's literal
O_{2',2} preserves that component under the induced fixed-subgroup quotient map.

The external-action theorem applies balance to the actual semidirect product,
so its actor and group may lie in different universes. No S₂, balance, model
classification or desired-output premise remains. The internal form also
retains the odd-E normal closure used in I.3; its ordinary-pumpup application
discharges the orbit premise of `Balance.pumpup_component_of_centralizes_oddCore`.

Source: GLS II, Chapter B, Proposition 5.22(i)-(iv), using Theorem 5.17;
Aschbacher--Smith, I.3.1(2), for the ordinary-pumpup application.
The existing conditional interfaces are preserved in the imported modules.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.GeneralTwoOrbit.Source
universe u v

/-- The genuine universal GLS 5.17 input, proved on each actual finite group. -/
theorem twoLayerCentralizerBalance : OrdinaryBalance.TwoLayerCentralizerBalance.{u} := by
  intro H _ _ hS P hP
  exact LayerBalance.map_twoLayer_centralizer_le hS P hP

variable {G : Type u} [Group G] [Finite G]

/-- GLS 5.22(i)-(iii) for an internal two-subgroup, including the odd-E normal
closure needed by the I.3 consumers. All earlier-source inputs are discharged. -/
theorem internal_orbit_and_closures
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      let D := I.map (centralizer (P : Set G)).subtype
      let X := componentOrbit J P
      D ≤ X ∧
      componentOrbit D X = X ∧
      componentOrbit D (twoComponentLayer G) = X ∧
      componentOrbit D (oddELayer G) = X ∧
      IsLeast {M : Subgroup G | D ≤ M ∧ M.IsSubnormal} X ∧
      IsLeast {M : Subgroup G | D ≤ M ∧ M ≤ twoComponentLayer G ∧
        (M.subgroupOf (twoComponentLayer G)).IsSubnormal} X ∧
      (D.subgroupOf (X ⊓ centralizer (P : Set G))).IsTwoComponent :=
  exists_orbit_and_closures twoLayerCentralizerBalance P hP I hI

/-- The literal orbit equality consumed by the ordinary and rank-two I.3
arguments, without any hypothesis on simple sections or the ambient models. -/
theorem twoComponentOrbit
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      componentOrbit (I.map (centralizer (P : Set G)).subtype) (oddELayer G) =
        componentOrbit J P := by
  obtain ⟨J, hJ, _, _, _, hodd, _⟩ := internal_orbit_and_closures P hP I hI
  exact ⟨J, hJ, hodd⟩

/-- The I.3 ordinary-pumpup application with its GLS orbit premise discharged.
The odd-core centralization refers to the original ambient group and seed. -/
theorem ordinary_pumpup
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent)
    (hodd : I.map (centralizer (P : Set G)).subtype ≤
      centralizer (pPrimeCore 2 G : Set G)) :
    ∃ J : Subgroup G, IsComponent G J ∧
      componentOrbit (I.map (centralizer (P : Set G)).subtype) (oddELayer G) =
        componentOrbit J P ∧
      I.map (centralizer (P : Set G)).subtype ≤ componentOrbit J P := by
  obtain ⟨J, hJ, he⟩ := twoComponentOrbit P hP I hI
  exact ⟨J, Balance.pumpup_component_of_centralizes_oddCore P _ J hJ he hodd,
    he, he ▸ le_componentOrbit _ (oddELayer G)⟩

variable {A : Type v} [Group A] [Finite A] [MulDistribMulAction A G]

/-- GLS II Proposition 5.22, all four clauses, for every finite two-group
action. The orbit, fixed-subgroup inclusion and quotient homomorphism are the
original ones; no additional earlier-source or classification premise remains. -/
theorem proposition522
    (hA : IsPGroup 2 A)
    (I : Subgroup (fixedPointSubgroup A G)) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      ∃ hX : IsInvariant A G (actionOrbit (A := A) J),
        let := hX
        let X := actionOrbit (A := A) J
        let D := I.map (fixedPointSubgroup A G).subtype
        let I₀ := I.comap (orbitFixedInclusion (A := A) X)
        D ≤ X ∧ componentOrbit D X = X ∧
        componentOrbit D (twoComponentLayer G) = X ∧
        IsLeast {M : Subgroup G | D ≤ M ∧ M.IsSubnormal} X ∧
        IsLeast {M : Subgroup G | D ≤ M ∧ M ≤ twoComponentLayer G ∧
          (M.subgroupOf (twoComponentLayer G)).IsSubnormal} X ∧
        I₀.IsTwoComponent ∧ I₀.map (orbitFixedInclusion X) = I ∧
        ∀ (N : Subgroup X) [N.Normal] (hN : IsInvariant A X N),
          N ≤ oddTwoCore X →
            letI : MulDistribMulAction A (X ⧸ N) := quotientMulDistribMulAction N hN
            (I₀.map (FixedPoints.quotientMap N hN)).IsTwoComponent :=
  GeneralTwoOrbit.proposition522 twoLayerCentralizerBalance hA I hI

end CFSG.Quasithin.ChapterI.GeneralTwoOrbit.Source
