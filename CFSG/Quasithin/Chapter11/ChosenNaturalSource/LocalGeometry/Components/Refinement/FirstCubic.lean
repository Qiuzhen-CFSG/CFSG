module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstKernel
public import Theory.GroupTheory.CComponent.SevenCoverTheta

/-!
# Faithful cubic actors in the first flag normalizer

The component containing L₁ centralizes V₁. A faithful subgroup of order
three in N_G(V₁) therefore supplies a cubic outside that component. A
centerless two-core quotient of cubic rank two with two-group outer group
has component index prime to three, so it absorbs every cubic actor. The alternating-seven theorem also treats its central three-cover,
using the actual cover's exponent-three argument.

All quotient transports use K/O₂(K) and K.subgroupOf N_G(V₁). Normality
is relative to that normalizer. The flag PSL₂ model, L₁-centralization,
and faithful Cartan factor are preceding flag/Cartan inputs, owned by
qt-d-1222-natural-flag-cartan and ultimately discharged by
qt-d-1222-natural-local-geometry. The relative-components owner retains
the remaining sieve and source-family assembly.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, first-index proof, printed pp.761--762, using A.3.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem relative_cubic_mem
    {H K : Subgroup G} (hK : Source.NormalComponentIn H K)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (hH : primeRank 3 H ≤ 2) {x : G} (hxH : x ∈ H) (hx : orderOf x = 3) : x ∈ K := by
  let B := K.subgroupOf H
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1)
      (pCore_map_iso 2 _)
  let : B.Normal := hK.2
  have hzB : center (B ⧸ pCore 2 B) = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨b,hb⟩).property)
  have hrB : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by rwa [primeRank_congr 3 e]
  have hoB := ho.of_equiv (MulAut.outerCongr e).symm
  have hi : Nat.Coprime 3 B.index :=
    cComponent_index_coprime_three_of_quotient B hK.1.2 hzB hrB hH (by
      obtain ⟨m,hm⟩ := hoB.exists_card_dvd_pow
      exact ((by decide : Nat.Coprime 3 2).pow_right m).coprime_dvd_right hm)
  exact primeToResidual_le B hi (mem_primeToResidual_of_pow (n := 1)
    (show (⟨x,hxH⟩ : H) ^ (3^1) = 1 from Subtype.ext (by simpa [hx] using pow_orderOf_eq_one x)))

private theorem relative_seven_cubic_mem
    {H K : Subgroup G} (hK : Source.NormalComponentIn H K)
    (hm : IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7)
    (hH : primeRank 3 H ≤ 2) {x : G} (hxH : x ∈ H) (hx : orderOf x = 3) : x ∈ K := by
  let B := K.subgroupOf H
  let e : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  let : B.Normal := hK.2
  have hx' : orderOf (⟨x,hxH⟩ : H) = 3 := (orderOf_coe _).symm.trans hx
  rcases hm with hm | ⟨hq,hz,⟨a⟩⟩
  · let a := hm.some
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv (e.trans a).symm
    exact SevenCComponentTheta.order_three_mem_of_quotient_seven B hK.1.2 (e.trans a) hH hx'
  · let := hq
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
    exact SevenCComponentTheta.order_three_mem_of_central_quotient_seven B hK.1.2
      ((QuotientGroup.congr _ _ e (by
        apply le_antisymm
        · rintro _ ⟨z,hz,rfl⟩
          exact ((centerCongr e) ⟨z,hz⟩).property
        · intro z hz
          exact ⟨e.symm z, ((centerCongr e).symm ⟨z,hz⟩).property, e.apply_symm_apply z⟩)).trans a) hH hx'

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
  (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem first_exists_cubic_outside
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ∃ x : G, x ∈ normalizer (f.Vi 0 : Set G) ∧ orderOf x = 3 ∧ x ∉ K := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card X₁ by rw [hXcard])
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  refine ⟨x,hXN x.property,hxG,?_⟩
  intro hxK
  have he : (x : G) = 1 := mem_bot.mp ((first_component_disjoint_of_faithful_cartan
    D S f hm hfix hK hLK hfaith).le_bot ⟨hxK,x.property⟩)
  rw [he, orderOf_one] at hxG
  contradiction

/-- A full-cubic-rank, centerless, outer-two model is impossible for the
first containing component: its cubic residual would absorb the faithful
Cartan factor. This uses the literal intrinsic O₂(K) quotient. -/
theorem first_component_not_centerless_cubic
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) : False := by
  obtain ⟨x,hxN,hx,hout⟩ := first_exists_cubic_outside D S f hm hfix hK.1 hLK hXN hXcard hfaith
  exact hout (relative_cubic_mem hK hz hr ho
    ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
      3 Nat.prime_three (by decide)) hxN hx)

/-- Both alternating-seven rows, including the actual central three-cover,
are excluded in the first normalizer by the same faithful cubic actor. -/
theorem first_component_not_seven
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXN : X₁ ≤ normalizer (f.Vi 0 : Set G)) (hXcard : Nat.card X₁ = 3)
    (hfaith : X₁ ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ (IsAlternating (K ⧸ pCore 2 K) 7 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmodel
  obtain ⟨x,hxN,hx,hout⟩ := first_exists_cubic_outside D S f hm hfix hK.1 hLK hXN hXcard hfaith
  exact hout (relative_seven_cubic_mem hK hmodel
    ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
      3 Nat.prime_three (by decide)) hxN hx)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
