module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Simple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Covers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Natural
/-!
# The remaining nilpotent-Fitting case on the original Geometry

Apply the full A.3.6 reduction to the literal component image in G₁/O₂(G₁).
The actual quotient equivalence transports the Cartan actor, its nontriviality
and its coprimality to that image. The simple-model and triple-cover arguments
remove the ordinary component rows; the characteristic-plane argument then
removes the natural-extension row.

The output retains the entire nilpotent-Fitting alternative, including the
SL₂(5) quotient, prime restrictions and extraspecial or homocyclic core shapes,
as well as every common A.3.6 clause. No field actor or Borel movement is
assumed. This is a reduction, not a proof of source 11.5.6(3).
The remaining row and 11.5.6(3--4) assembly stay with
qt-d-1222-natural-closure-cartan. The parent qt-d-1222-natural-closure retains
discharge of the preceding original flag/Cartan geometry.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02 CFSG.Quasithin.Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- All simple and triple-cover rows are excluded on the literal moved
component image. Only the two noncentral-Fitting alternatives remain. -/
theorem moved_component_noncentral_fitting_cases (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    (A36Natural B ∨ A36Nilpotent B) ∧ A36Common B ∧ primeRank 3 B ≤ 1 := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  obtain ⟨hc,hcommon,hrB⟩ := E.moved_component_remaining_source_cases hp hT hX c
    hcart hXR hCX hz hNG hr hodd hI hmoved
  refine ⟨?_,hcommon,hrB⟩
  cases hc with
  | natural h => exact Or.inl h
  | nilpotent h => exact Or.inr h
  | cover hcomp hcenter hmodel =>
      let : IsQuasisimple B := hcomp.2
      exact (three_cover_not_small_rank hmodel hcenter hrB).elim
  | simple hcomp hsimple hmodel =>
      let : IsSimpleGroup B := hsimple
      let : IsQuasisimple B := hcomp.2
      let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
      let eQ : (I ⧸ pCore 2 I) ≃* B :=
        (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans
          (cComponentTwoCoreQuotientEquiv (E.component_in_point_normalizer hI))
      obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX hcart.odd hI hmoved
      let a : MulAut B := MulAut.congr eQ (coreQuotientAction I x)
      have hd : orderOf a ∣ Nat.card E.X := by
        apply ((orderOf_map_dvd (MulAut.congr eQ).toMonoidHom _).trans
          (orderOf_map_dvd (coreQuotientAction I) x)).trans
        rw [← Subgroup.orderOf_coe x]
        exact E.X.orderOf_dvd_natCard hx
      have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
        (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
      have ha6 : Nat.Coprime (orderOf a) 6 :=
        (hcart.odd.of_dvd_nat hd).coprime_two_right.mul_right
          ((Nat.prime_three.coprime_iff_not_dvd.mpr
            (E.three_not_dvd_cartan_of_split_marking (c.cartanTorusEquiv hcart) hodd)).symm.of_dvd_left hd)
      have haB : Nat.Coprime (orderOf a) (Nat.card B) := by
        rw [← Nat.card_congr eQ.toEquiv]
        exact (E.cartan_coprime_component_of_split_marking (c.cartanTorusEquiv hcart)
          hcop hI).of_dvd hd (pCore 2 I).card_quotient_dvd_card
      have ha := remaining_simple_coprime_actor_eq_one hmodel hrB a ha6 haB
      exact (hne ((MulAut.congr eQ).injective (ha.trans (map_one _).symm))).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The only remaining full A.3.6 row for an original moved component is
the nilpotent-Fitting extension of SL₂(5). Its actual prime cores and all
common source clauses are retained. This is a sieve reduction, not 11.5.6(3). -/
theorem moved_component_nilpotent_fitting_case (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    A36Nilpotent B ∧ A36Common B ∧ primeRank 3 B ≤ 1 := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  obtain ⟨hcases,hcommon,hrB⟩ := E.moved_component_noncentral_fitting_cases hp hT hX c
    hcart hXR hCX hz hNG hr hodd hI hmoved
  refine ⟨?_,hcommon,hrB⟩
  rcases hcases with hnatural | hnilpotent
  · let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
    let eQ : (I ⧸ pCore 2 I) ≃* B :=
      (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans
        (cComponentTwoCoreQuotientEquiv (E.component_in_point_normalizer hI))
    obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX hcart.odd hI hmoved
    let a : MulAut B := MulAut.congr eQ (coreQuotientAction I x)
    have hd : orderOf a ∣ Nat.card E.X := by
      apply ((orderOf_map_dvd (MulAut.congr eQ).toMonoidHom _).trans
        (orderOf_map_dvd (coreQuotientAction I) x)).trans
      rw [← Subgroup.orderOf_coe x]
      exact E.X.orderOf_dvd_natCard hx
    have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
      (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
    have haB : Nat.Coprime (orderOf a) (Nat.card B) := by
      rw [← Nat.card_congr eQ.toEquiv]
      exact (E.cartan_coprime_component_of_split_marking (c.cartanTorusEquiv hcart)
        hcop hI).of_dvd hd (pCore 2 I).card_quotient_dvd_card
    have ha := natural_coprime_actor_eq_one hnatural a haB
    exact (hne ((MulAut.congr eQ).injective (ha.trans (map_one _).symm))).elim
  · exact hnilpotent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
