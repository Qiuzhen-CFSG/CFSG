module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.UnitaryMovement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.FixedAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import Theory.GroupTheory.CComponent.FullOddRankCharacteristic
public import Theory.SpecificGroups.ThreeDivisibility.Classical

/-!
# The actual unitary component in the Cartan sieve

Positive three-rank and the source bound m₃(Y) ≤ 1 fix a simple unitary
component under G₁. A genuine Hermitian basis change then aligns its quotient
with the original Sylow intersection. The odd-subfield construction supplies
Borel movement, and the point-normalizer contradiction proves the component
commutator clause. No field-actor, invariant-Borel or normalizer-lift premise
is retained. Simplicity is inherited from the simple row of A.3.6.

Only preceding point/Cartan and quotient geometry remain explicit. The other
A.3.6 rows and final assembly stay with qt-d-1222-natural-closure-cartan;
the preceding inputs are discharged by qt-d-1222-natural-closure.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The original three-rank bound prevents a second unitary component. -/
theorem unitary_component_normalized (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField) (J : HermitianForm 3 F.Carrier)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : (I ⧸ pCore 2 I) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    E.G₁ ≤ normalizer (I : Set G) := by
  let A := I.subgroupOf E.Y
  let eA : A ≃* I := subgroupOfEquivOfLe hI.1
  let eQ : (A ⧸ pCore 2 A) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans e
  let : Group.IsPerfect A := hI.2.perfect
  let : Group.IsPerfect (A ⧸ pCore 2 A) := inferInstance
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eQ.isSimpleGroup
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    rcases (inferInstance : (center (A ⧸ pCore 2 A)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (A ⧸ pCore 2 A)
        (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
      (QuotientGroup.quotientBot)).isSimpleGroup }
  have hd : 3 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J n hn hc hconj
  have hpos : 0 < primeRank 3 (A ⧸ pCore 2 A) := by
    have hne : primeRank 3 (A ⧸ pCore 2 A) ≠ 0 :=
      fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
    omega
  let : A.Characteristic := hI.2.characteristic_of_full_odd_rank (by decide : Odd 3)
    hz hpos (by omega)
  have hnorm := normalizer_le_normalizer_characteristic_image E.Y A
  rw [map_subgroupOf_eq_of_le hI.1] at hnorm
  exact E.G₁_normalizes_Y.trans hnorm

open CartanActions.FieldDetection.OddLinear
open OddPrimeSylow.NormalizedOuter.FormTransport

/-- The actual simple unitary quotient yields Borel movement in the original
geometry, including all simultaneous normalizer lifts. -/
theorem unitary_borel_movement_of_quotient
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField) (J : HermitianForm 3 F.Carrier)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcF : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ z, J.conj z = z ^ (2 ^ n))
    (e : (I ⧸ pCore 2 I) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) : E.BorelMovement := by
  have hTI := hT.trans (E.unitary_component_normalized hr hI F J (by omega) hcF hconj e)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcF hconj
  obtain ⟨eJ⟩ := exists_projectiveEquiv J (2 ^ n) hcF hf
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    eJ.isSimpleGroup_congr.mp inferInstance
  obtain ⟨c⟩ := Unitary.exists_coordinates hTI F (standardForm J) rfl
    (by omega) hcF hconj (e.trans eJ)
  obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX ho hI hmoved
  exact c.borel_movement hn hcF hconj hTI hI.1 x hx
    (E.cartan_normalizes_component_sylow hp hT hX ho hXR hI hx) ho
    (Nat.prime_three.coprime_iff_not_dvd.mpr
      (E.three_not_dvd_cartan_of_split_marking eX hodd)).symm
    (E.cartan_coprime_component_of_split_marking eX hc hI) hne

/-- The unitary row of 11.5.6(3) uses the actual point-normalizer calculation. -/
theorem unitary_component_commutator_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField) (J : HermitianForm 3 F.Carrier)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 2 ≤ n) (hcF : Nat.card F.Carrier = (2 ^ n) ^ 2)
    (hconj : ∀ z, J.conj z = z ^ (2 ^ n))
    (e : (I ⧸ pCore 2 I) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  by_contra hmoved
  exact E.no_borel_movement hT hX hcart.odd hXR
    (E.cartan_disjoint_Y hcart.odd hCX hz) hNG
    (E.oddPointNormalizerAction_of_cartan hT hX hcart)
    (E.unitary_borel_movement_of_quotient hp hT hX hcart.odd hXR
      (c.cartanTorusEquiv hcart) hc hr hodd hI F J hn hcF hconj e hmoved)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
