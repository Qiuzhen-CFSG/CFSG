module
public import Theory.GroupTheory.CComponent.FullOddRankCharacteristic
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankTwoMovement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.FixedAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# The original PSL₃ component in the Cartan action

A centerless quotient carrying positive three-rank is characteristic in Y,
since the source bound m₃(Y) ≤ 1 excludes a second such component. Thus T
fixes the component. Sylow conjugacy and the odd coefficient subfield now
construct the actual normalizer lifts and Borel movement, even when the
aligned Cartan actor has a nontrivial inner Borel factor.

The final consumer applies the marked point-normalizer calculation and
Cartan disjointness to obtain the PSL₃ branch of 11.5.6(3). Only preceding
point/flag geometry, the proved three-rank bound and the actual component
quotient remain explicit. The full odd-component sieve stays with
qt-d-1222-natural-closure-cartan; final preceding-input discharge belongs
to qt-d-1222-natural-closure.

Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Three-rank one makes a centerless linear component invariant under the
whole normalizer of Y, excluding a swapped orbit without ambient normality. -/
theorem linearThree_component_normalized (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField)
    (e : (I ⧸ pCore 2 I) ≃* PSL(3,F.Carrier)) :
    E.G₁ ≤ normalizer (I : Set G) := by
  let A := I.subgroupOf E.Y
  let eA : A ≃* I := subgroupOfEquivOfLe hI.1
  let eQ : (A ⧸ pCore 2 A) ≃* PSL(3,F.Carrier) :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans e
  let : Group.IsPerfect A := hI.2.perfect
  let : Group.IsPerfect (A ⧸ pCore 2 A) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect SL(3,F.Carrier) := Atlas.sl_perfect 3 (by decide)
  let : IsSimpleGroup PSL(3,F.Carrier) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eQ.isSimpleGroup
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hh : eQ a ∈ center PSL(3,F.Carrier) := by
      rw [mem_center_iff]
      intro z
      obtain ⟨b,rfl⟩ := eQ.surjective z
      simpa only [map_mul] using congrArg eQ (mem_center_iff.mp ha b)
    rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F.Carrier),mem_bot] at hh
    exact eQ.map_eq_one_iff.mp hh
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
      (QuotientGroup.quotientBot)).isSimpleGroup }
  have hd : 3 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F.Carrier) (show (0 : Fin 3) ≠ 1 by decide)).trans (card_subgroup_dvd_card _)
  have hpos : 0 < primeRank 3 (A ⧸ pCore 2 A) := by
    have hn : primeRank 3 (A ⧸ pCore 2 A) ≠ 0 :=
      fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
    omega
  let : A.Characteristic := hI.2.characteristic_of_full_odd_rank (by decide : Odd 3)
    hz hpos (by omega)
  have hn := normalizer_le_normalizer_characteristic_image E.Y A
  rw [map_subgroupOf_eq_of_le hI.1] at hn
  exact E.G₁_normalizes_Y.trans hn
open CartanActions.FieldDetection.OddLinear

/-- The PSL₃ case constructs every simultaneous subfield normalizer lift and
its nontrivial Cartan field action from the actual component quotient. -/
theorem linearThree_borel_movement_of_quotient
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField)
    (e : (I ⧸ pCore 2 I) ≃* PSL(3,F.Carrier))
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) : E.BorelMovement := by
  have hTI := hT.trans (E.linearThree_component_normalized hr hI F e)
  obtain ⟨c⟩ := RankTwo.exists_coordinates hTI F e
  obtain ⟨x,hx,hne⟩ := E.exists_component_quotient_mover hp hX ho hI hmoved
  exact c.borel_movement hTI hI.1 x hx
    (E.cartan_normalizes_component_sylow hp hT hX ho hXR hI hx) ho
    (E.cartan_coprime_component_of_split_marking eX hc hI) hne

/-- The rank-three field marking needs no additional alignment or lifting input. -/
theorem linearThree_borel_movement_of_field_marking
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (w : LinearFieldMarking E I 3) (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    E.BorelMovement := by
  exact E.linearThree_borel_movement_of_quotient hp hT hX ho hXR eX hc hr hI
    w.field w.model hmoved

/-- The PSL₃ branch of literal 11.5.6(3), with the actual point-normalizer
calculation and Cartan torus marking applied. -/
theorem linearThree_component_commutator_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (F : BinaryField)
    (e : (I ⧸ pCore 2 I) ≃* PSL(3,F.Carrier)) : ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  by_contra hmoved
  exact E.no_borel_movement hT hX hcart.odd hXR
    (E.cartan_disjoint_Y hcart.odd hCX hz) hNG
    (E.oddPointNormalizerAction_of_cartan hT hX hcart)
    (E.linearThree_borel_movement_of_quotient hp hT hX hcart.odd hXR
      (c.cartanTorusEquiv hcart) hc hr hI F e hmoved)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
