module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.UnitaryComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankOneComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki

/-!
# The complete simple rank-one row of the odd Cartan sieve

Inspect the actual Bender model isomorphism in the simple row of A.3.6.
The linear, unitary and Suzuki branches each construct Borel movement from
a moved component. Their existing lift and field-actor constructions are
applied to the same I/O₂(I), with no additional callbacks. The marked
point-normalizer calculation rules out that movement.

This closes this source row only. The remaining simple rows, triple covers,
natural and nilpotent-Fitting cases stay with the final Cartan sieve owner,
qt-d-1222-natural-closure-cartan. Preceding geometry is discharged by
qt-d-1222-natural-closure. Source: A.3.6 and 11.5.6(3), pp.43--45,780--781.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Every moved simple Bender component gives the literal Borel movement. -/
theorem bender_borel_movement_of_model
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (ho : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (eX : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    [IsSimpleGroup (I ⧸ pCore 2 I)]
    (hmodel : ClassificationModels.IsBenderModel (I ⧸ pCore 2 I))
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) : E.BorelMovement := by
  cases hmodel with
  | linear n hn hi =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hi
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hF)
      let B : BinaryField := {
        Carrier := F
        binaryAlgebra := ZMod.algebra F 2
        degree := n
        degree_pos := by omega
        card_eq := hF }
      exact E.linearTwo_borel_movement_of_quotient hp hT hX ho hXR eX hc hr hI
        B hn e hmoved
  | unitary n hn hi =>
      obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hi
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
        (by simpa only [← Nat.card_eq_fintype_card,pow_mul] using hF)
      let B : BinaryField := {
        Carrier := F
        binaryAlgebra := ZMod.algebra F 2
        degree := n * 2
        degree_pos := by omega
        card_eq := by simpa only [pow_mul] using hF }
      let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
        e.isSimpleGroup_congr.mp inferInstance
      exact E.unitary_borel_movement_of_quotient hp hT hX ho hXR eX hc hr hodd hI
        B J hn hF hconj e hmoved
  | suzuki m hm hi =>
      obtain ⟨e⟩ := hi
      exact E.suzuki_borel_movement_of_quotient hp hT hX ho hXR eX hc hI hm e hmoved

/-- The complete simple rank-one source row in the original marked geometry. -/
theorem bender_component_commutator_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    [IsSimpleGroup (I ⧸ pCore 2 I)]
    (hmodel : ClassificationModels.IsBenderModel (I ⧸ pCore 2 I)) :
    ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2 := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  by_contra hmoved
  exact E.no_borel_movement hT hX hcart.odd hXR
    (E.cartan_disjoint_Y hcart.odd hCX hz) hNG
    (E.oddPointNormalizerAction_of_cartan hT hX hcart)
    (E.bender_borel_movement_of_model hp hT hX hcart.odd hXR
      (c.cartanTorusEquiv hcart) hc hr hodd hI hmodel hmoved)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
