module
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.Basic
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# Faithful full-torus action on the first central triality layer

Apply the proved root-coroot conjugation equation to the entire ordered
positive-root product, then read its first two cubic coordinates. For an
arm parameter t and a fixed-field parameter s, the weights are t²/s and
ts/(F(t)F²(t)). If both are one, t² = s is Frobenius-fixed; square
injectivity forces t to be fixed, and the second weight forces t = s = 1.
All higher radical coordinates and both torus parameters are retained.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for
Aschbacher–Smith F.1.12(I)(4), printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.ConcreteBruhat
namespace Triality.Standard.Parabolics.CentralRootSquare

/-- Full torus weights on the two marked cubic coordinates. -/
def torusWeight (P : Parameters) (a : TorusCoordinates.OrbitParameters P) : Fin 2 → ExtensionField P :=
  ![a.1.val ^ 2 / a.2.val.val,
    a.1.val * a.2.val.val /
      (fieldFrobenius P a.1.val * fieldFrobenius P (fieldFrobenius P a.1.val))]

private def rootWeight (P : Parameters) (a : TorusCoordinates.Coordinates P)
    (j : Fin 12) : ExtensionField P :=
  (a 0).val ^ (typeDRootPairing 2).pairingIn ℤ (PositiveCoordinates.rootIndex j)
      (typeDSimpleRootIndex 2 0) *
    ((a 2).val ^ (typeDRootPairing 2).pairingIn ℤ (PositiveCoordinates.rootIndex j)
      (typeDSimpleRootIndex 2 2) *
    ((a 3).val ^ (typeDRootPairing 2).pairingIn ℤ (PositiveCoordinates.rootIndex j)
      (typeDSimpleRootIndex 2 3) *
     (a 1).val ^ (typeDRootPairing 2).pairingIn ℤ (PositiveCoordinates.rootIndex j)
      (typeDSimpleRootIndex 2 1)))

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group

private theorem product_curve (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (j : Fin 12) (u : ExtensionField P) :
    TorusCoordinates.product P a * PositiveCoordinates.curve P j u *
        (TorusCoordinates.product P a)⁻¹ =
      PositiveCoordinates.curve P j (rootWeight P a j * u) := by
  simp only [TorusCoordinates.product, conjugate_product, torusWord_curve_conjugate P hp]
  simp only [rootWeight, mul_assoc]

private theorem product_orderedProduct (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.Coordinates P) (v : PositiveCoordinates.Coordinates P) :
    TorusCoordinates.product P a * PositiveCoordinates.orderedProduct P v *
        (TorusCoordinates.product P a)⁻¹ =
      PositiveCoordinates.orderedProduct P (fun j => rootWeight P a j * v j) := by
  simp only [PositiveCoordinates.orderedProduct, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, mul_one]
  simp only [conjugate_mul, product_curve P hp]

private def layerPairing : Fin 2 → Fin 4 → ℤ := ![![2,-1,0,0], ![1,1,-1,-1]]

private theorem layer_pairing (j : Fin 2) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (PositiveCoordinates.rootIndex (![0,4] j))
      (typeDSimpleRootIndex 2 i) = layerPairing j i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex (![0,4] j)) k) = layerPairing j i := by
    revert j i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (layerPairing j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem rootWeight_layer (P : Parameters) (a : TorusCoordinates.OrbitParameters P)
    (j : Fin 2) : rootWeight P (TorusCoordinates.expand P a) (![0,4] j) =
      torusWeight P a j := by
  simp only [rootWeight, layer_pairing]
  fin_cases j <;> simp [torusWeight, layerPairing, TorusCoordinates.expand,
    TorusCoordinates.fixedUnit, TorusCoordinates.frobenius,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, -fieldFrobenius_apply]

private theorem layer_of_coordinates (P : Parameters) (hp : P.prime = 2)
    (r s : radical P .central) (w : Fin 12 → ExtensionField P)
    (h : PositiveCoordinates.expand P (extendOrbit P .central ((coordinates P hp).symm s)) =
      fun j => w j * PositiveCoordinates.expand P
        (extendOrbit P .central ((coordinates P hp).symm r)) j) :
    firstLayer P hp s = (w 0 * (firstLayer P hp r).1, w 4 * (firstLayer P hp r).2) := by
  exact Prod.ext (congrFun h 0) (congrFun h 4)

/-- All torus factors act diagonally over the cubic field, on every radical element. -/
theorem firstLayer_torusActor (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P) (r : radical P .central) :
    firstLayer P hp (conjugation P (torusActor P hp a) r) =
      (torusWeight P a 0 * (firstLayer P hp r).1,
       torusWeight P a 1 * (firstLayer P hp r).2) := by
  have hx : toCarrier P (TorusCoordinates.orbitElementary P hp a) ∈ parabolic P .central := by
    rw [← torusActor_val P hp a]
    exact (torusActor P hp a).property
  have hg : (⟨toCarrier P (TorusCoordinates.orbitElementary P hp a), hx⟩ :
      parabolic P .central) = torusActor P hp a := Subtype.ext (torusActor_val P hp a).symm
  let v := PositiveCoordinates.expand P (extendOrbit P .central ((coordinates P hp).symm r))
  have he := conjugation_coordinates_split P hp (TorusCoordinates.orbitElementary P hp a) hx r
  have hleft := congrArg (fun g : parabolic P .central =>
    PositiveCoordinates.orderedProduct P
      (PositiveCoordinates.expand P (extendOrbit P .central
        ((coordinates P hp).symm (conjugation P g r))))) hg.symm
  have hright := congrArg (fun t : SplitGroup P =>
    t * PositiveCoordinates.orderedProduct P v * t⁻¹)
    (TorusCoordinates.inclusion_orbitElementary P hp a)
  have hv := PositiveCoordinates.orderedProduct_injective P
    (hleft.trans (he.trans (hright.trans (product_orderedProduct P hp _ v))))
  have hh := layer_of_coordinates P hp r (conjugation P (torusActor P hp a) r)
    (rootWeight P (TorusCoordinates.expand P a)) hv
  exact hh.trans (Prod.ext
    (congrArg (· * (firstLayer P hp r).1) (rootWeight_layer P a 0))
    (congrArg (· * (firstLayer P hp r).2) (rootWeight_layer P a 1)))

/-- The displayed torus operator is cubic-linear. -/
def torusLinear (P : Parameters) (a : TorusCoordinates.OrbitParameters P) :
    (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
      (ExtensionField P × ExtensionField P) :=
  ((torusWeight P a 0) • LinearMap.fst _ _ _).prod
    ((torusWeight P a 1) • LinearMap.snd _ _ _)

theorem firstLayer_torusLinear (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P) (r : radical P .central) :
    firstLayer P hp (conjugation P (torusActor P hp a) r) =
      torusLinear P a (firstLayer P hp r) := firstLayer_torusActor P hp a r

theorem torusWeight_ne_zero (P : Parameters) (a : TorusCoordinates.OrbitParameters P)
    (j : Fin 2) : torusWeight P a j ≠ 0 := by
  have hs : a.2.val.val ≠ 0 := by exact_mod_cast a.2.ne_zero
  fin_cases j <;> simp [torusWeight, a.1.ne_zero, hs, -fieldFrobenius_apply]

/-- The two weights jointly detect the entire fixed torus, including the
complementary arm parameter. Square injectivity is essential here. -/
theorem torusWeight_eq_one (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P)
    (h0 : torusWeight P a 0 = 1) (h1 : torusWeight P a 1 = 1) : a = 1 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hsq : a.1.val ^ 2 = a.2.val.val := (div_eq_one_iff_eq
    (show a.2.val.val ≠ 0 by exact_mod_cast a.2.ne_zero)).mp h0
  have hfix : fieldFrobenius P a.1.val = a.1.val := by
    apply CharTwo.sq_injective
    change (fieldFrobenius P a.1.val) ^ 2 = a.1.val ^ 2
    rw [← map_pow, hsq]
    exact a.2.val.property
  have h : a.1.val = 1 := by
    change a.1.val * a.2.val.val /
      (fieldFrobenius P a.1.val * fieldFrobenius P (fieldFrobenius P a.1.val)) = 1 at h1
    rw [hfix, hfix, ← hsq] at h1
    calc
      a.1.val = a.1.val * a.1.val ^ 2 / a.1.val ^ 2 :=
        (mul_div_cancel_right₀ _ (pow_ne_zero 2 a.1.ne_zero)).symm
      _ = 1 := by simpa only [pow_two] using h1
  apply Prod.ext
  · exact Units.ext h
  · apply Units.ext
    apply Subtype.ext
    change a.2.val.val = 1
    simpa only [h, one_pow] using hsq.symm

/-- Trivial action on the first layer forces a torus actor to be the identity. -/
theorem torusActor_eq_one_of_firstLayer (P : Parameters) (hp : P.prime = 2)
    (a : TorusCoordinates.OrbitParameters P)
    (h : ∀ r, firstLayer P hp (conjugation P (torusActor P hp a) r) = firstLayer P hp r) :
    torusActor P hp a = 1 := by
  have hw (v : ExtensionField P × ExtensionField P) :
      (torusWeight P a 0 * v.1, torusWeight P a 1 * v.2) = v := by
    obtain ⟨r, rfl⟩ := firstLayer_surjective P hp v
    exact (firstLayer_torusActor P hp a r).symm.trans (h r)
  have h0 : torusWeight P a 0 = 1 := by simpa using congrArg Prod.fst (hw (1,0))
  have h1 : torusWeight P a 1 = 1 := by simpa using congrArg Prod.snd (hw (0,1))
  have ha := torusWeight_eq_one P hp a h0 h1
  apply Subtype.ext
  change (TorusCoordinates.torusMulEquiv P hp a).val = 1
  rw [ha, map_one]
  rfl

end Triality.Standard.Parabolics.CentralRootSquare
end
