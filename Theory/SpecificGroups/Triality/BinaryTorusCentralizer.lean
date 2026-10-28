module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.RootRelations
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# The seven-centralizer bound in the binary-triality Borel

The three cubic root coordinates of a unipotent element have nontrivial
weights under a generator of the torus of order seven. An element fixing
that torus therefore has all three cubic coordinates zero. Its remaining
three binary coordinates give an injection into a set of order eight.
Sylow conjugacy extends the bound to every order-seven subgroup in the
literal Borel, retaining any two-subgroup it centralizes.

This is the size bound used to exclude the marked binary-triality row of
Aschbacher–Smith 5.2.2, printed p.648 (`refs/quasithin.pdf`). The root
ordering and coroot action are those of GLS3 §§2.4 and 2.6, as constructed
in the imported Geck model. No identification of the whole centralizer
as a dihedral group is needed for this bound.
-/

public noncomputable section
open Subgroup
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.ConcreteBruhat
namespace Triality.Standard.BinaryTorusCentralizer
open Parabolics PositiveCoordinates
local notation "P" => binaryParameters 1 Nat.zero_lt_one
private theorem prime_two : (P).prime = 2 := rfl

private def rootWeight (a : TorusCoordinates.Coordinates P) (j : Fin 12) : ExtensionField P :=
  (a 0).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 0) *
    ((a 2).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 2) *
    ((a 3).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 3) *
     (a 1).val ^ (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 1)))

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem product_curve (a : TorusCoordinates.Coordinates P) (j : Fin 12)
    (u : ExtensionField P) :
    TorusCoordinates.product P a * curve P j u * (TorusCoordinates.product P a)⁻¹ =
      curve P j (rootWeight a j * u) := by
  simp only [TorusCoordinates.product, conjugate_product, torusWord_curve_conjugate P prime_two]
  simp only [rootWeight, mul_assoc]

private theorem product_orderedProduct (a : TorusCoordinates.Coordinates P) (v : Coordinates P) :
    TorusCoordinates.product P a * orderedProduct P v * (TorusCoordinates.product P a)⁻¹ =
      orderedProduct P (fun j => rootWeight a j * v j) := by
  simp only [orderedProduct, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  simp only [conjugate_mul, product_curve]

private def shortPairing : Fin 3 → Fin 4 → ℤ :=
  ![![2,-1,0,0], ![1,1,-1,-1], ![1,0,1,-1]]
private theorem short_pairing (j : Fin 3) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (![0,4,7] j))
      (typeDSimpleRootIndex 2 i) = shortPairing j i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex (![0,4,7] j)) k) = shortPairing j i := by
    revert j i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (shortPairing j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem short_weights_ne_one (t : (ExtensionField P)ˣ) (ht : orderOf t = 7)
    (j : Fin 3) : rootWeight (TorusCoordinates.expand P (t,1)) (![0,4,7] j) ≠ 1 := by
  have hn (k : ℕ) (hk : ¬7 ∣ k) : t.val ^ k ≠ 1 := by
    intro he
    have hh : t ^ k = 1 := Units.ext (by simpa using he)
    exact hk (ht ▸ orderOf_dvd_of_pow_eq_one hh)
  have hF (x : ExtensionField P) : fieldFrobenius P x = x^2 := by
    rw [fieldFrobenius_apply]; rfl
  simp only [rootWeight,short_pairing]
  fin_cases j
  · simpa [shortPairing,TorusCoordinates.expand,TorusCoordinates.fixedUnit] using hn 2 (by decide)
  · simp only [shortPairing, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.cons_val_three, TorusCoordinates.expand]
    simp only [TorusCoordinates.frobenius,
      TorusCoordinates.fixedUnit, map_one, Units.val_one, one_zpow, mul_one]
    intro he
    have he' : t.val = t.val^2 * (t.val^2)^2 := by
      apply (div_eq_one_iff_eq (mul_ne_zero (pow_ne_zero 2 t.ne_zero)
        (pow_ne_zero 2 (pow_ne_zero 2 t.ne_zero)))).mp
      simpa [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,hF] using he
    apply hn 5 (by decide)
    apply mul_left_cancel₀ t.ne_zero
    calc
      t.val * t.val^5 = t.val^2*(t.val^2)^2 := by ring
      _ = t.val := he'.symm
      _ = t.val*1 := (mul_one _).symm
  · simp only [shortPairing, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.cons_val_three, TorusCoordinates.expand]
    simp only [TorusCoordinates.frobenius,
      TorusCoordinates.fixedUnit, map_one, Units.val_one, one_zpow, mul_one]
    intro he
    have he' : t.val*t.val^2 = (t.val^2)^2 := by
      apply (div_eq_one_iff_eq (pow_ne_zero 2 (pow_ne_zero 2 t.ne_zero))).mp
      simpa [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,hF] using he
    apply hn 1 (by decide)
    rw [pow_one]
    apply mul_right_cancel₀ (pow_ne_zero 3 t.ne_zero)
    calc
      t.val*t.val^3 = (t.val^2)^2 := by ring
      _ = t.val*t.val^2 := he'.symm
      _ = 1*t.val^3 := by ring

private theorem short_zero_of_centralizes (u : unipotent P)
    (hu : (u : Carrier P) ∈ centralizer (torus P : Set (Carrier P))) :
    ((CentralCovers.TwoPrimary.positiveEquiv 1 Nat.zero_lt_one).symm u).1 = 0 := by
  let v := (CentralCovers.TwoPrimary.positiveEquiv 1 Nat.zero_lt_one).symm u
  have hv : FixedDescent.carrierToSplit P prime_two u = orderedProduct P (expand P v) := by
    rw [← CentralCovers.TwoPrimary.baseProduct_toSplit]
    apply congrArg (FixedDescent.carrierToSplit P prime_two)
    exact (congrArg Subtype.val ((CentralCovers.TwoPrimary.positiveEquiv 1 Nat.zero_lt_one).apply_symm_apply u)).symm.trans
      (CentralCovers.TwoPrimary.positiveEquiv_val 1 Nat.zero_lt_one v)
  let : Fintype (ExtensionField P) := Fintype.ofFinite _
  obtain ⟨t,ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ExtensionField P)ˣ)
  have ht7 : orderOf t = 7 := by
    rw [Nat.card_units,card_extensionField] at ht
    exact ht
  let a : TorusCoordinates.OrbitParameters P := (t,1)
  let g := TorusCoordinates.torusMulEquiv P prime_two a
  have hc : (g : Carrier P) * u * (g : Carrier P)⁻¹ = u := by
    rw [hu g g.property, mul_inv_cancel_right]
  have hg : FixedDescent.carrierToSplit P prime_two g = TorusCoordinates.product P
      (TorusCoordinates.expand P a) := by
    change FixedDescent.carrierToSplit P prime_two (TorusCoordinates.torusMulEquiv P prime_two a).val = _
    rw [TorusCoordinates.torusMulEquiv_val, FixedDescent.carrierToSplit_toCarrier]
    exact TorusCoordinates.inclusion_orbitElementary P prime_two a
  have hc' := congrArg (FixedDescent.carrierToSplit P prime_two) hc
  simp only [map_mul,map_inv,hg,hv] at hc'
  rw [product_orderedProduct] at hc'
  have he := orderedProduct_injective P hc'
  funext j
  have hj : rootWeight (TorusCoordinates.expand P a) (![0,4,7] j) * v.1 j = v.1 j := by
    have hh := congrFun he (![0,4,7] j)
    fin_cases j <;> simpa [expand] using hh
  by_contra hne
  exact short_weights_ne_one t ht7 j (mul_right_cancel₀ hne (hj.trans (one_mul _).symm))

/-- Only the three binary root coordinates can survive the seven-torus action. -/
theorem centralizer_torus_card_le_eight :
    Nat.card (unipotent P ⊓ centralizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) ≤ 8 := by
  let E := unipotent P ⊓ centralizer (torus P : Set (Carrier P))
  let f : E → Fin 3 → fixedField P := fun x =>
    ((CentralCovers.TwoPrimary.positiveEquiv 1 Nat.zero_lt_one).symm ⟨x,x.property.1⟩).2
  have hf : Function.Injective f := by
    intro x y he
    have hxy : (⟨x,x.property.1⟩ : unipotent P) = ⟨y,y.property.1⟩ := by
      apply (CentralCovers.TwoPrimary.positiveEquiv 1 Nat.zero_lt_one).symm.injective
      apply Prod.ext
      · exact (short_zero_of_centralizes _ x.property.2).trans (short_zero_of_centralizes _ y.property.2).symm
      · exact he
    exact Subtype.ext (congrArg (fun z : unipotent P => (z : Carrier P)) hxy)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun,card_fixedField,Nat.card_fin] at hb
  exact hb

/-- Any two-subgroup in the actual binary Borel centralized by an order-seven
subgroup has order at most eight; no preferred Hall marking is required. -/
theorem borel_two_subgroup_card_le_eight
    (V E : Subgroup (borel P)) (hV : IsPGroup 2 V) (hE : Nat.card E = 7)
    (hc : V ≤ centralizer (E : Set (borel P))) : Nat.card V ≤ 8 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C := (torus P).subgroupOf (borel P)
  have hC : Nat.card C = 7 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel P)).toEquiv,
      TorusCoordinates.card_torus P prime_two]
    rfl
  have hb : Nat.card (borel P) = 28672 := FixedCellCount.card_borel 1 Nat.zero_lt_one
  have hs (F : Subgroup (borel P)) (hF : Nat.card F = 7) :
      Nat.card F = 7 ^ (Nat.card (borel P)).factorization 7 := by
    rw [hF,hb]
    decide +kernel
  let Q : Sylow 7 (borel P) := Sylow.ofCard E (hs E hE)
  let Q₀ : Sylow 7 (borel P) := Sylow.ofCard C (hs C hC)
  obtain ⟨g,a,_,ha⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (borel P)) Q Q₀
  change E.map a.toMonoidHom = C at ha
  let f : borel P →* Carrier P := (borel P).subtype.comp a.toMonoidHom
  have hf : Function.Injective f := (borel P).subtype_injective.comp a.injective
  have hEf : E.map f = torus P := by
    rw [← map_map,ha,map_subgroupOf_eq_of_le (torus_le_borel P)]
  let U := (unipotentSylow P prime_two).subtype (unipotent_le_borel P)
  let : Unique (Sylow 2 (borel P)) := Sylow.unique_of_normal U (unipotent_normal_in_borel P prime_two)
  obtain ⟨Q₂,hQ₂⟩ := (hV.map a.toMonoidHom).exists_le_sylow
  have hV₂ : V.map a.toMonoidHom ≤ (unipotent P).subgroupOf (borel P) := by
    rw [Subsingleton.elim Q₂ U] at hQ₂
    exact hQ₂
  have hVU : V.map f ≤ unipotent P := by
    rw [← map_map]
    exact (map_mono hV₂).trans_eq (map_subgroupOf_eq_of_le (unipotent_le_borel P))
  have hVC : V.map f ≤ centralizer (torus P : Set (Carrier P)) := by
    rw [←hEf]
    exact (map_mono hc).trans (map_centralizer_le_centralizer_image E f)
  have hh := (Nat.card_le_card_of_injective (inclusion (le_inf hVU hVC))
    (inclusion_injective _)).trans centralizer_torus_card_le_eight
  rwa [card_map_of_injective hf] at hh
end Triality.Standard.BinaryTorusCentralizer
