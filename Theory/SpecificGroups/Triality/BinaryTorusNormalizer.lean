module
public import Theory.SpecificGroups.Triality.BinaryTorusCentralizer
public import Theory.GroupTheory.CentralizerInjectiveImage
-- Intentional internal proof extension: reuse the coordinate-weight calculation
-- without exposing its implementation or changing the shared centralizer API.
import all Theory.SpecificGroups.Triality.BinaryTorusCentralizer

/-!
# The exact binary-triality Borel torus normalizer

The order-seven torus fixes the three long-root coordinates pointwise. The
existing weight calculation kills the other three coordinates, so its
unipotent centralizer has order eight. Unique Borel factorization then shows
that the Borel torus normalizer is its centralizer and has order 56.

These are the actual native subgroups used in the marked completion comparison
for Aschbacher--Smith F.4.15--17 and14.2.18--19. In particular, the Borel torus
normalizer is larger than the torus; normalization alone cannot replace the
hexagon relation. Root coordinates and coroot actions follow GLS3 §§2.4,2.6
through the imported Geck construction.
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.BinaryTorusCentralizer
open Parabolics ConcreteBruhat PositiveCoordinates
open RadicalCoordinates.LeviCommutators CentralCovers.TwoPrimary
open Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData
local notation "P" => binaryParameters 1 Nat.zero_lt_one

private def longPairing : Fin 3 → Fin 4 → ℤ :=
  ![![-1,2,-1,-1], ![1,-1,1,1], ![0,1,0,0]]
private theorem long_pairing (j : Fin 3) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (longPosition j))
      (typeDSimpleRootIndex 2 i) = longPairing j i := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex i) k *
      rootCoords (positiveIndex (longPosition j)) k) = longPairing j i := by
    revert j i
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (longPairing j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem long_weight_one (a : TorusCoordinates.OrbitParameters P) (i : Fin 3) :
    rootWeight (TorusCoordinates.expand P a) (longPosition i) = 1 := by
  have ha : a.2 = 1 := by
    have h := pow_card_eq_one' (x := a.2)
    rw [Nat.card_units,card_fixedField] at h
    simpa only [show (P).q - 1 = 1 from rfl,pow_one] using h
  have ht : a.1.val ^ 7 = 1 := by
    have h := pow_card_eq_one' (x := a.1)
    rw [Nat.card_units,card_extensionField] at h
    exact congrArg Units.val h
  have hF (x : ExtensionField P) : fieldFrobenius P x = x^2 := by
    rw [fieldFrobenius_apply]; rfl
  have hf (t : (ExtensionField P)ˣ) :
      (TorusCoordinates.frobenius P t).val = t.val^2 := hF t.val
  simp only [rootWeight,long_pairing,TorusCoordinates.expand,ha]
  fin_cases i <;> simp only [longPairing, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zpow_neg_one, zpow_ofNat, pow_zero, pow_one]
  · change a.1.val⁻¹ * ((TorusCoordinates.frobenius P a.1).val⁻¹ *
      ((TorusCoordinates.frobenius P (TorusCoordinates.frobenius P a.1)).val⁻¹ *
        (TorusCoordinates.fixedUnit P 1).val^2)) = 1
    simp only [map_one,Units.val_one,one_pow,mul_one,hf]
    have he : a.1.val * (a.1.val^2 * (a.1.val^2)^2) = 1 := by
      convert ht using 1
      ring
    calc
      _ = (a.1.val * (a.1.val^2 * (a.1.val^2)^2))⁻¹ := by
        simp only [mul_inv_rev]
        ac_rfl
      _ = 1 := by rw [he,inv_one]
  · change a.1.val * ((TorusCoordinates.frobenius P a.1).val *
      ((TorusCoordinates.frobenius P (TorusCoordinates.frobenius P a.1)).val *
        (TorusCoordinates.fixedUnit P 1).val⁻¹)) = 1
    simp only [map_one,Units.val_one,inv_one,mul_one,hf]
    convert ht using 1
    ring
  · simp only [map_one,Units.val_one,one_mul]

/-- Every long root is fixed pointwise by the binary order-seven torus. -/
theorem long_mem_torus_centralizer (i : Fin 3) (u : fixedField P) :
    long P rfl i u ∈ centralizer (torus P : Set (Carrier P)) := by
  intro g hg
  obtain ⟨a,ha⟩ := (TorusCoordinates.torusMulEquiv P prime_two).surjective ⟨g,hg⟩
  have hval : FixedDescent.carrierToSplit P prime_two g =
      TorusCoordinates.product P (TorusCoordinates.expand P a) := by
    change FixedDescent.carrierToSplit P prime_two (⟨g,hg⟩ : torus P).val = _
    rw [←ha,TorusCoordinates.torusMulEquiv_val,
      FixedDescent.carrierToSplit_toCarrier]
    exact TorusCoordinates.inclusion_orbitElementary P prime_two a
  have hlong : FixedDescent.carrierToSplit P prime_two (long P prime_two i u) = longSplit P i u :=
    (FixedDescent.carrierToSplit_toCarrier P prime_two _).trans (longElementary_val P prime_two i u)
  have hconj : g * long P prime_two i u * g⁻¹ = long P prime_two i u := by
    apply FixedDescent.carrierToSplit_injective P prime_two
    simp only [map_mul,map_inv,hval,hlong,longSplit,product_curve,long_weight_one,one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- The fixed unipotent elements have exactly the three long-root coordinates. -/
theorem mem_unipotent_torus_centralizer_iff (g : Carrier P) :
    g ∈ unipotent P ⊓ centralizer (torus P : Set (Carrier P)) ↔
      ∃ a : Fin 3 → fixedField P, baseProduct 1 Nat.zero_lt_one (0,a) = g := by
  constructor
  · intro h
    let u : unipotent P := ⟨g,h.1⟩
    let v := (positiveEquiv 1 Nat.zero_lt_one).symm u
    have hv : v.1 = 0 := short_zero_of_centralizes u h.2
    refine ⟨v.2,?_⟩
    have he := congrArg Subtype.val ((positiveEquiv 1 Nat.zero_lt_one).apply_symm_apply u)
    rw [positiveEquiv_val] at he
    change baseProduct 1 Nat.zero_lt_one v = g at he
    rw [show v = (0,v.2) from Prod.ext hv rfl] at he
    exact he
  · rintro ⟨a,rfl⟩
    constructor
    · rw [←positiveEquiv_val]
      exact (positiveEquiv 1 Nat.zero_lt_one (0,a)).property
    · simp only [baseProduct]
      change short P prime_two 0 0 * long P prime_two 0 (a 0) * short P prime_two 1 0 *
        short P prime_two 2 0 * long P prime_two 1 (a 1) * long P prime_two 2 (a 2) ∈ _
      simp only [short_zero,one_mul,mul_one]
      exact (centralizer _).mul_mem ((centralizer _).mul_mem
        (long_mem_torus_centralizer 0 _) (long_mem_torus_centralizer 1 _))
          (long_mem_torus_centralizer 2 _)

/-- The eight fixed unipotent elements, with their literal native coordinates. -/
def torusFixedUnipotentEquiv : (Fin 3 → fixedField P) ≃
    (unipotent P ⊓ centralizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) :=
  Equiv.ofBijective
    (fun a => ⟨baseProduct 1 Nat.zero_lt_one (0,a),
      (mem_unipotent_torus_centralizer_iff _).mpr ⟨a,rfl⟩⟩)
    ⟨fun a b h => congrArg Prod.snd (baseProduct_injective 1 Nat.zero_lt_one
        (congrArg Subtype.val h)),
      fun g => by
        obtain ⟨a,ha⟩ := (mem_unipotent_torus_centralizer_iff g).mp g.property
        exact ⟨a,Subtype.ext ha⟩⟩

theorem centralizer_torus_card_eq_eight :
    Nat.card (unipotent P ⊓ centralizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) = 8 := by
  rw [←Nat.card_congr torusFixedUnipotentEquiv,Nat.card_fun,card_fixedField,Nat.card_fin]
  rfl

private theorem torus_commute {x y : Carrier P} (hx : x ∈ torus P) (hy : y ∈ torus P) :
    Commute x y := by
  let e := TorusCoordinates.torusMulEquiv P prime_two
  have h : (⟨x,hx⟩ : torus P) * ⟨y,hy⟩ = ⟨y,hy⟩ * ⟨x,hx⟩ := by
    apply e.symm.injective
    simp only [map_mul,mul_comm]
  exact congrArg Subtype.val h

/-- A unipotent element normalizing the complementary torus centralizes it. -/
theorem unipotent_normalizer_eq_centralizer :
    unipotent P ⊓ normalizer (torus P : Set (Carrier P)) =
      unipotent P ⊓ centralizer (torus P : Set (Carrier P)) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le_normalizer _))
  rintro u ⟨hu,hn⟩
  refine ⟨hu,?_⟩
  intro t ht
  have htN := (normal_subgroupOf_iff_le_normalizer (unipotent_le_borel P)).mp
    (unipotent_normal_in_borel P prime_two) (torus_le_borel P ht)
  have hU : u*t*u⁻¹*t⁻¹ ∈ unipotent P := by
    have hh := (mem_normalizer_iff.mp htN u⁻¹).mp ((unipotent P).inv_mem hu)
    simpa only [mul_assoc] using (unipotent P).mul_mem hu hh
  have hT : u*t*u⁻¹*t⁻¹ ∈ torus P :=
    (torus P).mul_mem ((mem_normalizer_iff.mp hn t).mp ht) ((torus P).inv_mem ht)
  have he : u*t*u⁻¹*t⁻¹ = 1 :=
    (disjoint_unipotent_torus P prime_two).le_bot ⟨hU,hT⟩
  have hc : u*t=t*u := by
    have hh := congrArg (fun z : Carrier P => z*t*u) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using hh
  exact hc.symm

/-- The whole Borel normalizer of the seven-torus centralizes it. -/
theorem borel_normalizer_eq_centralizer :
    borel P ⊓ normalizer (torus P : Set (Carrier P)) =
      borel P ⊓ centralizer (torus P : Set (Carrier P)) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le_normalizer _))
  rintro g ⟨hg,hn⟩
  obtain ⟨⟨u,t⟩,he,_⟩ := existsUnique_borel_factors P prime_two ⟨g,hg⟩
  change (u : Carrier P) * t = g at he
  have huN : (u : Carrier P) ∈ normalizer (torus P : Set (Carrier P)) := by
    have hh := (normalizer _).mul_mem hn ((torus P).le_normalizer ((torus P).inv_mem t.property))
    simpa only [←he,mul_inv_cancel_right] using hh
  have huC : (u : Carrier P) ∈ centralizer (torus P : Set (Carrier P)) :=
    (show (u : Carrier P) ∈ unipotent P ⊓ centralizer (torus P : Set (Carrier P)) from
      unipotent_normalizer_eq_centralizer ▸ ⟨u.property,huN⟩).2
  have htC : (t : Carrier P) ∈ centralizer (torus P : Set (Carrier P)) :=
    fun x hx => (torus_commute hx t.property).eq
  exact ⟨hg,he ▸ (centralizer _).mul_mem huC htC⟩

/-- Unique factorization of the Borel torus normalizer by its fixed unipotent
subgroup and the actual torus. -/
def borelTorusNormalizerEquiv :
    (unipotent P ⊓ centralizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) ×
        torus P ≃ (borel P ⊓ normalizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) :=
  Equiv.ofBijective
    (fun a => ⟨(a.1 : Carrier P)*a.2,
      (borel P).mul_mem (unipotent_le_borel P a.1.property.1) (torus_le_borel P a.2.property),
      (normalizer _).mul_mem ((centralizer_le_normalizer _) a.1.property.2)
        ((torus P).le_normalizer a.2.property)⟩)
    (by
      constructor
      · intro a b he
        have h := Subgroup.mul_injective_of_disjoint (disjoint_unipotent_torus P prime_two)
          (a₁ := (⟨a.1,a.1.property.1⟩,a.2)) (a₂ := (⟨b.1,b.1.property.1⟩,b.2))
          (congrArg Subtype.val he)
        exact Prod.ext (Subtype.ext (congrArg (fun z => z.1.val) h))
          (congrArg (fun z : unipotent P × torus P => z.2) h)
      · intro g
        obtain ⟨⟨u,t⟩,he,_⟩ := existsUnique_borel_factors P prime_two ⟨g,g.property.1⟩
        change (u : Carrier P) * t = g.val at he
        have hgC : (g : Carrier P) ∈ centralizer (torus P : Set (Carrier P)) :=
          (show (g : Carrier P) ∈ borel P ⊓ centralizer (torus P : Set (Carrier P)) from
            borel_normalizer_eq_centralizer ▸ g.property).2
        have htC : (t : Carrier P) ∈ centralizer (torus P : Set (Carrier P)) :=
          fun x hx => (torus_commute hx t.property).eq
        have huC : (u : Carrier P) ∈ centralizer (torus P : Set (Carrier P)) := by
          have hh := (centralizer _).mul_mem hgC ((centralizer _).inv_mem htC)
          simpa only [←he,mul_inv_cancel_right] using hh
        exact ⟨(⟨u,u.property,huC⟩,t),Subtype.ext he⟩)

theorem borel_torus_normalizer_card :
    Nat.card (borel P ⊓ normalizer (torus P : Set (Carrier P)) : Subgroup (Carrier P)) = 56 := by
  rw [←Nat.card_congr borelTorusNormalizerEquiv,Nat.card_prod,
    centralizer_torus_card_eq_eight,TorusCoordinates.card_torus P prime_two]
  rfl

private theorem map_normalizer_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (Q : Subgroup A) :
    (normalizer (Q : Set A)).map f = f.range ⊓ normalizer (Q.map f : Set B) := by
  rw [← map_comap_eq]
  congr 1
  rw [comap_normalizer_eq_of_le_range (map_le_range f Q),
    comap_map_eq_self_of_injective hf]

private theorem map_centralizer_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (Q : Subgroup A) :
    (centralizer (Q : Set A)).map f = f.range ⊓ centralizer (Q.map f : Set B) := by
  simpa only [inf_top_eq, top_inf_eq, ← MonoidHom.range_eq_map] using
    (map_inf_centralizer_of_injective f hf ⊤ Q).symm

private theorem native_borel_normalizer_eq_centralizer :
    normalizer ((torus P).subgroupOf (borel P) : Set (borel P)) =
      centralizer ((torus P).subgroupOf (borel P) : Set (borel P)) := by
  apply map_injective (borel P).subtype_injective
  rw [map_normalizer_injective _ (borel P).subtype_injective,
    map_centralizer_injective _ (borel P).subtype_injective,
    map_subgroupOf_eq_of_le (torus_le_borel P),range_subtype]
  exact borel_normalizer_eq_centralizer

variable {G : Type*} [Group G] (f : borel P →* G) (hf : Function.Injective f)
include hf

/-- The exact Borel normalizer equality persists under a literal marking. -/
theorem borel_embedding_normalizer_eq_centralizer :
    f.range ⊓ normalizer (((torus P).subgroupOf (borel P)).map f : Set G) =
      f.range ⊓ centralizer (((torus P).subgroupOf (borel P)).map f : Set G) := by
  rw [← map_normalizer_injective f hf,← map_centralizer_injective f hf,
    native_borel_normalizer_eq_centralizer]

/-- The fixed unipotent subgroup of the marked torus has order eight. -/
theorem borel_embedding_unipotent_centralizer_card :
    Nat.card (((unipotent P).subgroupOf (borel P)).map f ⊓
      centralizer (((torus P).subgroupOf (borel P)).map f : Set G) : Subgroup G) = 8 := by
  rw [map_inf_centralizer_of_injective f hf,card_map_of_injective hf]
  rw [← card_map_of_injective (borel P).subtype_injective,
    ← map_inf_centralizer_of_injective _ (borel P).subtype_injective,
    map_subgroupOf_eq_of_le (unipotent_le_borel P),
    map_subgroupOf_eq_of_le (torus_le_borel P)]
  exact centralizer_torus_card_eq_eight

/-- The full marked Borel torus normalizer has order 56. -/
theorem borel_embedding_normalizer_card :
    Nat.card (f.range ⊓ normalizer
      (((torus P).subgroupOf (borel P)).map f : Set G) : Subgroup G) = 56 := by
  rw [← map_normalizer_injective f hf,card_map_of_injective hf,
    ← card_map_of_injective (borel P).subtype_injective,
    map_normalizer_injective _ (borel P).subtype_injective,
    map_subgroupOf_eq_of_le (torus_le_borel P),range_subtype]
  exact borel_torus_normalizer_card
end Triality.Standard.BinaryTorusCentralizer

