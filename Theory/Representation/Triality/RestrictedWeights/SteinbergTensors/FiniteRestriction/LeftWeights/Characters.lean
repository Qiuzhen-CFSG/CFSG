module

public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootSystems.TypeD4RestrictedWeights

/-!
# Inverting the GLS character convention

GLS3 §1.9 and 1.12.1 use inverse conjugation. Steinberg (6.1),
§13 uses direct conjugation. Invert characters and cocharacter parameters
simultaneously; the positive root groups and Cartan integers stay fixed.
All inversion maps below are actual regular morphisms.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.LeftWeights
universe u
variable {k : Type u} [Field k]

/-- Regular inversion is a group morphism on a commutative algebraic group. -/
def inversion (T : Variety k) [AlgebraicGroup T]
    (hc : ∀ x y : Variety.Point T, x * y = y * x) :
    Theory.AlgebraicGroup.Morphism T T where
  toVariety := Theory.AlgebraicGroup.invMorphism T
  map_one := inv_one
  map_mul := fun x y => (mul_inv_rev x y).trans (hc _ _)

@[simp] theorem inversion_apply (T : Variety k) [AlgebraicGroup T]
    (hc : ∀ x y : Variety.Point T, x * y = y * x) (t : Variety.Point T) :
    (inversion T hc).onPoints t = t⁻¹ := rfl

/-- The actual regular inversion of the multiplicative parameter. -/
def parameterInversion : Theory.AlgebraicGroup.Morphism (KMult k) (KMult k) :=
  inversion _ ((isMulCommutative_iff.mp (dVariety_isMulCommutative 1)))

/-- The left cocharacter keeps the raw word and inverts its parameter. -/
def leftCocharacter {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (h : ClosedSubgroupTorusCocharacter T) : ClosedSubgroupTorusCocharacter T :=
  h.comp parameterInversion

@[simp] theorem leftCocharacter_apply {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (h : ClosedSubgroupTorusCocharacter T)
    (t : Variety.Point (KMult k)) :
    (leftCocharacter h).onPoints t = h.onPoints t⁻¹ := rfl

theorem leftCocharacter_apply_eq_inv {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (h : ClosedSubgroupTorusCocharacter T)
    (t : Variety.Point (KMult k)) :
    (leftCocharacter h).onPoints t = (h.onPoints t)⁻¹ := map_inv h.onPoints t

/-- The diagonal coordinates carry inversion to inversion of units. -/
theorem dPointEquiv_inverse (n : ℕ) (t : Variety.Point (dVariety k n)) :
    dPointEquiv n t⁻¹ = (dPointEquiv n t)⁻¹ := by
  let f : Variety.Point (dVariety k n) →* (Fin n → kˣ) :=
    ⟨⟨dPointEquiv n, dPointEquiv_one n⟩, dPointEquiv_mul n⟩
  exact map_inv f t

/-- Inverting a character is regular inversion on its values. -/
theorem inverseCharacter_morphism {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) : χ⁻¹ = parameterInversion.comp χ := rfl

theorem pointCharacter_inv {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (t : Variety.Point T) :
    (χ⁻¹).pointCharacter t = (χ.pointCharacter t)⁻¹ := by
  change (dPointEquiv 1 (χ.onPoints t)⁻¹ 0 : k) = _
  rw [dPointEquiv_inverse]
  exact Units.val_inv_eq_inv_val (dPointEquiv 1 (χ.onPoints t) 0)

/-- Pullback, including graph and Frobenius pullback, commutes with inversion. -/
theorem pullback_inv {T U : Variety k} [AlgebraicGroup T] [AlgebraicGroup U]
    (f : Theory.AlgebraicGroup.Morphism T U) (χ : TorusCharacter U) :
    TorusCharacter.pullback f χ⁻¹ = (TorusCharacter.pullback f χ)⁻¹ :=
  map_inv (TorusCharacter.pullback f) χ

theorem pullback_inversion {T : Variety k} [AlgebraicGroup T]
    (hc : ∀ x y : Variety.Point T, x * y = y * x) (χ : TorusCharacter T) :
    TorusCharacter.pullback (inversion T hc) χ = χ⁻¹ := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext t
  exact map_inv χ.onPoints t

/-- Inverting both sides of the character--cocharacter pairing preserves its integer. -/
theorem inverse_pairing {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {χ : TorusWeight T} {h : ClosedSubgroupTorusCocharacter T} {m : ℤ}
    (he : WeightCocharacterEquation T χ h m) :
    WeightCocharacterEquation T χ⁻¹ (leftCocharacter h) m := by
  intro t
  rw [pointCharacter_inv, leftCocharacter_apply, he, dPointEquiv_inverse]
  simp

/-- Inverting just the cocharacter reverses the exponent. -/
theorem left_pairing {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {χ : TorusWeight T} {h : ClosedSubgroupTorusCocharacter T} {m : ℤ}
    (he : WeightCocharacterEquation T χ h m) :
    WeightCocharacterEquation T χ (leftCocharacter h) (-m) := by
  intro t
  rw [leftCocharacter_apply, he, dPointEquiv_inverse]
  simp

/-- The raw root equation at the inverse torus point is direct conjugation. -/
theorem direct_conjugation {K : Variety k} [AlgebraicGroup K]
    {T X : ClosedSubgroup K} {χ : TorusWeight T} (he : RootWeightEquation T X χ)
    (x : OneParameterParametrization X.carrierVariety) (u : k)
    (t : Variety.Point T.carrierVariety) :
    T.includePoint t * X.includePoint (x.value u) * (T.includePoint t)⁻¹ =
      X.includePoint (x.value ((χ⁻¹).pointCharacter t * u)) := by
  have h := he x u t⁻¹
  change (T.inclusion.onPoints t⁻¹)⁻¹ * _ * T.inclusion.onPoints t⁻¹ = _ at h
  rw [map_inv, inv_inv] at h
  have heval : χ.pointCharacter t⁻¹ = (χ⁻¹).pointCharacter t := by
    change (dPointEquiv 1 (χ.onPoints t⁻¹) 0 : k) = _
    rw [map_inv]
    rfl
  rwa [heval] at h

/-- The entire Cartan matrix survives simultaneous inversion. -/
theorem left_cartan {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (r s : D.Root) :
    WeightCocharacterEquation T (D.rootWeight r)⁻¹
      (leftCocharacter (D.rootCocharacter s)) (D.pairing r s) :=
  inverse_pairing (hD.rootWeight_rootCocharacter r s)

theorem left_cartan_self {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (r : D.Root) :
    WeightCocharacterEquation T (D.rootWeight r)⁻¹
      (leftCocharacter (D.rootCocharacter r)) 2 := by
  simpa only [hD.2.2.2.2.2.2.1 r] using left_cartan hD r r

/-- Negation of integral weights defines the left character embedding. -/
def embedding {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) : Weight ↪ TorusCharacter T :=
  ⟨fun a => e (Multiplicative.ofAdd (-a)), fun _ _ h => neg_injective (e.injective h)⟩

theorem embedding_eq_inv {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) (a : Weight) :
    embedding e a = (e (Multiplicative.ofAdd a))⁻¹ := map_inv e _

@[simp] theorem embedding_zero {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) : embedding e 0 = 1 := by
  simp [embedding]

@[simp] theorem embedding_neg {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) (a : Weight) :
    embedding e (-a) = (embedding e a)⁻¹ := by
  simp [embedding, ofAdd_neg]

theorem embedding_add {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) (a b : Weight) :
    embedding e (a + b) = embedding e a * embedding e b := by
  change e (Multiplicative.ofAdd (-(a + b))) = _
  rw [neg_add, ofAdd_add, map_mul]
  rfl

theorem embedding_zsmul {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) (m : ℤ) (a : Weight) :
    embedding e (m • a) = embedding e a ^ m := by
  change e (Multiplicative.ofAdd (-(m • a))) = _
  rw [← smul_neg, ofAdd_zsmul, map_zpow]
  rfl

theorem embedding_nsmul {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) (m : ℕ) (a : Weight) :
    embedding e (m • a) = embedding e a ^ m := by
  change e (Multiplicative.ofAdd (-(m • a))) = _
  rw [← smul_neg, ofAdd_nsmul, map_pow]
  rfl

theorem embedding_sum {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T) {ι : Type*}
    (s : Finset ι) (a : ι → Weight) :
    embedding e (∑ i ∈ s, a i) = ∏ i ∈ s, embedding e (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, embedding_add, ih]

/-- Reflection is integral linear, for the unchanged numbered D4 Cartan matrix. -/
theorem reflection_neg (i : Fin 4) (a : Weight) : reflection i (-a) = -reflection i a := by
  funext j
  simp only [reflection, Pi.neg_apply]
  ring

/-- The raw normalizer character equation at `-a` gives all four left equations.
The geometry owner supplies the actual torus maps and their raw equation. -/
theorem reflection_character {T : Variety k} [AlgebraicGroup T]
    (e : Multiplicative Weight ≃* TorusCharacter T)
    (c : Fin 4 → Variety.Point T → Variety.Point T)
    (he : ∀ i a t, (e (Multiplicative.ofAdd (reflection i a))).pointCharacter t =
      (e (Multiplicative.ofAdd a)).pointCharacter (c i t)) :
    ∀ i a t, (embedding e (reflection i a)).pointCharacter t =
      (embedding e a).pointCharacter (c i t) := by
  intro i a t
  change (e (Multiplicative.ofAdd (-reflection i a))).pointCharacter t = _
  rw [← reflection_neg]
  exact he i (-a) t

end Triality.RestrictedWeights.SteinbergTensors.LeftWeights
