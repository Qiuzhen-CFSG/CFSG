module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Assembly
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Normalization

/-!
# Short-root sections normalized by the actual arms torus at q = 2

The arms Levi torus acts with weights t², t² and t⁻¹ on the three
short roots and fixes the three long roots. A commutator with one moving
actor constructs additive sections equivariant under every arms actor.
The long sections are retained literally, so the existing commuting and
upper relations persist. These are preparations for the two lower exchanges,
not an assertion of those exchanges.

The weight calculations adapt the checked calculations in SmallField.Commuting
(accepted fleet task qt-i01-triality-small-commuting-pairs), preserving its
D₄ marking. Source: GLS3 §§2.4.5, 2.4.7 and 6.1;
Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates.LeviCommutators
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
noncomputable section

private def weightTable : Fin 12 → Fin 4 → ℤ :=
  ![![2, -1, 0, 0], ![0, -1, 2, 0], ![0, -1, 0, 2], ![-1, 2, -1, -1],
    ![1, 1, -1, -1], ![-1, 1, 1, -1], ![-1, 1, -1, 1],
    ![1, 0, 1, -1], ![-1, 0, 1, 1], ![1, 0, -1, 1],
    ![1, -1, 1, 1], ![0, 1, 0, 0]]

private theorem pairing_table (j : Fin 12) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 i) =
      weightTable j i := by
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weightTable j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases j <;> fin_cases i <;>
    norm_num [weightTable, rootIndex, difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem torus_curve (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 12) (u : ExtensionField P) :
    torusWord P i t * curve P j u * (torusWord P i t)⁻¹ =
      curve P j (t.val ^ weightTable j i * u) := by
  rw [torusWord_curve_conjugate P hp, pairing_table]

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem torus_short_zero (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * shortSplit P 0 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      shortSplit P 0 (t.val ^ 2 * u) := by
  simp only [torusElementary_arms_val, shortSplit, conjugate_mul, conjugate_product,
    torus_curve P hp]
  simp [shortPosition, weightTable, TorusCoordinates.frobenius, map_mul, map_pow, -fieldFrobenius_apply]

private theorem torus_long_two (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * longSplit P 2 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ = longSplit P 2 u := by
  simp only [torusElementary_arms_val, longSplit, conjugate_product, torus_curve P hp]
  simp [longPosition, weightTable]


private def armShortWeight (P : Parameters) (t : (ExtensionField P)ˣ) :
    Fin 3 → ExtensionField P :=
  ![t.val ^ 2, t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)),
    t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val)]

private theorem torus_short_scaling (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (i : Fin 3) (x : ExtensionField P) :
    torusActor P hp .arms t * short P hp i x * (torusActor P hp .arms t)⁻¹ =
      short P hp i (armShortWeight P t i * x) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val]
  fin_cases i
  · exact torus_short_zero P hp t x
  · exact torus_arms_short_one_conjugate P hp t x
  · exact torus_arms_short_two_conjugate P hp t x

private theorem torus_fixes_longs (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (hnorm : cubicNorm P t.val = 1)
    (j : Fin 3) (u : fixedField P) :
    torusActor P hp .arms t * long P hp j u * (torusActor P hp .arms t)⁻¹ =
      long P hp j u := by
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, longElementary_val]
  fin_cases j
  · have h : (cubicNorm P t.val)⁻¹ * u = u := by rw [hnorm, inv_one, one_mul]
    exact (torus_arms_long_zero_conjugate P hp t u).trans (congrArg (longSplit P 0) h)
  · have h : cubicNorm P t.val * u = u := by rw [hnorm, one_mul]
    exact (torus_arms_long_one_conjugate P hp t u).trans (congrArg (longSplit P 1) h)
  · exact torus_long_two P hp t u

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hP" => binaryParameters_prime 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

private theorem small_norm (t : Fˣ) : cubicNorm P t.val = 1 := by
  rcases fixedField_cases (cubicNorm P t.val) with h | h
  · have hv := congrArg Subtype.val h
    change t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val) = 0 at hv
    exact False.elim ((mul_ne_zero (mul_ne_zero t.ne_zero
      ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero))
      ((map_ne_zero (fieldFrobenius P)).mpr ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero))) hv)
  · exact h

private theorem small_weights (t : Fˣ) :
    t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) = t.val ^ 2 ∧
    t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val) = t.val⁻¹ := by
  have hn := congrArg Subtype.val (small_norm t)
  change t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val) = 1 at hn
  have hF (x : F) : fieldFrobenius P x = x ^ 2 := rfl
  simp only [hF, ← pow_mul] at hn ⊢
  have ht := t.ne_zero
  constructor
  · field_simp
    linear_combination -hn
  · field_simp

private theorem small_torus_motion (i : Fin 3) :
    ∃ (t : Fˣ) (c : F), c ≠ 1 ∧
      (∀ x, torusActor P hP .arms t * short P hP i x *
        (torusActor P hP .arms t)⁻¹ = short P hP i (c*x)) ∧
      (∀ j u, torusActor P hP .arms t * long P hP j u *
        (torusActor P hP .arms t)⁻¹ = long P hP j u) := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have ht1 : t.val ≠ 1 := by
    intro h
    have : t = 1 := Units.ext h
    rw [this, orderOf_one, Nat.card_units, card_extensionField] at ht
    change 1 = 7 at ht
    contradiction
  have ht2 : t.val ^ 2 ≠ 1 := by
    intro h
    have hh := orderOf_dvd_of_pow_eq_one (show t ^ 2 = 1 from Units.ext h)
    rw [ht, Nat.card_units, card_extensionField] at hh
    change 7 ∣ 2 at hh
    norm_num at hh
  refine ⟨t, armShortWeight P t i, ?_, torus_short_scaling P hP t i,
    torus_fixes_longs P hP t (small_norm t)⟩
  fin_cases i
  · exact ht2
  · change t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) ≠ 1
    rw [(small_weights t).1]
    exact ht2
  · change t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val) ≠ 1
    rw [(small_weights t).2]
    exact inv_ne_one.mpr ht1


/-- The published small-field arms weights, in short-root order. -/
def shortWeight (t : Fˣ) : Fin 3 → F := ![t.val ^ 2, t.val ^ 2, t.val⁻¹]

private theorem armShortWeight_eq (t : Fˣ) : armShortWeight P t = shortWeight t := by
  funext i
  fin_cases i
  · rfl
  · exact (small_weights t).1
  · exact (small_weights t).2

/-- The same actual torus actor scales every marked short root. -/
theorem short_scaling (t : Fˣ) (i : Fin 3) (x : F) :
    torusActor P hP .arms t * short P hP i x * (torusActor P hP .arms t)⁻¹ =
      short P hP i (shortWeight t i * x) := by
  simpa only [armShortWeight_eq] using torus_short_scaling P hP t i x

variable {E : Type*} [Group E] {f : E →* BinaryCarrier 1 Nat.zero_lt_one}

/-- Lift the literal torus element through the genuine PSL₂(8) arms Levi. -/
def armsTorusLift (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (t : Fˣ) : E :=
  armsSection f hf hk ⟨torusActor P hP .arms t, torusActor_mem_levi P hP .arms t⟩

theorem armsTorusLift_project (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (t : Fˣ) :
    f (armsTorusLift hf hk t) = torusActor P hP .arms t :=
  DFunLike.congr_fun (armsSection_project f hf hk) _

private theorem torus_seventh_power (t : Fˣ) : (torusActor P hP .arms t) ^ 7 = 1 := by
  have he : elementaryInclusion P (torusElementary P hP .arms t) =
      productHom P hP ![t, 1, frobenius P t, frobenius P (frobenius P t)] := by
    simp [productHom, product, torusElementary_arms_val, torusWord_one P hP]
  have h7 (a : Fˣ) : a ^ 7 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [Nat.card_units, card_extensionField] at h
    change a ^ 7 = 1 at h
    exact h
  have hcoords : (![t, 1, frobenius P t, frobenius P (frobenius P t)] : TorusCoordinates.Coordinates P) ^ 7 = 1 := by
    funext i
    exact h7 _
  have hsplit : elementaryInclusion P ((torusElementary P hP .arms t) ^ 7) = 1 := by
    rw [map_pow, he, ← map_pow, hcoords, map_one]
  have hel : (torusElementary P hP .arms t) ^ 7 = 1 :=
    (elementaryInclusion_injective P) (hsplit.trans (map_one _).symm)
  simpa only [torusActor, map_pow, map_one] using congrArg (toCarrier P) hel

/-- The chosen lift has order dividing seven, because the Levi map is a section. -/
theorem armsTorusLift_seventh_power (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (t : Fˣ) : (armsTorusLift hf hk t) ^ 7 = 1 := by
  have h : (⟨torusActor P hP .arms t, torusActor_mem_levi P hP .arms t⟩ : levi P .arms) ^ 7 = 1 :=
    Subtype.ext (torus_seventh_power t)
  change (armsSection f hf hk _) ^ 7 = 1
  rw [← map_pow, h, map_one]

/-- Every lift of an arms torus actor fixes each additive long section exactly. -/
theorem long_fixed (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (t : Fˣ) (z : E)
    (hz : f z = torusActor P hP .arms t) (i : Fin 3) (a : fixedField P) :
    z * L.longRoot i (.ofAdd a) * z⁻¹ = L.longRoot i (.ofAdd a) := by
  let v := armsTorusLift hf hk t
  let x := L.longRoot i (.ofAdd a)
  have hx2 : x ^ 2 = 1 := by
    change (L.longRoot i (.ofAdd a)) ^ 2 = 1
    rw [← map_pow]
    have h : (Multiplicative.ofAdd a) ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change a + a = 0
      apply Subtype.ext
      exact CharTwo.add_self_eq_zero (a.val : GaloisField 2 3)
    rw [h, map_one]
  have hkx : ⁅v, x⁆ ∈ Subgroup.center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    change ⁅f (armsTorusLift hf hk t), f (L.longRoot i (.ofAdd a))⁆ = 1
    rw [armsTorusLift_project, L.project_long, commutatorElement_def,
      torus_fixes_longs P hP t (small_norm t), mul_inv_cancel]
  have hconj (y : E) : y * ⁅v, x⁆ * y⁻¹ = ⁅v, x⁆ := by
    rw [Subgroup.mem_center_iff.mp hkx y, mul_inv_cancel_right]
  have hpow (n : ℕ) : ⁅v ^ n, x⁆ = ⁅v, x⁆ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_eq_conj_mul, hconj, ih, pow_succ']
  have hk7 : ⁅v, x⁆ ^ 7 = 1 := by
    rw [← hpow, armsTorusLift_seventh_power]
    simp
  have hk2 : ⁅v, x⁆ ^ 2 = 1 := by
    have h := commutatorElement_mul_right_eq_mul_conj v x x
    rw [← pow_two, hx2, commutatorElement_one_right] at h
    rw [mul_assoc, mul_assoc, ← mul_assoc x, hconj] at h
    simpa only [pow_two] using h.symm
  have hk1 : ⁅v, x⁆ = 1 := by
    have h : (7 : ℕ) = 2 * 3 + 1 := rfl
    rw [h, pow_add, pow_mul, hk2] at hk7
    simpa using hk7
  have he : Commute z x := commutatorElement_eq_one_iff_commute.mp
    ((CentralExtension.commutator_eq_of_image_eq f hk
      (hz.trans (armsTorusLift_project hf hk t).symm) rfl).trans hk1)
  change z * x * z⁻¹ = x
  rw [he.eq, mul_inv_cancel_right]

/-- Equivariance under all actual cubic-field arms torus actors. -/
def ShortTorusNormalized (L : RootSections 1 Nat.zero_lt_one f) : Prop :=
  ∀ (t : Fˣ) (z : E), f z = torusActor P hP .arms t →
    ∀ (i : Fin 3) (x : F),
      z * L.shortRoot i (.ofAdd x) * z⁻¹ =
        L.shortRoot i (.ofAdd (shortWeight t i * x))

private theorem normalized_short_exists
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (i : Fin 3) :
    ∃ s : Multiplicative F →* E,
      (∀ x, f (s (.ofAdd x)) = short P hP i x) ∧
      ∀ (t : Fˣ) (z : E), f z = torusActor P hP .arms t → ∀ x : F,
        z * s (.ofAdd x) * z⁻¹ = s (.ofAdd (shortWeight t i * x)) := by
  obtain ⟨t, c, hc, ht, _⟩ := small_torus_motion i
  let v := armsTorusLift hf hk t
  have hv : f v = torusActor P hP .arms t := armsTorusLift_project hf hk t
  let w := L.shortRoot i
  let s : F → E := fun x => ⁅v, w (.ofAdd ((c-1)⁻¹*x))⁆
  have hd : c-1 ≠ 0 := sub_ne_zero.mpr hc
  have hs (x : F) : f (s x) = short P hP i x := by
    change f ⁅v, w (.ofAdd ((c-1)⁻¹*x))⁆ = _
    rw [map_commutatorElement, hv, commutatorElement_def, L.project_short, ht]
    rw [← L.project_short i (c*((c-1)⁻¹*x)),
      ← L.project_short i ((c-1)⁻¹*x), ← map_inv, ← map_mul]
    change f (w (.ofAdd (c*((c-1)⁻¹*x))) * (w (.ofAdd ((c-1)⁻¹*x)))⁻¹) = _
    rw [← map_inv, ← map_mul]
    change f (w (.ofAdd (c*((c-1)⁻¹*x) + -((c-1)⁻¹*x)))) = _
    have he : c*((c-1)⁻¹*x) + -((c-1)⁻¹*x) = x := by
      calc
        _ = (c-1)*((c-1)⁻¹*x) := by ring
        _ = x := mul_inv_cancel_left₀ hd x
    rw [he]
    exact L.project_short i x
  have hcomm (x y : F) : Commute (w (.ofAdd x)) (s y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl
      ((hs y).trans (L.project_short i y).symm)]
    exact ((Commute.all (.ofAdd x) (.ofAdd y)).map w).commutator_eq
  have hsadd (x y : F) : s (x+y) = s x * s y := by
    dsimp [s]
    rw [mul_add, ofAdd_add, map_mul, commutatorElement_mul_right_eq_mul_conj]
    change s x * w (.ofAdd ((c-1)⁻¹*x)) * s y * (w (.ofAdd ((c-1)⁻¹*x)))⁻¹ = _
    rw [mul_assoc (s x), (hcomm _ y).eq, ← mul_assoc,
      mul_assoc (s x * s y), mul_inv_cancel, mul_one]
  refine ⟨{ toFun := fun x => s x.toAdd
            map_one' := by simp [s]
            map_mul' := fun x y => hsadd x.toAdd y.toAdd }, hs, ?_⟩
  intro u z hz x
  change z * ⁅v, w (.ofAdd ((c-1)⁻¹*x))⁆ * z⁻¹ =
    ⁅v, w (.ofAdd ((c-1)⁻¹*(shortWeight u i*x)))⁆
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hz, hv,
      (torusActor_commute P hP .arms .arms u t).eq, mul_inv_cancel_right]
  · rw [map_mul, map_mul, map_inv, hz, L.project_short, L.project_short, short_scaling]
    congr 1
    ring

/-- Construct equivariant short sections and keep every long section. -/
theorem exists_shortTorusNormalized
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) :
    ∃ M : RootSections 1 Nat.zero_lt_one f,
      L.longRoot = M.longRoot ∧ ShortTorusNormalized M := by
  choose s hs he using normalized_short_exists hf hk L
  exact ⟨{ shortRoot := s
           longRoot := L.longRoot
           project_short := hs
           project_long := L.project_long }, rfl, fun t z hz i => he i t z hz⟩

/-- The lower normalization may use these sections without losing its upper inputs. -/
theorem exists_shortTorusNormalized_of_upper
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L)
    (hu : UpperRelations L) :
    ∃ M : RootSections 1 Nat.zero_lt_one f,
      L.longRoot = M.longRoot ∧ ShortTorusNormalized M ∧
        CommutingPairs M ∧ UpperRelations M := by
  obtain ⟨M, hl, hm⟩ := exists_shortTorusNormalized hf hk L
  exact ⟨M, hl, hm, (commutingPairs_iff hk L M).mp hcomm, hu.of_same_long hk hl⟩

/-- The complete arms action on the six chosen sections. -/
def ArmsTorusNormalized (L : RootSections 1 Nat.zero_lt_one f) : Prop :=
  ShortTorusNormalized L ∧
    ∀ (t : Fˣ) (z : E), f z = torusActor P hP .arms t →
      ∀ (i : Fin 3) (x : fixedField P),
        z * L.longRoot i (.ofAdd x) * z⁻¹ = L.longRoot i (.ofAdd x)

/-- The common normalized family needed by both lower polynomial calculations. -/
theorem exists_armsTorusNormalized_of_upper
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hcomm : CommutingPairs L)
    (hu : UpperRelations L) :
    ∃ M : RootSections 1 Nat.zero_lt_one f,
      L.longRoot = M.longRoot ∧ ArmsTorusNormalized M ∧
        CommutingPairs M ∧ UpperRelations M := by
  obtain ⟨M, hl, ht, hc, hu⟩ := exists_shortTorusNormalized_of_upper hf hk L hcomm hu
  exact ⟨M, hl, ⟨ht, long_fixed hf hk M⟩, hc, hu⟩

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
