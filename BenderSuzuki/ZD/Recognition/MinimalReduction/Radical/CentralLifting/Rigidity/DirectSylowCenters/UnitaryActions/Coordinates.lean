module

public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers
public import Theory.SpecificGroups.SU3.BinaryRootFrattini

/-!
# Coordinates for the unitary Sylow-center action criterion

The actual upper-root subgroup of PSU₃ is identified with its Hermitian
Heisenberg coordinates. The actual diagonal torus lies in its normalizer,
acts transitively on the nonidentity center, and has odd period q² - 1.
The derived subgroup equals the center by Huppert's matrix description.

Every element in the kernel of the first-coordinate map is a square, by
norm surjectivity. Binary bihomomorphisms therefore descend in both arguments
to the additive coefficient field. This descent intertwines the literal
normalizer action with multiplication by k/conj(k)²; no projective torus
injection is assumed. The scalar vanishing assertion remains explicit here.

Source: Huppert II.10.4 and II.10.12; the direct proof of the Sylow-center
conclusion of GLS4, Chapter 4, Lemma 2.8(c).
-/

public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
namespace BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions
variable {K : Type*} [Field K] (J : HermitianForm 3 K)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The genuine projective root map is injective on Hermitian coordinates. -/
noncomputable def rootEquiv : hermitianUnipotentCoord J ≃* projectiveRoot J hJ :=
  MonoidHom.ofInjective (EvenInner.root_injective J hJ)

theorem torus_mem_normalizer (k : Kˣ) : hermitianTorusPSU J hJ k ∈
    normalizer (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hc (l : Kˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J)
      (hx : x ∈ projectiveRoot J hJ) :
      hermitianTorusPSU J hJ l * x * (hermitianTorusPSU J hJ l)⁻¹ ∈
        projectiveRoot J hJ := by
    obtain ⟨z, rfl⟩ := hx
    rw [EvenInner.projective_torus_action]
    exact ⟨_, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc k x
  · intro hx
    have hh := hc k⁻¹ _ hx
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The actual torus homomorphism, with codomain restricted to the root normalizer. -/
def torusNormalizer : Kˣ →*
    normalizer (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) where
  toFun k := ⟨hermitianTorusPSU J hJ k, torus_mem_normalizer J hJ k⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' k l := Subtype.ext (map_mul _ k l)

theorem torusNormalizer_action (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k)
        (rootEquiv J hJ z) = rootEquiv J hJ (hermitianTorusAction J k z) := by
  apply Subtype.ext
  exact EvenInner.projective_torus_action J hJ k z

theorem root_commutator_eq_center [Finite K] {q : ℕ}
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    _root_.commutator (projectiveRoot J hJ) = center (projectiveRoot J hJ) := by
  obtain ⟨_, _, _, _, _, _,
    ⟨R, _, _, _, _, _, _, _, _, hcomm, _, _, _, ⟨e, he⟩, _⟩, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hJ
  have heq (z : hermitianUnipotentCoord J) :
      (e z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hp⟩ := he z
    apply Subtype.ext
    rw [hp, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  have hR : R = projectiveRoot J hJ := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, (heq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← heq]
      exact (e z).property
  subst R
  exact hcomm

variable [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card K = (2^n)^2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2^n)

include hn hcard hfixed in
theorem center_transitive (z w : center (projectiveRoot J hJ)) (hz : z ≠ 1) (hw : w ≠ 1) :
    ∃ h : normalizer (projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      centerCongr ((projectiveRoot J hJ).normalizerMonoidHom h) z = w := by
  have hzmem : z.val.val ∈ centralImage J hJ := by
    rw [← NormalizedRootCentralizers.root_center J (by omega : 1 < n) hcard hfixed hJ]
    exact ⟨z.val, z.property, rfl⟩
  have hwmem : w.val.val ∈ centralImage J hJ := by
    rw [← NormalizedRootCentralizers.root_center J (by omega : 1 < n) hcard hfixed hJ]
    exact ⟨w.val, w.property, rfl⟩
  obtain ⟨b, hb⟩ := hzmem
  obtain ⟨c, hc⟩ := hwmem
  have hb0 : b.toAdd ≠ 0 := by
    intro he
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    rw [← hb, show b = 1 from he, map_one]
    rfl
  have hc0 : c.toAdd ≠ 0 := by
    intro he
    apply hw
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, show c = 1 from he, map_one]
    rfl
  obtain ⟨k, hk⟩ := central_transitive J hJ hcard hfixed b.toAdd c.toAdd hb0 hc0
  refine ⟨torusNormalizer J hJ k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change hermitianTorusPSU J hJ k * z.val.val * (hermitianTorusPSU J hJ k)⁻¹ = w.val.val
  rw [← hb, ← hc]
  exact hk

include hn hcard hfixed in
theorem center_fixed (k : Kˣ) (hk : inverseNorm J k ≠ 1)
    (z : projectiveRoot J hJ) (hz : z ∈ center (projectiveRoot J hJ))
    (hfix : (projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) z = z) :
    z = 1 := by
  have hzmem : z.val ∈ centralImage J hJ := by
    rw [← NormalizedRootCentralizers.root_center J (by omega : 1 < n) hcard hfixed hJ]
    exact ⟨z, hz, rfl⟩
  obtain ⟨b, hb⟩ := hzmem
  have he := congrArg Subtype.val hfix
  change hermitianTorusPSU J hJ k * z.val * (hermitianTorusPSU J hJ k)⁻¹ = z.val at he
  rw [← hb, projective_torus_central] at he
  have hscalar := congrArg Multiplicative.toAdd (centralMap_injective J hJ he)
  have hb0 : b.toAdd = 0 := by
    by_contra hb0
    apply hk
    apply Units.ext
    exact mul_right_cancel₀ hb0 (hscalar.trans (one_mul _).symm)
  apply Subtype.ext
  rw [← hb, show b = 1 from hb0, map_one]
  rfl

open BinaryRootFrattini

include hcard hfixed in
theorem first_kernel_le_hom_ker {A : Type*} [Group A] (hsq : ∀ a : A, a ^ 2 = 1)
    (f : hermitianUnipotentCoord J →* A) : (firstCoordinate J).ker ≤ f.ker := by
  intro z hz
  have hz0 : z.val.1 = 0 := congrArg Multiplicative.toAdd hz
  by_cases hb : z.val.2 = 0
  · have he : z = 1 := Subtype.ext (Prod.ext hz0 hb)
    exact he ▸ f.ker.one_mem
  have hfix : J.conj z.val.2 = z.val.2 := by
    have hp := z.property
    rw [hz0, zero_mul, add_zero] at hp
    exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
  obtain ⟨a, _, ha⟩ := huppert_II_10_4_norm_surjective J (2^n) hcard hfixed z.val.2 hfix hb
  obtain ⟨w, hw⟩ := firstCoordinate_surjective J hcard hfixed (Multiplicative.ofAdd a)
  have hw0 : w.val.1 = a := congrArg Multiplicative.toAdd hw
  have hs : w ^ 2 = z := by
    apply Subtype.ext
    rw [EvenInner.square_coordinates, hw0, ha]
    exact Prod.ext hz0.symm rfl
  change f z = 1
  rw [← hs, map_pow, hsq]

/-- Descent through the surjective first coordinate for an exponent-two target. -/
noncomputable def descendHom {A : Type*} [Group A] (hsq : ∀ a : A, a ^ 2 = 1)
    (f : hermitianUnipotentCoord J →* A) : Multiplicative K →* A :=
  (firstCoordinate J).liftOfSurjective (firstCoordinate_surjective J hcard hfixed)
    ⟨f, first_kernel_le_hom_ker J hcard hfixed hsq f⟩

theorem descendHom_first {A : Type*} [Group A] (hsq : ∀ a : A, a ^ 2 = 1)
    (f : hermitianUnipotentCoord J →* A) (z : hermitianUnipotentCoord J) :
    descendHom J hcard hfixed hsq f (firstCoordinate J z) = f z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem binary_square (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  change (2 : ℕ) • x.toAdd = 0
  rw [two_nsmul]
  exact CharTwo.add_self_eq_zero _

omit [Finite K] [CharP K 2] in
private theorem binary_hom_square (f : hermitianUnipotentCoord J →* Multiplicative (ZMod 2)) :
    f ^ 2 = 1 := by
  ext x
  exact binary_square (f x)

/-- The binary pairing induced on the actual first-coordinate quotient. -/
noncomputable def descendPairing
    (c : hermitianUnipotentCoord J →* (hermitianUnipotentCoord J →* Multiplicative (ZMod 2))) :
    Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)) where
  toFun x := descendHom J hcard hfixed binary_square
    (descendHom J hcard hfixed (binary_hom_square J) c x)
  map_one' := by
    apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := firstCoordinate_surjective J hcard hfixed y
    rw [descendHom_first, map_one]
    rfl
  map_mul' x y := by
    apply MonoidHom.ext
    intro z
    obtain ⟨w, rfl⟩ := firstCoordinate_surjective J hcard hfixed z
    simp only [descendHom_first, map_mul, MonoidHom.mul_apply]

theorem descendPairing_first
    (c : hermitianUnipotentCoord J →* (hermitianUnipotentCoord J →* Multiplicative (ZMod 2)))
    (z w : hermitianUnipotentCoord J) :
    descendPairing J hcard hfixed c (firstCoordinate J z) (firstCoordinate J w) = c z w := by
  change descendHom J hcard hfixed binary_square _ (firstCoordinate J w) = _
  rw [descendHom_first, descendHom_first]

/-- Pull back a pairing along the actual projective root equivalence. -/
noncomputable def rootPairing
    (c : projectiveRoot J hJ →* (projectiveRoot J hJ →* Multiplicative (ZMod 2))) :
    hermitianUnipotentCoord J →* (hermitianUnipotentCoord J →* Multiplicative (ZMod 2)) where
  toFun z := (c (rootEquiv J hJ z)).comp (rootEquiv J hJ).toMonoidHom
  map_one' := by ext w; simp
  map_mul' z w := by ext u; simp

open OddPrimeSylow.NormalizedOuter.Coverage in
omit [Finite K] [CharP K 2] in
theorem first_torus (k : Kˣ) (z : hermitianUnipotentCoord J) :
    firstCoordinate J (hermitianTorusAction J k z) =
      .ofAdd ((torusWeight J k : K) * (firstCoordinate J z).toAdd) := by
  apply Multiplicative.toAdd.injective
  change z.val.1 * (k : K) * (J.conj (k : K))⁻¹ ^ 2 = (torusWeight J k : K) * z.val.1
  rw [torusWeight_val]
  simp only [div_eq_mul_inv, inv_pow]
  ring

open OddPrimeSylow.NormalizedOuter.Coverage in
theorem descendPairing_invariant (k : Kˣ)
    (c : projectiveRoot J hJ →* (projectiveRoot J hJ →* Multiplicative (ZMod 2)))
    (hc : ∀ x y, c ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) x)
        ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) y) = c x y) :
    ∀ a b : Multiplicative K,
      descendPairing J hcard hfixed (rootPairing J hJ c)
        (.ofAdd ((torusWeight J k : K) * a.toAdd))
        (.ofAdd ((torusWeight J k : K) * b.toAdd)) =
      descendPairing J hcard hfixed (rootPairing J hJ c) a b := by
  intro a b
  obtain ⟨z, rfl⟩ := firstCoordinate_surjective J hcard hfixed a
  obtain ⟨w, rfl⟩ := firstCoordinate_surjective J hcard hfixed b
  rw [← first_torus, ← first_torus, descendPairing_first, descendPairing_first]
  change c (rootEquiv J hJ (hermitianTorusAction J k z))
    (rootEquiv J hJ (hermitianTorusAction J k w)) = c (rootEquiv J hJ z) (rootEquiv J hJ w)
  rw [← torusNormalizer_action, ← torusNormalizer_action]
  exact hc _ _

open OddPrimeSylow.NormalizedOuter.Coverage in
include hcard hfixed in
theorem root_pairings_trivial (k : Kˣ)
    (hfield : ∀ b : Multiplicative K →* (Multiplicative K →* Multiplicative (ZMod 2)),
      (∀ x y : Multiplicative K, b (.ofAdd ((torusWeight J k : K) * x.toAdd))
        (.ofAdd ((torusWeight J k : K) * y.toAdd)) = b x y) → b = 1)
    (c : projectiveRoot J hJ →* (projectiveRoot J hJ →* Multiplicative (ZMod 2)))
    (hc : ∀ x y, c ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) x)
        ((projectiveRoot J hJ).normalizerMonoidHom (torusNormalizer J hJ k) y) = c x y) :
    c = 1 := by
  have he := hfield (descendPairing J hcard hfixed (rootPairing J hJ c))
    (descendPairing_invariant J hJ hcard hfixed k c hc)
  apply MonoidHom.ext
  intro x
  apply MonoidHom.ext
  intro y
  obtain ⟨z, rfl⟩ := (rootEquiv J hJ).surjective x
  obtain ⟨w, rfl⟩ := (rootEquiv J hJ).surjective y
  have hh := descendPairing_first J hcard hfixed (rootPairing J hJ c) z w
  rw [he] at hh
  exact hh.symm

omit [Finite K] [CharP K 2] in
include hn hcard in
theorem unit_odd_period (k : Kˣ) : Odd ((2^n)^2 - 1) ∧ k ^ ((2^n)^2 - 1) = 1 := by
  constructor
  · have he : Even ((2^n)^2) :=
      (even_two.pow_of_ne_zero (by omega : n ≠ 0)).pow_of_ne_zero (by decide)
    have hle : 1 ≤ (2^n)^2 := one_le_pow₀ (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ)))
    exact Nat.Even.sub_odd hle he (by decide)
  · have he := pow_card_eq_one' (x := k)
    rwa [Nat.card_units, hcard] at he

end BenderSuzuki.ZD.DirectSylowCenters.UnitaryActions
