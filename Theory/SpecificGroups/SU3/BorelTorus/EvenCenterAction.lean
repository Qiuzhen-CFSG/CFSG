module
public import Theory.SpecificGroups.SU3.BorelTorus.Basic
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Residual

/-!
# The binary unitary Borel action on central root coordinates

The upper-right root coordinate is the additive fixed field. The full torus
acts on it by the inverse norm, whose image is the entire multiplicative
fixed field. Thus the action is transitive on nonzero central coordinates,
and its pointwise kernel consists exactly of the norm-one parameters.
All actions here use the actual projective special unitary matrices; in
particular no injectivity of the projective torus parametrization is assumed.

The central-coordinate definitions follow the same matrix construction as
`Chapter16/.../TorusConstruction/Unitary/Omega`, placed here at the intrinsic
group layer for independent consumers. The root injection is reused from
`EvenInnerCentralizers.Residual`.

Source: Huppert II.10.12; Aschbacher–Smith, combined manuscript (1 March
2004), the rank-one argument in E.6.8(1), printed pp.247–248.
-/

@[expose] public section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

abbrev fixedField := FixedBy.subfield E J.conj

theorem fixedField_mem (b : fixedField J) : J.conj (b : E) = b := b.property

def inverseNorm : Eˣ →* (fixedField J)ˣ where
  toFun k := Units.mk0
    ⟨((k : E) * J.conj (k : E))⁻¹, by
      change J.conj _ = _
      rw [map_inv₀, map_mul, J.conj_involutive, mul_comm]⟩
    (by
      intro h
      have h' := congrArg (fun x : fixedField J => (x : E)) h
      exact inv_ne_zero (mul_ne_zero k.ne_zero ((map_ne_zero J.conj).mpr k.ne_zero)) h')
  map_one' := by apply Units.ext; apply Subtype.ext; simp
  map_mul' k l := by
    apply Units.ext
    apply Subtype.ext
    change (((k : E) * l) * J.conj ((k : E) * l))⁻¹ =
      ((k : E) * J.conj (k : E))⁻¹ * ((l : E) * J.conj (l : E))⁻¹
    rw [map_mul, mul_inv, mul_inv, mul_inv, mul_inv]
    ring

theorem inverseNorm_val (k : Eˣ) :
    ((inverseNorm J k : fixedField J) : E) = ((k : E) * J.conj (k : E))⁻¹ := rfl

theorem inverseNorm_surjective [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Function.Surjective (inverseNorm J) := by
  intro u
  have hu : ((u : fixedField J) : E) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  obtain ⟨k, hk, hnorm⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed
    (((u : fixedField J) : E)⁻¹) (by rw [map_inv₀, fixedField_mem])
    (inv_ne_zero hu)
  refine ⟨Units.mk0 k hk, ?_⟩
  apply Units.ext
  apply Subtype.ext
  change (k * J.conj k)⁻¹ = _
  rw [hnorm, inv_inv]

variable [CharP E 2]

/-- The additive fixed field in the upper-right Hermitian root coordinate. -/
def centralCoord : Multiplicative (fixedField J) →* hermitianUnipotentCoord J where
  toFun b := ⟨(0, (b.toAdd : E)), by
    simp only [zero_mul, fixedField_mem, CharTwo.add_self_eq_zero]⟩
  map_one' := rfl
  map_mul' b c := by
    apply Subtype.ext
    apply Prod.ext
    · exact (zero_add 0).symm
    · change (b.toAdd : E) + c.toAdd =
        (b.toAdd : E) + c.toAdd - 0 * J.conj 0
      simp

theorem centralCoord_injective : Function.Injective (centralCoord J) := by
  intro b c he
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he

theorem centralCoord_mem_center (b : Multiplicative (fixedField J)) :
    centralCoord J b ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change z.val.1 + 0 = 0 + z.val.1
    simp
  · change z.val.2 + (b.toAdd : E) - z.val.1 * J.conj 0 =
      (b.toAdd : E) + z.val.2 - 0 * J.conj z.val.1
    simp [add_comm]

theorem torus_centralCoord (k : Eˣ) (b : Multiplicative (fixedField J)) :
    hermitianTorusAction J k (centralCoord J b) =
      centralCoord J (Multiplicative.ofAdd ((inverseNorm J k : fixedField J) * b.toAdd)) := by
  apply Subtype.ext
  apply Prod.ext
  · change 0 * (k : E) * (J.conj (k : E))⁻¹ ^ 2 = 0
    simp
  · change (b.toAdd : E) * (J.conj (k : E))⁻¹ * (k : E)⁻¹ =
      ((k : E) * J.conj (k : E))⁻¹ * (b.toAdd : E)
    rw [mul_inv]
    ring

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

def centralMap : Multiplicative (fixedField J) →*
    ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianUnipotentPSU J hJ).comp (centralCoord J)

def centralImage : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (centralMap J hJ).range

theorem centralMap_injective : Function.Injective (centralMap J hJ) :=
  (EvenInner.root_injective J hJ).comp (centralCoord_injective J)

theorem centralImage_le_root : centralImage J hJ ≤ projectiveRoot J hJ := by
  rintro _ ⟨b, rfl⟩
  exact ⟨centralCoord J b, rfl⟩

theorem centralImage_le_center : centralImage J hJ ≤
    (center (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype := by
  rintro _ ⟨b, rfl⟩
  refine ⟨⟨centralMap J hJ b, centralImage_le_root J hJ ⟨b, rfl⟩⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  rintro ⟨_, z, rfl⟩
  apply Subtype.ext
  exact (map_mul (hermitianUnipotentPSU J hJ) _ _).symm.trans
    ((congrArg (hermitianUnipotentPSU J hJ)
      (mem_center_iff.mp (centralCoord_mem_center J b) z)).trans
      (map_mul (hermitianUnipotentPSU J hJ) _ _))

theorem root_centralizes : projectiveRoot J hJ ≤
    centralizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rintro _ ⟨z, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨b, rfl⟩
  change hermitianUnipotentPSU J hJ (centralCoord J b) * hermitianUnipotentPSU J hJ z =
    hermitianUnipotentPSU J hJ z * hermitianUnipotentPSU J hJ (centralCoord J b)
  rw [← map_mul, ← map_mul]
  exact congrArg _ (mem_center_iff.mp (centralCoord_mem_center J b) z).symm

theorem centralImage_card [Finite E] {q : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (centralImage J hJ) = q := by
  change Nat.card (centralMap J hJ).range = q
  rw [← Nat.card_congr (MonoidHom.ofInjective (centralMap_injective J hJ)).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  exact hfixed

/-- The actual projective torus action retains the scalar quotient. -/
theorem projective_torus_central (k : Eˣ) (b : Multiplicative (fixedField J)) :
    hermitianTorusPSU J hJ k * centralMap J hJ b * (hermitianTorusPSU J hJ k)⁻¹ =
      centralMap J hJ (Multiplicative.ofAdd ((inverseNorm J k : fixedField J) * b.toAdd)) := by
  change hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ (centralCoord J b) * _ = _
  rw [EvenInner.projective_torus_action, torus_centralCoord]
  rfl

/-- Norm surjectivity gives transitivity on the nonidentity central root elements. -/
theorem central_transitive [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (b c : fixedField J) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ k : Eˣ, hermitianTorusPSU J hJ k * centralMap J hJ (.ofAdd b) *
        (hermitianTorusPSU J hJ k)⁻¹ = centralMap J hJ (.ofAdd c) := by
  obtain ⟨k, hk⟩ := inverseNorm_surjective J hcard hfixed (Units.mk0 (c / b) (div_ne_zero hc hb))
  refine ⟨k, ?_⟩
  rw [projective_torus_central, hk]
  change centralMap J hJ (.ofAdd ((c / b) * b)) = _
  rw [div_mul_cancel₀ _ hb]

/-- The pointwise kernel of the full torus action is exactly the norm-one subgroup. -/
theorem torus_centralizer_iff (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈
      centralizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
        inverseNorm J k = 1 := by
  constructor
  · intro hk
    have he := mem_centralizer_iff.mp hk (centralMap J hJ (.ofAdd 1)) ⟨_, rfl⟩
    have ha := projective_torus_central J hJ k (.ofAdd 1)
    rw [← he, mul_inv_cancel_right] at ha
    have hb := centralMap_injective J hJ ha
    apply Units.ext
    have hh := (congrArg Multiplicative.toAdd hb).symm
    change (inverseNorm J k : fixedField J) * 1 = 1 at hh
    simpa only [mul_one, Units.val_one] using hh
  · intro hk
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, rfl⟩
    have ha := projective_torus_central J hJ k b
    rw [hk] at ha
    simp only [Units.val_one, one_mul] at ha
    exact (mul_inv_eq_iff_eq_mul.mp ha).symm

/-- The full torus normalizes the central root group. -/
theorem torus_normalizes : projectiveTorus J hJ ≤
    normalizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hc (k : Eˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J)
      (hx : x ∈ centralImage J hJ) :
      hermitianTorusPSU J hJ k * x * (hermitianTorusPSU J hJ k)⁻¹ ∈ centralImage J hJ := by
    obtain ⟨b, rfl⟩ := hx
    rw [projective_torus_central]
    exact ⟨_, rfl⟩
  rintro _ ⟨k, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc k x
  · intro hx
    have hh := hc k⁻¹ _ hx
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using hh

theorem borel_normalizes : projectiveBorel J hJ ≤
    normalizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  sup_le ((root_centralizes J hJ).trans (centralizer_le_normalizer _))
    (torus_normalizes J hJ)

/-- An invariant subgroup of the central root group is zero or the whole group. -/
theorem central_irreducible [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ centralImage J hJ)
    (hnorm : projectiveTorus J hJ ≤ normalizer (A : Set _)) :
    A = ⊥ ∨ A = centralImage J hJ := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  apply le_antisymm hA
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨b, hb⟩ := hA a.property
  have hb0 : b.toAdd ≠ 0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [← hb, show b = 1 from Multiplicative.toAdd.injective he, map_one]
    rfl
  rintro _ ⟨c, rfl⟩
  by_cases hc0 : c.toAdd = 0
  · rw [show c = 1 from Multiplicative.toAdd.injective hc0, map_one]
    exact A.one_mem
  obtain ⟨k, hk⟩ := central_transitive J hJ hcard hfixed b.toAdd c.toAdd hb0 hc0
  have hm := (mem_normalizer_iff.mp (hnorm ⟨k, rfl⟩) (a : _)).mp a.property
  change hermitianTorusPSU J hJ k * centralMap J hJ b *
    (hermitianTorusPSU J hJ k)⁻¹ = centralMap J hJ c at hk
  rwa [← hb, hk] at hm

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction
