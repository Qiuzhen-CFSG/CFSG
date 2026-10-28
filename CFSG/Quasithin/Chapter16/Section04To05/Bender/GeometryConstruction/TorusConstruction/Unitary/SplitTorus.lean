module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction.Unitary.Omega

/-!
# The split diagonal torus on the unitary omega layer

The fixed-field units give a cyclic subgroup of order q − 1 in the actual
projective unitary group. Its conjugation on the central root coordinate is
multiplication by the inverse square, so it is regular on nonzero coordinates
in characteristic two.

Source: Aschbacher–Smith, Proposition 16.5.1, printed p.1194.
-/

@[expose] public section

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

/-- The fixed-field units, as units of the matrix field. -/
def splitUnits : (fixedField J)ˣ →* Eˣ :=
  Units.map (fixedField J).subtype.toMonoidHom

theorem splitUnits_fixed (k : (fixedField J)ˣ) :
    J.conj (splitUnits J k : E) = (splitUnits J k : E) :=
  (k : fixedField J).property

/-- The split diagonal torus map, preserving literal matrix conjugation. -/
def splitMap : (fixedField J)ˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp (splitUnits J)

def splitImage : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (splitMap J hJ).range

private instance [Finite E] : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Quotient.finite _

variable [CharP E 2]

theorem splitMap_injective : Function.Injective (splitMap J hJ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro k hk
  have hh := (BorelTorus.projective_eq_one_iff J hJ (splitUnits J k)).mp hk
  have hnorm : J.conj (splitUnits J k : E) = (splitUnits J k : E)⁻¹ := hh.1
  rw [splitUnits_fixed] at hnorm
  have hs : (splitUnits J k : E) ^ 2 = 1 ^ 2 := by
    rw [pow_two, one_pow]
    calc
      _ = (splitUnits J k : E)⁻¹ * (splitUnits J k : E) := congrArg (fun x => x * (splitUnits J k : E)) hnorm
      _ = 1 := inv_mul_cancel₀ (Units.ne_zero _)
  have he := CharTwo.sq_injective hs
  apply mem_bot.mpr
  apply Units.ext
  apply Subtype.ext
  exact he

theorem splitImage_card [Finite E] {q : ℕ}
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (splitImage J hJ) = q - 1 := by
  change Nat.card (splitMap J hJ).range = q - 1
  rw [← Nat.card_congr (MonoidHom.ofInjective (splitMap_injective J hJ)).toEquiv,
    Nat.card_units]
  exact congrArg (fun n => n - 1) hfixed

omit [CharP E 2] in
theorem splitImage_cyclic [Finite E] : IsCyclic (splitImage J hJ) :=
  isCyclic_of_surjective (splitMap J hJ).rangeRestrict
    (splitMap J hJ).rangeRestrict_surjective

/-- The split torus's weight on omega is the inverse square over the fixed field. -/
theorem split_action (k : (fixedField J)ˣ) (b : Multiplicative (fixedField J)) :
    MulAut.conj (splitMap J hJ k) (centralMap J hJ b) =
      centralMap J hJ (Multiplicative.ofAdd (b.toAdd * (k : fixedField J)⁻¹ ^ 2)) := by
  change hermitianTorusPSU J hJ (splitUnits J k) *
    hermitianUnipotentPSU J hJ (centralCoord J b) *
    (hermitianTorusPSU J hJ (splitUnits J k))⁻¹ = _
  rw [EvenInner.projective_torus_action]
  change hermitianUnipotentPSU J hJ _ = hermitianUnipotentPSU J hJ (centralCoord J _)
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianTorusAction_fst]
    change 0 * _ * _ = 0
    simp
  · rw [hermitianTorusAction_snd, splitUnits_fixed]
    change (b.toAdd : E) * ((k : fixedField J) : E)⁻¹ * ((k : fixedField J) : E)⁻¹ =
      (b.toAdd : E) * (((k : fixedField J) : E)⁻¹ ^ 2)
    ring

private theorem scalar_regular [Finite E] (b c : fixedField J) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃! k : (fixedField J)ˣ, b * (k : fixedField J)⁻¹ ^ 2 = c := by
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective
    (CharTwo.sq_injective : Function.Injective (fun x : fixedField J => x ^ 2)) (b / c)
  change a ^ 2 = b / c at ha
  have ha0 : a ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide : 2 ≠ 0)] at ha
    exact div_ne_zero hb hc ha.symm
  have hsol : b * a⁻¹ ^ 2 = c := by
    field_simp
    rw [ha]
    field_simp
  refine ⟨Units.mk0 a ha0, hsol, ?_⟩
  intro k hk
  apply Units.ext
  apply inv_injective
  apply CharTwo.sq_injective
  exact mul_left_cancel₀ hb (hk.trans hsol.symm)

/-- Literal conjugation is sharply transitive on the nonidentity omega layer. -/
theorem split_regular [Finite E]
    {v w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hv : v ∈ centralImage J hJ) (hv1 : v ≠ 1)
    (hw : w ∈ centralImage J hJ) (hw1 : w ≠ 1) :
    ∃! x : splitImage J hJ, MulAut.conj (x : ProjectiveSpecialUnitaryMatrixGroup J) v = w := by
  obtain ⟨b, rfl⟩ := hv
  obtain ⟨c, rfl⟩ := hw
  have hb : b.toAdd ≠ 0 := by
    intro he
    apply hv1
    have : b = 1 := Multiplicative.toAdd.injective he
    rw [this, map_one]
  have hc : c.toAdd ≠ 0 := by
    intro he
    apply hw1
    have : c = 1 := Multiplicative.toAdd.injective he
    rw [this, map_one]
  obtain ⟨k, hk, huniq⟩ := scalar_regular J b.toAdd c.toAdd hb hc
  refine ⟨⟨splitMap J hJ k, ⟨k, rfl⟩⟩, ?_, ?_⟩
  · change MulAut.conj (splitMap J hJ k) (centralMap J hJ b) = _
    rw [split_action, hk]
    rfl
  · rintro ⟨_, l, rfl⟩ hl
    apply Subtype.ext
    apply congrArg (splitMap J hJ)
    apply huniq
    rw [split_action] at hl
    exact congrArg Multiplicative.toAdd ((centralMap_injective J hJ) hl)

omit [CharP E 2] in
/-- Every fixed-field torus element normalizes the full Hermitian root group. -/
theorem split_normalizes_root [Finite E] : splitImage J hJ ≤
    normalizer (BorelTorus.projectiveRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rintro _ ⟨k, rfl⟩
  apply mem_normalizer_fintype
  rintro _ ⟨z, rfl⟩
  change hermitianTorusPSU J hJ (splitUnits J k) * hermitianUnipotentPSU J hJ z *
    (hermitianTorusPSU J hJ (splitUnits J k))⁻¹ ∈ _
  rw [EvenInner.projective_torus_action]
  exact ⟨_, rfl⟩

/-- In particular the torus preserves the central coordinate layer. -/
theorem split_normalizes_central [Finite E] : splitImage J hJ ≤
    normalizer (centralImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rintro _ ⟨k, rfl⟩
  apply mem_normalizer_fintype
  rintro _ ⟨b, rfl⟩
  change MulAut.conj (splitMap J hJ k) (centralMap J hJ b) ∈ _
  rw [split_action]
  exact ⟨_, rfl⟩

/-- No nonidentity omega element is fixed by the whole split torus. -/
theorem split_fixed_eq_bot [Finite E] (hlarge : 2 < Nat.card (fixedField J)) :
    centralImage J hJ ⊓ centralizer (splitImage J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊥ := by
  have : Nontrivial (splitImage J hJ) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [splitImage_card J hJ (q := Nat.card (fixedField J)) rfl]
    omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : splitImage J hJ)
  apply eq_bot_iff.mpr
  intro u hu
  apply mem_bot.mpr
  by_contra hu1
  have hxu : MulAut.conj (x : ProjectiveSpecialUnitaryMatrixGroup J) u = u := by
    have hc := mem_centralizer_iff.mp hu.2 x x.property
    change (x : ProjectiveSpecialUnitaryMatrixGroup J) * u * (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ = u
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hreg := split_regular J hJ hu.1 hu1 hu.1 hu1
  exact hx (hreg.unique hxu (by simp))

/-- A single nontrivial torus weight generates the whole omega layer by commutators. -/
theorem split_commutator [Finite E] (hlarge : 2 < Nat.card (fixedField J)) :
    ⁅centralImage J hJ, splitImage J hJ⁆ = centralImage J hJ := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (split_normalizes_central J hJ))
  have : Nontrivial (fixedField J)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : (fixedField J)ˣ)
  have hs : (a : fixedField J)⁻¹ ^ 2 ≠ 1 := by
    intro he
    have hsq : (a : fixedField J)⁻¹ ^ 2 = 1 ^ 2 := by simpa only [one_pow] using he
    have hi : (a : fixedField J)⁻¹ = 1 := CharTwo.sq_injective hsq
    apply ha
    apply Units.ext
    simpa only [inv_inv, inv_one, Units.val_one] using congrArg Inv.inv hi
  rintro _ ⟨b, rfl⟩
  let c : Multiplicative (fixedField J) :=
    Multiplicative.ofAdd (b.toAdd / ((a : fixedField J)⁻¹ ^ 2 - 1))
  have hc := commutator_mem_commutator (H₁ := splitImage J hJ) (H₂ := centralImage J hJ)
    (show splitMap J hJ a ∈ splitImage J hJ from ⟨a, rfl⟩)
    (show centralMap J hJ c ∈ centralImage J hJ from ⟨c, rfl⟩)
  rw [commutator_comm] at hc
  have he : ⁅splitMap J hJ a, centralMap J hJ c⁆ = centralMap J hJ b := by
    rw [commutatorElement_def]
    change MulAut.conj (splitMap J hJ a) (centralMap J hJ c) * (centralMap J hJ c)⁻¹ = _
    rw [split_action, ← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    change c.toAdd * (a : fixedField J)⁻¹ ^ 2 + -c.toAdd = b.toAdd
    calc
      _ = c.toAdd * ((a : fixedField J)⁻¹ ^ 2 - 1) := by ring
      _ = b.toAdd := div_mul_cancel₀ _ (sub_ne_zero.mpr hs)
  rwa [he] at hc

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Unitary
