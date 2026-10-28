module

public import Theory.Representation.SpecialLinearThreeFrameGeometry.PlaneResidual.Coordinates
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.GroupTheory.PResidual.PrimeSetFiniteImage
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The coordinate plane kernel and its odd-order quotient

The radicals at the first two coordinate lines generate the entire affine
subgroup [[A,v],[0,1]]: their transvections generate SL₂, and their remaining
root elements give all translations. This subgroup is the kernel of the
plane stabilizer's quotient-scalar map. A diagonal torus supplements it
and fixes both marked points.

In characteristic two every radical element squares to one, so every
odd-order quotient kills these generators. Conversely the scalar image
has odd order. Thus the kernel is exactly the relative prime-to-two residual,
including over F₂.

Source: Aschbacher–Smith, G.2.5 proof, printed pp.335–336.
-/

@[expose] public section
noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry.PlaneResidual
open Matrix Subgroup
open scoped MatrixGroups Pointwise
variable {F : Type*} [Field F]

open PSL3.LinearThree

theorem coordinatePlane_stabilizer [Finite F] :
    stabilizer (coordinatePoint (F := F) 0 ⊔ coordinatePoint 1) =
      PSL3.LinearThree.lineParabolicSL F := by
  unfold stabilizer PSL3.LinearThree.lineParabolicSL
  congr 1
  ext v
  exact mem_coordinatePlane v

def coordinatePair : Subgroup SL(3, F) :=
  pointRadical (coordinatePoint 0) ⊔ pointRadical (coordinatePoint 1)

theorem transvection_mem_radical (i j : Fin 3) (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ pointRadical (coordinatePoint i) := by
  constructor
  · intro v
    rw [mem_coordinatePoint]
    intro k hk
    change (((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j c).mulVec v - v) k = 0
    simp [add_mulVec, single_mulVec_eq, Pi.single_eq_of_ne hk]
  · intro v hv
    have hvj := (mem_coordinatePoint _ _).mp hv j hij.symm
    change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j c).mulVec v = v
    simp [add_mulVec, single_mulVec_eq, hvj]

def affineEmbedding : SL2.Affine F →* SL(3, F) :=
  (lineLocalSL F).subtype.comp (lineLocalAffineEquiv F).symm.toMonoidHom

theorem affine_linear_transvection (i j : Fin 2) (hij : i ≠ j) (c : F) :
    affineEmbedding (SemidirectProduct.inr (SpecialLinearGroup.transvection hij c)) =
      SpecialLinearGroup.transvection (show i.castSucc ≠ j.castSucc by simpa using hij) c := by
  apply Subtype.ext
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp_all [affineEmbedding, lineLocalAffineEquiv, affineToLine,
      SpecialLinearGroup.transvection_coe, Matrix.single]

theorem affine_translation (v : Multiplicative (Fin 2 → F)) :
    affineEmbedding (SemidirectProduct.inl v) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (v.toAdd 0) *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (v.toAdd 1) := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [affineEmbedding, lineLocalAffineEquiv, affineToLine,
      SpecialLinearGroup.transvection_coe, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_one, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single]

theorem lineLocal_le_pair : lineLocalSL F ≤ coordinatePair (F := F) := by
  have hlin (a : SL(2, F)) :
      affineEmbedding (SemidirectProduct.inr a) ∈ coordinatePair (F := F) := by
    induction a using SL2.transvection_induction with
    | htransvec i j hij c =>
      rw [affine_linear_transvection]
      fin_cases i
      · exact Subgroup.mem_sup_left (transvection_mem_radical _ _ _ _)
      · exact Subgroup.mem_sup_right (transvection_mem_radical _ _ _ _)
    | hmul a b ha hb =>
      rw [map_mul, map_mul]
      exact Subgroup.mul_mem _ ha hb
  intro g hg
  let a := lineLocalAffineEquiv F ⟨g, hg⟩
  have he : affineEmbedding a = g := congrArg Subtype.val
    ((lineLocalAffineEquiv F).symm_apply_apply ⟨g, hg⟩)
  rw [← he, ← SemidirectProduct.inl_left_mul_inr_right a, map_mul]
  apply Subgroup.mul_mem _ _ (hlin _)
  rw [affine_translation]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (transvection_mem_radical _ _ _ _))
    (Subgroup.mem_sup_right (transvection_mem_radical _ _ _ _))

theorem radical_le_lineLocal (i : Fin 3) (hi : (2 : Fin 3) ≠ i) :
    pointRadical (coordinatePoint (F := F) i) ≤ lineLocalSL F := by
  intro g hg j
  have hh := (mem_coordinatePoint i _).mp (hg.1 (Pi.single j 1)) 2 hi
  change (g.val.mulVec (Pi.single j 1)) 2 - (Pi.single j (1 : F) : Fin 3 → F) 2 = 0 at hh
  simpa [Pi.single_apply, eq_comm] using sub_eq_zero.mp hh

theorem coordinatePair_eq_lineLocal : coordinatePair (F := F) = lineLocalSL F :=
  le_antisymm (sup_le (radical_le_lineLocal 0 (by decide))
    (radical_le_lineLocal 1 (by decide))) lineLocal_le_pair

variable [Finite F]

theorem coordinateScalar_ne_zero (g : lineParabolicSL F) : g.val.val 2 2 ≠ 0 := by
  have hg := (mem_lineParabolicSL_iff F g.val).mp g.property
  intro hz
  have h := congrArg (fun a : SL(3, F) => a.val 2 2) (mul_inv_cancel g.val)
  change (g.val.val * g.val⁻¹.val) 2 2 = 1 at h
  simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hz] at h

/-- The genuine action on the quotient by the coordinate plane. -/
def quotientScalar : lineParabolicSL F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 2 2) (coordinateScalar_ne_zero g)
  map_one' := by apply Units.ext; rfl
  map_mul' g h := by
    apply Units.ext
    have hg := (mem_lineParabolicSL_iff F g.val).mp g.property
    change (g.val.val * h.val.val) 2 2 = g.val.val 2 2 * h.val.val 2 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

theorem quotientScalar_ker :
    (quotientScalar (F := F)).ker.map (lineParabolicSL F).subtype = lineLocalSL F := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hp := (mem_lineParabolicSL_iff F x.val).mp x.property
    have hs : x.val.val 2 2 = 1 := congrArg Units.val hx
    exact (mem_lineLocalSL_iff F _).mpr ⟨hp.1, hp.2, hs⟩
  · intro hg
    refine ⟨⟨g, lineLocalSL_le F hg⟩, ?_, rfl⟩
    apply Units.ext
    exact ((mem_lineLocalSL_iff F g).mp hg).2.2

theorem lineTorus_mem_coordinate_stabilizer (a : Fˣ) (i : Fin 3) :
    lineTorus F a ∈ stabilizer (coordinatePoint i) := by
  rw [stabilizer, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  intro v hv
  apply (mem_coordinatePoint i _).mpr
  intro j hj
  change ((lineTorus F a).val.mulVec v) j = 0
  simp [lineTorus, mulVec, dotProduct, diagonal, (mem_coordinatePoint i v).mp hv j hj]

omit [Finite F] in
theorem pair_stabilizer_le_plane (A B : Submodule F (Fin 3 → F)) :
    stabilizer A ⊓ stabilizer B ≤ stabilizer (A ⊔ B) := by
  rintro g ⟨ha, hb⟩
  rw [mem_stabilizer_iff, Submodule.map_sup,
    (mem_stabilizer_iff A g).mp ha, (mem_stabilizer_iff B g).mp hb]

theorem coordinate_factorization :
    (lineParabolicSL F : Set SL(3, F)) =
      (coordinatePair (F := F) : Set SL(3, F)) *
        (↑(stabilizer (coordinatePoint (F := F) 0) ⊓ stabilizer (coordinatePoint 1)) : Set SL(3, F)) := by
  ext g
  constructor
  · intro hg
    have hz := (mem_lineParabolicSL_iff F g).mp hg
    let a := quotientScalar (⟨g, hg⟩ : lineParabolicSL F)
    let t := lineTorus F a⁻¹
    have ht : t ∈ stabilizer (coordinatePoint 0) ⊓ stabilizer (coordinatePoint 1) :=
      ⟨lineTorus_mem_coordinate_stabilizer _ _, lineTorus_mem_coordinate_stabilizer _ _⟩
    have hl : g * t ∈ lineLocalSL F := by
      rw [mem_lineLocalSL_iff]
      change (g.val * t.val) 2 0 = 0 ∧ (g.val * t.val) 2 1 = 0 ∧ (g.val * t.val) 2 2 = 1
      simp [t, a, quotientScalar, lineTorus, Matrix.mul_diagonal, hz.1, hz.2,
        coordinateScalar_ne_zero (⟨g, hg⟩ : lineParabolicSL F)]
    exact Set.mem_mul.mpr ⟨g * t, (coordinatePair_eq_lineLocal (F := F)).symm ▸ hl,
      t⁻¹, inv_mem ht, by simp⟩
  · rintro ⟨a, ha, t, ht, rfl⟩
    apply (lineParabolicSL F).mul_mem
    · exact lineLocalSL_le F (coordinatePair_eq_lineLocal (F := F) ▸ ha)
    · rw [← coordinatePlane_stabilizer]
      exact pair_stabilizer_le_plane _ _ ht

/-- An involution vanishes in every odd-order quotient. -/
theorem square_one_mem_oddResidual {H : Type*} [Group H] [Finite H]
    (x : H) (hx : x ^ 2 = 1) :
    x ∈ piResidual {p : Nat.Primes | p.val ≠ 2} H := by
  apply Subgroup.mem_sInf.mpr
  rintro N ⟨hN, hpi⟩
  let := hN
  let y := QuotientGroup.mk' N x
  have hy : y ^ 2 = 1 := by
    change (QuotientGroup.mk' N x) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hd := orderOf_dvd_of_pow_eq_one hy
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)
  · have hd' : 2 ∣ Nat.card (H ⧸ N) := by
      rw [← h2]
      exact orderOf_dvd_natCard y
    have hp := (IsPiGroup_iff _ _).mp hpi ⟨2, Nat.prime_two⟩ hd'
    exact (hp rfl).elim

variable [CharP F 2]

theorem units_odd : IsPiGroup {p : Nat.Primes | p.val ≠ 2} Fˣ := by
  let := Fintype.ofFinite F
  have he : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have ho : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd (by have := Finite.one_lt_card (α := F); omega) he odd_one
  rw [IsPiGroup_iff]
  intro p hp h2
  rw [h2] at hp
  exact ho.not_two_dvd_nat hp

theorem coordinate_residual : coordinatePair (F := F) =
    (piResidual {p : Nat.Primes | p.val ≠ 2} (lineParabolicSL F)).map
      (lineParabolicSL F).subtype := by
  apply le_antisymm
  · apply sup_le
    all_goals
      intro x hx
      have hp : x ∈ lineParabolicSL F := lineLocalSL_le F
        (radical_le_lineLocal _ (by decide) hx)
      exact ⟨⟨x, hp⟩, square_one_mem_oddResidual _
        (Subtype.ext (pointRadical_sq _ x hx)), rfl⟩
  · rw [coordinatePair_eq_lineLocal, ← quotientScalar_ker]
    apply Subgroup.map_mono
    apply piResidual_le_ker_of_range
    exact units_odd.of_injective (quotientScalar (F := F)).range.subtype Subtype.val_injective

end Matrix.SpecialLinearGroup.FrameGeometry.PlaneResidual
