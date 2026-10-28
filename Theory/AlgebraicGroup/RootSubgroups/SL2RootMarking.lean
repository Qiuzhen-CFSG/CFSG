module

public import Theory.AlgebraicGroup.BNPair.SL2SimpleExchange
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation

/-!
SL₂ markings of actual opposite root subgroups and normalization of the torus.

A marking identifies both standard matrix curves with algebraic one-parameter
parametrizations of the supplied root subgroups. Their reciprocal torus weights
turn inverse conjugation of the three-factor Weyl word into a diagonal times
that word. Diagonal containment and the formula for its square then prove
normalization of the entire torus, in arbitrary characteristic.

This is the rank-one calculation used in GLS3, §§1.9 and 1.11.3, and Borel,
§§13.18 and 14.15. Existence of the compatible marking is separate geometry;
no root-recognition or Tits-system existence theorem is invoked here.
-/

open Matrix
open scoped MatrixGroups

namespace Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- A jointly calibrated pair of algebraic root curves and an abstract SL₂ map.
The curve identities require the literal matrix parameters. In particular,
independently chosen parametrizations are not asserted to be compatible. -/
public structure SL2RootMarking (D : RootGroupData G T) (α : D.Root) where
  plus : OneParameterParametrization (D.rootSubgroup α).carrierVariety
  minus : OneParameterParametrization (D.rootSubgroup (D.neg α)).carrierVariety
  hom : SL(2, k) →* Variety.Point G
  upper_eq : ∀ t, hom (BruhatGeneration.SL2.upper t) =
    (D.rootSubgroup α).includePoint (plus.value t)
  lower_eq : ∀ t, hom (BruhatGeneration.SL2.lower t) =
    (D.rootSubgroup (D.neg α)).includePoint (minus.value t)
  diagonal_mem : ∀ t (ht : t ≠ 0), hom (SpecialLinearGroup.diag2 t ht) ∈ T.toSubgroup

private theorem parametrization_range (X : ClosedSubgroup G)
    (p : OneParameterParametrization X.carrierVariety) :
    Set.range (fun t => X.includePoint (p.value t)) = (X : Set (Variety.Point G)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (X.pointEquiv (p.value t)).property
  · intro hx
    let y := X.pointEquiv.symm ⟨x, hx⟩
    let a := p.inv.onPoints y
    refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k a), ?_⟩
    change X.includePoint (p.hom.onPoints (kPlusPoint _)) = x
    rw [kPlusPoint_coordinate, p.inv_hom_id]
    exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨x, hx⟩)

namespace SL2RootMarking

variable {D : RootGroupData G T} {α : D.Root} (M : SL2RootMarking D α)

/-- The upper matrix curve maps onto the chosen root subgroup. -/
public theorem upper_range : Set.range (fun t => M.hom (BruhatGeneration.SL2.upper t)) =
    (D.rootSubgroup α : Set (Variety.Point G)) := by
  simp_rw [M.upper_eq]
  exact parametrization_range _ M.plus

/-- The lower matrix curve maps onto the chosen opposite root subgroup. -/
public theorem lower_range : Set.range (fun t => M.hom (BruhatGeneration.SL2.lower t)) =
    (D.rootSubgroup (D.neg α) : Set (Variety.Point G)) := by
  simp_rw [M.lower_eq]
  exact parametrization_range _ M.minus

private theorem matrix_word (a : k) (ha : a ≠ 0) :
    BruhatGeneration.SL2.upper a * BruhatGeneration.SL2.lower (-a⁻¹) *
      BruhatGeneration.SL2.upper a =
      SpecialLinearGroup.diag2 a ha * BruhatGeneration.SL2.reflection := by
  apply Subtype.ext
  change (BruhatGeneration.SL2.upper a).val * (BruhatGeneration.SL2.lower (-a⁻¹)).val *
    (BruhatGeneration.SL2.upper a).val =
      (SpecialLinearGroup.diag2 a ha).val * !![0, 1; -1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BruhatGeneration.SL2.upper, BruhatGeneration.SL2.lower,
      SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      mul_apply, Fin.sum_univ_two, ha]

private theorem reflection_word : BruhatGeneration.SL2.reflection (k := k) =
    BruhatGeneration.SL2.upper 1 * BruhatGeneration.SL2.lower (-1) *
      BruhatGeneration.SL2.upper 1 := by
  have h := matrix_word (1 : k) one_ne_zero
  have hdiag : SpecialLinearGroup.diag2 (1 : k) one_ne_zero = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.diag2_coe']
  simpa only [hdiag, one_mul, inv_one] using h.symm

/-- Inverse conjugation by a torus point multiplies the reflection by a diagonal
image. This uses the inverse-conjugation convention in `RootWeightEquation`;
the two root parameters scale by reciprocal characters. -/
public theorem torus_conjugates_reflection (hD : D.IsRealization)
    (s : Variety.Point T.carrierVariety) :
    ∃ ha : (D.rootWeight α).pointCharacter s ≠ 0,
      (T.includePoint s)⁻¹ * M.hom BruhatGeneration.SL2.reflection * T.includePoint s =
        M.hom (SpecialLinearGroup.diag2 ((D.rootWeight α).pointCharacter s) ha) *
          M.hom BruhatGeneration.SL2.reflection := by
  let a := (D.rootWeight α).pointCharacter s
  have ha : a ≠ 0 := Units.ne_zero (dPointEquiv 1 ((D.rootWeight α).onPoints s) 0)
  have hup (t : k) :
      (T.includePoint s)⁻¹ * M.hom (BruhatGeneration.SL2.upper t) * T.includePoint s =
        M.hom (BruhatGeneration.SL2.upper (a * t)) := by
    simp_rw [M.upper_eq]
    exact (hD.2.2.1 α).2 M.plus t s
  have hneg : (D.rootWeight (D.neg α)).pointCharacter s = a⁻¹ := by
    rw [hD.2.2.2.1 α]
    change (dPointEquiv 1 (((D.rootWeight α).onPoints s)⁻¹) 0 : k) = _
    have hmul := dPointEquiv_mul 1 ((D.rootWeight α).onPoints s)
      (((D.rootWeight α).onPoints s)⁻¹)
    rw [mul_inv_cancel, dPointEquiv_one] at hmul
    have hzero := congrArg (fun f : Fin 1 → kˣ => (f 0 : k)) hmul
    change 1 = a * (dPointEquiv 1 (((D.rootWeight α).onPoints s)⁻¹) 0 : k) at hzero
    apply mul_left_cancel₀ ha
    rw [← hzero, mul_inv_cancel₀ ha]
  have hlo (t : k) :
      (T.includePoint s)⁻¹ * M.hom (BruhatGeneration.SL2.lower t) * T.includePoint s =
        M.hom (BruhatGeneration.SL2.lower (a⁻¹ * t)) := by
    simp_rw [M.lower_eq]
    rw [← hneg]
    exact (hD.2.2.1 (D.neg α)).2 M.minus t s
  refine ⟨ha, ?_⟩
  calc
    _ = (T.includePoint s)⁻¹ *
        (M.hom (BruhatGeneration.SL2.upper 1) * M.hom (BruhatGeneration.SL2.lower (-1)) *
          M.hom (BruhatGeneration.SL2.upper 1)) * T.includePoint s := by
      rw [reflection_word, map_mul, map_mul]
    _ = ((T.includePoint s)⁻¹ * M.hom (BruhatGeneration.SL2.upper 1) * T.includePoint s) *
        ((T.includePoint s)⁻¹ * M.hom (BruhatGeneration.SL2.lower (-1)) * T.includePoint s) *
        ((T.includePoint s)⁻¹ * M.hom (BruhatGeneration.SL2.upper 1) * T.includePoint s) := by group
    _ = M.hom (BruhatGeneration.SL2.upper a * BruhatGeneration.SL2.lower (-a⁻¹) *
        BruhatGeneration.SL2.upper a) := by rw [hup, hlo]; simp only [mul_one, mul_neg_one, map_mul]
    _ = _ := by rw [matrix_word a ha, map_mul]

/-- A compatible SL₂ marking whose diagonal lies in T has reflection image in
its full abstract normalizer. The reverse containment follows from the fact
that the reflection squares into T, so no finite-index argument is needed. -/
public theorem reflection_mem (hD : D.IsRealization) :
    M.hom BruhatGeneration.SL2.reflection ∈ T.normalizer.toSubgroup := by
  let w := M.hom BruhatGeneration.SL2.reflection
  have hsq : w * w ∈ T.toSubgroup := by
    dsimp [w]
    rw [← map_mul, BruhatGeneration.SL2.reflection_square]
    exact M.diagonal_mem _ _
  have hforward (t : Variety.Point G) (ht : t ∈ T.toSubgroup) :
      w * t * w⁻¹ ∈ T.toSubgroup := by
    let s := T.pointEquiv.symm ⟨t, ht⟩
    have hs : T.includePoint s = t :=
      congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
    obtain ⟨ha, heq⟩ := M.torus_conjugates_reflection hD s
    rw [hs] at heq
    let a := (D.rootWeight α).pointCharacter s
    change t⁻¹ * w * t = M.hom (SpecialLinearGroup.diag2 a ha) * w at heq
    have heq' : w * t * w⁻¹ = t * M.hom (SpecialLinearGroup.diag2 a ha) := by
      calc
        _ = t * (t⁻¹ * w * t) * w⁻¹ := by group
        _ = _ := by rw [heq]; group
    rw [heq']
    exact T.toSubgroup.mul_mem ht (M.diagonal_mem a ha)
  change w ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point G))
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨hforward t, fun ht => ?_⟩
  have htwice := hforward (w * t * w⁻¹) ht
  have h := T.toSubgroup.mul_mem
    (T.toSubgroup.mul_mem (T.toSubgroup.inv_mem hsq) htwice) hsq
  convert h using 1
  group

end SL2RootMarking

/-- Distinct realized root indices have distinct root subgroups. This follows
from uniqueness of a subgroup's weight, and does not assume uniqueness of a
subgroup having a given weight. -/
public theorem RootGroupData.IsRealization.rootSubgroup_injective
    {D : RootGroupData G T} (hD : D.IsRealization) :
    Function.Injective D.rootSubgroup := by
  intro a b hab
  apply hD.1
  apply rootWeightEquation_unique T (D.rootSubgroup a) (hD.2.2.1 a).1.2
    (hD.2.2.1 a).2
  rw [hab]
  exact (hD.2.2.1 b).2

end Theory.AlgebraicGroup
