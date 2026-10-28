module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Inputs

/-!
# The central cubic in the actual long Leech subgroup

Every unit of GF(4) has cube one. Its scalar matrix therefore belongs to
SL₃(4), and its image through any `LongFrame.long` centralizes the entire
long subgroup in the ambient Leech quotient. In particular it lies in the
literal common centralizer of I and the placed D₁₀. Testing coordinate zero
proves injectivity, so the image is a genuine subgroup of order three.

In the octonion convention, the natural triple is (0,3,4) and the dual triple
is (5,2,1). The scalar matrix consequently acts by the precise pair
`(torus t, (torus t)⁻¹)` required by `Geometry`. The A₅ construction only
has to contain this already placed subgroup; its cubic action is proved here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284:
this is X inside E(K₁), before constructing K₂ = C_L(D). The actual
consumer is `SourceConstruction.geometryOfPlacement` in `Geometry.lean`.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

private theorem units_cube (t : Fˣ) : t ^ 3 = 1 := by
  have hc : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    norm_num
  simpa only [hc] using (pow_card_eq_one' (x := t))

def longCubicMatrix (t : Fˣ) : SL(3,F) :=
  ⟨!![(t : F),0,0;0,(t : F),0;0,0,(t : F)], by
    have h : (t : F) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val (units_cube t)
    simpa [Matrix.det_fin_three, pow_succ, mul_assoc] using h⟩

theorem longCubicMatrix_action (t : Fˣ) (v : Fin 6 → F) :
    action (BlockRealization.blockHom (longCubicMatrix t)) v =
      pairRepresentation (torus t, (torus t)⁻¹) v := by
  have hi : (t : F) * t = ((t⁻¹ : Fˣ) : F) := by
    have h := congrArg (fun a : Fˣ => a * t⁻¹) (units_cube t)
    have h' : t * t = t⁻¹ := by simpa [pow_succ, mul_assoc] using h
    exact_mod_cast h'
  rw [action_block]
  have hinv : (torus t)⁻¹ = torus t⁻¹ := by
    apply Subtype.ext
    change (!![(t : F),0;0,((t⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F).adjugate = _
    simp [torus, Matrix.adjugate_fin_two]
  rw [hinv]
  change _ = pairAction (torus t, torus t⁻¹) v
  funext i
  fin_cases i <;>
    simp [longCubicMatrix, pairAction, torus, BlockRealization.cofactor,
      Matrix.adjugate_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      CharTwo.neg_eq, hi]

def longCubicMatrixHom : Fˣ →* SL(3,F) where
  toFun := longCubicMatrix
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longCubicMatrix]
  map_mul' t s := by
    apply Subtype.ext
    change (longCubicMatrix (t * s)).val = (longCubicMatrix t).val * (longCubicMatrix s).val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longCubicMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem longCubicMatrix_commute (t : Fˣ) (A : SL(3,F)) :
    Commute (longCubicMatrix t) A := by
  have he : (longCubicMatrix t).val = Matrix.scalar (Fin 3) (t : F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longCubicMatrix, Matrix.scalar_apply]
  apply Subtype.ext
  change (longCubicMatrix t).val * A.val = A.val * (longCubicMatrix t).val
  rw [he]
  exact (Matrix.scalar_commute (t : F) (Commute.all _) A.val).eq

def longCubic (L : LongFrame) : Fˣ →* LeechCentralQuotient := L.long.comp longCubicMatrixHom

theorem longCubic_action (L : LongFrame) (t : Fˣ) (v : Fin 6 → F) :
    quotientModTwoRepresentation (longCubic L t) (L.coordinates v) =
      L.coordinates (pairRepresentation (torus t, (torus t)⁻¹) v) := by
  change quotientModTwoRepresentation (L.long (longCubicMatrix t)) (L.coordinates v) = _
  rw [L.intertwines_long, longCubicMatrix_action]

theorem longCubic_injective (L : LongFrame) : Function.Injective (longCubic L) := by
  intro s t h
  have hs := longCubic_action L s (Pi.single 0 1)
  have ht := longCubic_action L t (Pi.single 0 1)
  rw [h] at hs
  have he := L.coordinates_injective (hs.symm.trans ht)
  apply Units.ext
  simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun he 0

theorem longCubic_commutes_long (L : LongFrame) (t : Fˣ) (A : SL(3,F)) :
    Commute (longCubic L t) (L.long A) :=
  (longCubicMatrix_commute t A).map L.long

theorem longCubic_commutes_dihedral (L : LongFrame) (t : Fˣ) (d : DihedralGroup 5) :
    Commute (longCubic L t) (dihedralLift L d) :=
  longCubic_commutes_long L t (block (slEquiv (dihedralModel d)))

def localCentralizer (L : LongFrame) : Subgroup LeechCentralQuotient :=
  centralizerI ⊓ Subgroup.centralizer ((dihedralLift L).range : Set LeechCentralQuotient)

theorem longCubic_mem_localCentralizer (L : LongFrame) (t : Fˣ) :
    longCubic L t ∈ localCentralizer L := by
  refine ⟨L.long_mem _, ?_⟩
  rintro g ⟨d, rfl⟩
  exact (longCubic_commutes_dihedral L t d).symm.eq

theorem longCubic_range_le (L : LongFrame) :
    (longCubic L).range ≤ localCentralizer L := by
  rintro g ⟨t, rfl⟩
  exact longCubic_mem_localCentralizer L t

theorem longCubic_card (L : LongFrame) : Nat.card (longCubic L).range = 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (longCubic_injective L)).toEquiv,
    Nat.card_units, GaloisField.card 2 2 (by decide)]
  norm_num

theorem longCubic_order (L : LongFrame) {t : Fˣ} (ht : t ≠ 1) :
    orderOf (longCubic L t) = 3 := by
  rw [orderOf_injective (longCubic L) (longCubic_injective L)]
  exact orderOf_eq_prime (units_cube t) ht

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
