module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Factorization.ScalarModel

/-!
# Field linearity recovered from the actual scalar Y

Transport Y through the additive coordinates. Its commutation with the long
SL₃ and graph actions makes it a scalar by `ScalarModel`. Invertibility and
the actual absence of nonzero Y-fixed vectors exclude scalars 0 and 1.
Every GF(4) element is one of 0, 1, c, c+1; thus any additive map commuting
with Y is linear over the coordinate field. This proves linearity for the
literal tetrahedral centralizer without identifying the arbitrary frame
with the published scalar-field coordinates.

`Factorization` consumes this result for the source local A₅.
Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
open scoped Long
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

def yCoordinates (L : LongFrame) : (Fin 6 → F) →+ (Fin 6 → F) :=
  (coordinateEquiv L).symm.toAddMonoidHom.comp
    (Long.yEnd.toAddMonoidHom.comp (coordinateEquiv L).toAddMonoidHom)

theorem yCoordinates_spec (L : LongFrame) (v : Fin 6 → F) :
    L.coordinates (yCoordinates L v) =
      quotientModTwoRepresentation y (L.coordinates v) := by
  change ((coordinateEquiv L) ((coordinateEquiv L).symm
    (Long.yEnd (coordinateEquiv L v)))).val = _
  rw [(coordinateEquiv L).apply_symm_apply]
  rfl

theorem yCoordinates_scalar (L : LongFrame) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 ∧ ∀ v, yCoordinates L v = c • v := by
  have hswap (v : Fin 6 → F) :
      quotientModTwoRepresentation L.swap (L.coordinates v) =
        L.coordinates (action graph v) :=
    equivariant_of_single _ _ _ L.on_swap v
  obtain ⟨c, hc⟩ := commuting_long_graph_scalar (yCoordinates L)
    (fun A v => by
      apply L.coordinates_injective
      rw [yCoordinates_spec, ← L.intertwines_long, ← L.intertwines_long,
        yCoordinates_spec]
      have h := congrArg (fun g => quotientModTwoRepresentation g (L.coordinates v))
        (L.long_mem A y ⟨threeCycle, rfl⟩)
      simpa only [map_mul, LinearEquiv.mul_apply] using h)
    (fun v => by
      apply L.coordinates_injective
      rw [yCoordinates_spec, ← hswap, ← hswap, yCoordinates_spec]
      have h := congrArg (fun g => quotientModTwoRepresentation g (L.coordinates v))
        (L.swap_mem y ⟨threeCycle, rfl⟩)
      simpa only [map_mul, LinearEquiv.mul_apply] using h)
  have hvec : L.coordinates (Pi.single 0 1) ≠ 0 := by
    intro h
    have he := L.coordinates_injective (h.trans (map_zero L.coordinates).symm)
    have hz := congrFun he 0
    simp at hz
  refine ⟨c, ?_, ?_, hc⟩
  · intro hz
    have he := yCoordinates_spec L (Pi.single 0 1)
    rw [hc, hz, zero_smul, map_zero] at he
    exact hvec ((quotientModTwoRepresentation y).injective
      (he.symm.trans (map_zero _).symm))
  · intro ho
    apply hvec
    apply Long.y_fixed_eq_zero
    rw [← yCoordinates_spec, hc, ho, one_smul]

private theorem four_elements {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (t : F) :
    t = 0 ∨ t = 1 ∨ t = c ∨ t = c + 1 := by
  let e : Fin 4 → F := ![0,1,c,c+1]
  have hn0 : c + 1 ≠ 0 := by
    intro h
    apply hc1
    exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq (1 : F))
  have hn1 : c + 1 ≠ 1 := by simpa using hc0
  have hnc : c + 1 ≠ c := by simp
  have hi : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [e, eq_comm]
  have he : Function.Bijective e := (Nat.bijective_iff_injective_and_card e).mpr
    ⟨hi, by rw [Nat.card_fin, GaloisField.card 2 2 (by decide)]; norm_num⟩
  obtain ⟨i, rfl⟩ := he.surjective t
  fin_cases i <;> simp [e]

theorem coordinateAction_smul (L : LongFrame) (g : centralizerI) (t : F) (v : Fin 6 → F) :
    coordinateAction L g (t • v) = t • coordinateAction L g v := by
  obtain ⟨c, hc0, hc1, hc⟩ := yCoordinates_scalar L
  have hcomm (w : Fin 6 → F) :
      coordinateAction L g (yCoordinates L w) = yCoordinates L (coordinateAction L g w) := by
    apply L.coordinates_injective
    rw [coordinateAction_spec, yCoordinates_spec, yCoordinates_spec, coordinateAction_spec]
    have h := congrArg (fun k => quotientModTwoRepresentation k (L.coordinates w))
      (g.property y ⟨threeCycle, rfl⟩)
    simpa only [map_mul, LinearEquiv.mul_apply] using h.symm
  have hcs (w : Fin 6 → F) : coordinateAction L g (c • w) = c • coordinateAction L g w := by
    simpa only [hc] using hcomm w
  rcases four_elements hc0 hc1 t with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact hcs v
  · simp only [add_smul, one_smul, map_add, hcs]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Factorization
