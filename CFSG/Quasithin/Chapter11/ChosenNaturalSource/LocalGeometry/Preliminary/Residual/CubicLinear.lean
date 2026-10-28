module
public import Theory.Representation.SL3OddNaturalNormalizer
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Cubic determinants in the chosen natural linear argument

A cubic matrix whose determinant is nontrivial supplies all three independent
diagonal cubics in any linear overgroup of SL₃. Their elementary subgroup of
order 27 contradicts the ambient three-rank bound. The full scalar center is
retained, and the field need not have order four.

Source: the natural-module argument of Aschbacher--Smith A.3.19, printed
pp.54--55, used for 11.0.4, printed p.760. The consumer is CubicNatural.
-/

public noncomputable section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
variable {F : Type*} [Field F] [Finite F]

private def diagonalUnits : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun u := ⟨Matrix.diagonal (fun i => (u i : F)),
    Matrix.diagonal (fun i => ((u i)⁻¹ : F)),
    by simp [Matrix.diagonal_mul_diagonal],
    by simp [Matrix.diagonal_mul_diagonal]⟩
  map_one' := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp [Matrix.diagonal_mul_diagonal]

omit [Finite F] in
private theorem diagonalUnits_injective : Function.Injective (diagonalUnits (F := F)) := by
  intro x y h
  funext i
  apply Units.ext
  have hh := congrArg (fun A : GL (Fin 3) F => A.val i i) h
  change Matrix.diagonal (fun i => (x i : F)) i i =
    Matrix.diagonal (fun i => (y i : F)) i i at hh
  simpa only [Matrix.diagonal_apply_eq] using hh

omit [Finite F] in
private theorem diagonalUnits_det (v : Fin 3 → Fˣ) :
    GeneralLinearGroup.det (diagonalUnits v) = ∏ i, v i := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (v i : F))).det = _
  simp

/-- A nontrivial cubic determinant in an overgroup of SL₃ forces cubic rank three. -/
theorem three_le_rank_of_cubic_determinant (D : Subgroup (GL (Fin 3) F))
    (hSL : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ D)
    (A : D) (hA : A ^ 3 = 1) (hd : GeneralLinearGroup.det A.val ≠ 1) :
    3 ≤ primeRank 3 D := by
  classical
  let δ : GL (Fin 3) F →* Fˣ := GeneralLinearGroup.det
  let u := δ A.val
  have hu : u ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg δ (congrArg Subtype.val hA)).trans δ.map_one
  have ho : orderOf u = 3 := orderOf_eq_prime hu hd
  let P := zpowers u
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.zpowers_of_pow_eq_one hu
  have hP : P ≤ D.map δ := zpowers_le.mpr ⟨A.val,A.property,rfl⟩
  let f : (Fin 3 → P) →* D := (diagonalUnits.comp
    (MonoidHom.pi fun i : Fin 3 => P.subtype.comp (Pi.evalMonoidHom (fun _ : Fin 3 => P) i))).codRestrict D (by
      intro v
      have hm : δ (diagonalUnits (fun i => (v i : Fˣ))) ∈ D.map δ := by
        rw [diagonalUnits_det]
        exact (D.map δ).prod_mem fun i _ => hP (v i).property
      have hh : (D.map δ).comap δ = D := comap_map_eq_self hSL
      exact hh ▸ hm)
  have hf : Function.Injective f := by
    intro a b hab
    have hh := diagonalUnits_injective (congrArg Subtype.val hab)
    funext i
    exact Subtype.ext (congrFun hh i)
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 3) ?_ ?_ f hf
  · intro a
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 P) (a i)
  · rw [Nat.card_fun, Nat.card_fin, Nat.card_zpowers, ho]

/-- Every cubic in a rank-two linear overgroup has determinant one. -/
theorem cubic_det_eq_one (D : Subgroup (GL (Fin 3) F))
    (hSL : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker ≤ D)
    (hr : primeRank 3 D ≤ 2) (A : D) (hA : A ^ 3 = 1) :
    GeneralLinearGroup.det A.val = 1 := by
  by_contra hd
  have hh := three_le_rank_of_cubic_determinant D hSL A hA hd
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
