module
public import Theory.SpecificGroups.ClassicalOrthogonal.TwoRankLower.Odd
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Five-dimensional blocks in split orthogonal groups in odd characteristic

The explicit isometry from B₂ plus the negative square line to D₃ extends
actual Siegel generators. Larger hyperbolic block embeddings retain the
centerless PSp₄ subgroup, which survives the literal scalar quotient.
Source: GLS3 §2.7; Aschbacher–Smith A.2.12, printed p.36.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.TwoRank
open Fundamental.SplitOddBlocks Theory.GroupTheory
variable {F : Type} [Field F]
abbrev MinusLine : QuadraticForm F F := -(QuadraticMap.sq (R:=F))

def fivePlusLineLinear (h2 : (2:F) ≠ 0) : (VectorB 2 F × F) ≃ₗ[F] VectorD 3 F where
  toFun v := Sum.elim ![v.1.1 (.inl 0),v.1.1 (.inl 1),v.1.2+v.2]
    ![v.1.1 (.inr 0),v.1.1 (.inr 1),v.1.2-v.2]
  invFun x := ((Sum.elim (fun i => x (.inl i.castSucc)) (fun i => x (.inr i.castSucc)),
    (x (.inl 2)+x (.inr 2))/2), (x (.inl 2)-x (.inr 2))/2)
  left_inv v := by
    rcases v with ⟨⟨v,z⟩,w⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i; cases i with
        | inl i => fin_cases i <;> rfl
        | inr i => fin_cases i <;> rfl
      · dsimp
        field_simp [h2]
        ring
    · dsimp
      field_simp [h2]
      ring
  right_inv x := by
    funext i
    cases i with
    | inl i =>
      fin_cases i
      · rfl
      · rfl
      · change (x (.inl 2)+x (.inr 2))/2 + (x (.inl 2)-x (.inr 2))/2 = x (.inl 2)
        field_simp [h2]
        ring
    | inr i =>
      fin_cases i
      · rfl
      · rfl
      · change (x (.inl 2)+x (.inr 2))/2 - (x (.inl 2)-x (.inr 2))/2 = x (.inr 2)
        field_simp [h2]
        ring
  map_add' v w := by
    funext i
    cases i with
    | inl i => fin_cases i <;> first | rfl | (dsimp; ring)
    | inr i => fin_cases i <;> first | rfl | (dsimp; ring)
  map_smul' c v := by
    funext i
    cases i with
    | inl i => fin_cases i <;> first | rfl | (dsimp; ring)
    | inr i => fin_cases i <;> first | rfl | (dsimp; ring)

def fivePlusLine (h2 : (2:F) ≠ 0) :
    ((formB 2 F).prod (MinusLine (F:=F))).IsometryEquiv (formD 3 F) where
  __ := fivePlusLineLinear h2
  map_app' v := by
    simp only [formD_apply,Fin.sum_univ_succ]
    change (v.1.1 (.inl 0)*v.1.1 (.inr 0) +
      (v.1.1 (.inl 1)*v.1.1 (.inr 1) + ((v.1.2+v.2)*(v.1.2-v.2)+0))) = _
    simp only [QuadraticMap.prod_apply,formB_apply,formD_apply,Fin.sum_univ_succ]
    change _ = (v.1.1 (.inl 0)*v.1.1 (.inr 0)+(v.1.1 (.inl 1)*v.1.1 (.inr 1)+0)) + v.1.2^2 + -(v.2*v.2)
    ring

/-- The literal elementary five-space acts on split six, fixing its orthogonal line. -/
def fiveInSix (h2 : (2:F) ≠ 0) : OmegaOdd 2 F →* OmegaPlus 3 F :=
  (blockMap _ _ _ (fivePlusLine h2)).comp (MonoidHom.inl _ _)

theorem fiveInSix_injective (h2 : (2:F) ≠ 0) : Function.Injective (fiveInSix h2) :=
  (blockMap_injective _ _ _ _).comp (fun _ _ h => congrArg Prod.fst h)

variable [Finite F]
/-- A genuine elementary eight in every higher split orthogonal group in odd characteristic. -/
theorem plus_odd_three_le (h2 : (2:F) ≠ 0) {r : ℕ} (hr : 3 ≤ r) :
    3 ≤ primeRank 2 (POmegaPlus r F) := by
  obtain ⟨n,rfl⟩ : ∃ n, r=3+n := ⟨r-3,by omega⟩
  let f : OmegaOdd 2 F →* OmegaPlus (3+n) F :=
    ((plusBlocks 3 n).comp (MonoidHom.inl _ _)).comp (fiveInSix h2)
  have hf : Function.Injective f :=
    ((plusBlocks_injective 3 n).comp (fun _ _ h => congrArg Prod.fst h)).comp (fiveInSix_injective h2)
  let e := OddFiveComparison.pspEquivElementary h2
  have hE := (Theory.SpecificGroups.Symplectic.TwoRank.three_le F (by decide : 2≤2))
  have hB : 3 ≤ primeRank 2 (OmegaOdd 2 F) := by
    rw [← primeRank_equiv 2 e]
    exact hE
  exact hB.trans (primeRank_le_of_injective 2 _
    (projective_injective_of_centerless _ f hf (odd_five_center F h2)))
end ClassicalOrthogonal.TwoRank
