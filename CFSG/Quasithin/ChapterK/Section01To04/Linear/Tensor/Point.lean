module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Plane
/-!
# The point-radical alternative for the descended Hermitian tensor

The other root plane also has binary rank 4n, but fixes only the F-line
on e₀ tensor e₀. Two root shears kill the lower diagonal coordinates;
a coefficient of trace one kills the remaining off-diagonal entries.
Thus its fixed dimension is n and its action ratio is two. This concrete
alternative is needed to distinguish the minimizing plane radical.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed p.456/PDF p.467; the point-radical calculation in H.4.4,
printed p.381.
-/

@[expose] public section
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor
variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

theorem card_pointActor : Nat.card (pointActor n M hM) = 2 ^ (4 * n) := by
  rw [pointActor_eq_map,
    ← Nat.card_congr ((V₁ (E n)).equivMapOfInjective _
      (unipotentToOvergroup_injective n M hM)).toEquiv,
    card_V₁, card_E, ← pow_mul]
  congr 1
  omega

theorem rank_pointActor : rank (pointActor n M hM) = 4 * n := by
  rw [rank, card_pointActor, Nat.log_pow (by decide : 1 < 2)]

/-- The other root plane consists of shears with center the marked point. -/
def pointElement (a b : E n) : Cover n := specialLinear (E n) ⟨a,0,b⟩

omit M hM [NeZero n] in
theorem pointElement_matrix (a b : E n) :
    (pointElement n a b).val = !![1,a,b;0,1,0;0,0,1] := rfl

theorem pointElement_mem (a b : E n) :
    coverToOvergroup n M hM (pointElement n a b) ∈ pointActor n M hM := by
  rw [pointActor_eq_map]
  exact ⟨⟨a,0,b⟩, (mem_V₁ _ _).mpr rfl, rfl⟩

theorem pointActor_elements (g : M) : g ∈ pointActor n M hM ↔
    ∃ a b : E n, coverToOvergroup n M hM (pointElement n a b) = g := by
  rw [pointActor_eq_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hy := (mem_V₁ _ _).mp hu
    refine ⟨u.x, u.c, ?_⟩
    change unipotentToOvergroup n M hM ⟨u.x,0,u.c⟩ = unipotentToOvergroup n M hM u
    congr 1
    exact U.ext rfl hy.symm rfl
  · rintro ⟨a,b,rfl⟩
    exact ⟨⟨a,0,b⟩, (mem_V₁ _ _).mpr rfl, rfl⟩

theorem mem_point_fixed (X : Space n) :
    X ∈ fixedSpace (overgroupAction n M) (pointActor n M hM) ↔
      X.val 0 1 = 0 ∧ X.val 0 2 = 0 ∧ X.val 1 1 = 0 ∧
      X.val 1 2 = 0 ∧ X.val 2 2 = 0 := by
  constructor
  · intro h
    have hf (a b : E n) : action n (pointElement n a b) X = X :=
      h ⟨coverToOvergroup n M hM (pointElement n a b), pointElement_mem n M hM a b⟩
    have hz : action n (root n) X = X := hf 0 1
    obtain ⟨h22,h12,h02⟩ := (root_action_iff n X).mp hz
    have h20 : X.val 2 0 = X.val 0 2 := (entry_conjugate n X 2 0).symm.trans h02
    have h11 : X.val 1 1 = 0 := by
      have hh := congrArg (fun Y : Space n => Y.val 0 1) (hf 1 0)
      simpa [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three] using hh
    have h10 : X.val 1 0 = X.val 0 1 := by
      have hh := congrArg (fun Y : Space n => Y.val 0 0) (hf 1 0)
      simp [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three, h11] at hh
      have hh' : X.val 1 0 + X.val 0 1 = 0 := by linear_combination hh
      exact CharTwo.add_eq_zero.mp hh'
    obtain ⟨t,ht⟩ := FieldSections.exists_trace_one n
    have h01z : X.val 0 1 = 0 := by
      have hh := congrArg (fun Y : Space n => Y.val 0 0) (hf t 0)
      simp [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three, h11, h10] at hh
      calc
        X.val 0 1 = X.val 0 1 * (sigma n t + t) := by rw [ht, mul_one]
        _ = 0 := by linear_combination hh
    have h02z : X.val 0 2 = 0 := by
      have hh := congrArg (fun Y : Space n => Y.val 0 0) (hf 0 t)
      simp [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three, h22, h20] at hh
      calc
        X.val 0 2 = X.val 0 2 * (sigma n t + t) := by rw [ht, mul_one]
        _ = 0 := by linear_combination hh
    exact ⟨h01z,h02z,h11,h12,h22⟩
  · rintro ⟨h01,h02,h11,h12,h22⟩ g
    obtain ⟨a,b,hg⟩ := (pointActor_elements n M hM g.val).mp g.property
    have h10 : X.val 1 0 = 0 := by rw [← entry_conjugate n X 1 0, h01, map_zero]
    have h20 : X.val 2 0 = 0 := by rw [← entry_conjugate n X 2 0, h02, map_zero]
    have h21 : X.val 2 1 = 0 := by rw [← entry_conjugate n X 2 1, h12, map_zero]
    change overgroupAction n M g.val X = X
    rw [← hg]
    change action n (pointElement n a b) X = X
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [action_apply, pointElement_matrix, adjoint, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_three, h01,h02,h11,h12,h22,h10,h20,h21]

/-- The point radical fixes precisely the F-line on e₀ tensor e₀. -/
def pointFixedCoordinates :
    fixedSpace (overgroupAction n M) (pointActor n M hM) ≃ F n where
  toFun X := ⟨X.val.val 0 0, entry_conjugate n X.val 0 0⟩
  invFun c := ⟨(Representation.HermitianTensorThree.coordinates n).symm
    (![c,0,0], ![0,0,0]), (mem_point_fixed n M hM _).mpr ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  left_inv X := by
    obtain ⟨h01,h02,h11,h12,h22⟩ := (mem_point_fixed n M hM X.val).mp X.property
    have h10 : X.val.val 1 0 = 0 := by rw [← entry_conjugate n X.val 1 0, h01, map_zero]
    have h20 : X.val.val 2 0 = 0 := by rw [← entry_conjugate n X.val 2 0, h02, map_zero]
    have h21 : X.val.val 2 1 = 0 := by rw [← entry_conjugate n X.val 2 1, h12, map_zero]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Representation.HermitianTensorThree.coordinates, h01,h02,h11,h12,h22,h10,h20,h21]
  right_inv c := rfl

theorem finrank_point_fixed :
    Module.finrank (ZMod 2) (fixedSpace (overgroupAction n M) (pointActor n M hM)) = n := by
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (overgroupAction n M) (pointActor n M hM))
  have hc : Nat.card (ZMod 2) = 2 := by simp
  rw [hc, Nat.card_congr (pointFixedCoordinates n M hM), card_F] at h2
  exact ((pow_right_inj₀ (by decide : 0 < (2 : ℕ)) (by decide : (2 : ℕ) ≠ 1)).mp h2).symm

theorem codim_point_fixed : fixedCodim (overgroupAction n M) (pointActor n M hM) = 8 * n := by
  have h := fixedCodim_add_finrank (overgroupAction n M) (pointActor n M hM)
  rw [finrank_point_fixed, finrank_binary] at h
  omega

theorem pointActor_ratio : actionRatio (overgroupAction n M) (pointActor n M hM) = 2 := by
  rw [actionRatio, codim_point_fixed, rank_pointActor, Nat.cast_mul, Nat.cast_mul]
  have hn : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [ENNReal.mul_div_mul_right _ _ hn (by simp)]
  norm_num only [Nat.cast_ofNat]
  rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by simp)]

end CFSG.Quasithin.ChapterK.Linear.Tensor
