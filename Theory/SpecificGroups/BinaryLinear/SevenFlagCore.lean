module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.FullFlagSylow
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Nilpotent
public import Theory.GroupTheory.PCoreImage
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# The two-core of a small binary Sylow overgroup with a factor seven

The actual flag theorem reduces the group to its block diagonal action.
A factor seven requires a block of size at least three. In dimensions four
and five there are therefore at most three blocks, and three strictly
block-upper-triangular differences have zero product. Thus the two-core
has nilpotency class at most two.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement Classical
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions SmallParabolicLevi
variable {m : ℕ}

private noncomputable def standardBasis : Basis m := Pi.basisFun (ZMod 2) (Fin (m + 1))
private noncomputable def standardBorel : Subgroup (LinearGroup (m + 1)) :=
  cutStabilizer standardBasis Set.univ
private noncomputable def matrix (g : LinearGroup (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  ((slEquivLinear (m + 1)).symm g).val
private theorem matrix_apply (g : LinearGroup (m + 1)) (i j : Fin (m + 1)) :
    matrix g i j = g (standardBasis j) i := by
  have h := congrFun (show (matrix g).mulVec (Pi.single j 1) = g (Pi.single j 1) from by
    rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, standardBasis, Pi.basisFun_apply] using h
private theorem mem_standard_cutSpace (i : Fin m) (v : Space (m + 1)) :
    v ∈ cutSpace standardBasis i ↔ ∀ j : Fin (m + 1), i.val < j.val → v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin (m + 1), v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))
private theorem mem_standard_cutStabilizer_iff (cuts : Set (Fin m)) (g : LinearGroup (m + 1)) :
    g ∈ cutStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i j : Fin (m + 1), k.val < i.val → j.val ≤ k.val → matrix g i j = 0 := by
  rw [mem_cutStabilizer_maps]
  constructor
  · intro h k hk i j hi hj
    rw [matrix_apply]
    exact (mem_standard_cutSpace k _).mp
      (h k hk _ ((basis_mem_cutSpace standardBasis k j).mpr hj)) i hi
  · intro h k hk v hv
    apply (mem_standard_cutSpace k _).mpr
    intro i hi
    have he : (matrix g).mulVec v = g v := by
      rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]
    rw [← he]
    change ∑ j, matrix g i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val ≤ k.val
    · rw [h k hk i j hi hj, zero_mul]
    · rw [(mem_standard_cutSpace k v).mp hv j (Nat.lt_of_not_ge hj), mul_zero]
private theorem mem_standardBorel_iff (g : LinearGroup (m + 1)) :
    g ∈ standardBorel ↔ (matrix g).IsUpperTriangular := by
  rw [standardBorel, mem_standard_cutStabilizer_iff]
  constructor
  · intro h i j hji
    exact h ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      (Set.mem_univ _) i j hji le_rfl
  · intro h k _ i j hi hj
    exact h (show j < i by change j.val < i.val; omega)
private theorem standardBorel_isPGroup : IsPGroup 2 (standardBorel (m := m)) :=
  fullFlag_isPGroup standardBasis

private instance (n : ℕ) : Finite (LinearGroup n) := Finite.of_injective
  (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private noncomputable def matrixHom : LinearGroup (m + 1) →* Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.SpecialLinearGroup.coeMonoidHom.comp (slEquivLinear (m + 1)).symm.toMonoidHom

@[simp] private theorem matrixHom_apply (g : LinearGroup (m + 1)) : matrixHom g = matrix g := rfl

/-- Actual automorphisms upper triangular with respect to an ordered partition. -/
private noncomputable def triangularGroup (c : Fin (m + 1) → Fin (m + 1)) : Subgroup (LinearGroup (m + 1)) where
  carrier := {g | (matrix g).BlockTriangular c}
  one_mem' := by change (matrixHom 1).BlockTriangular c; rw [map_one]; exact Matrix.blockTriangular_one
  mul_mem' {g h} hg hh := by
    change (matrixHom (g * h)).BlockTriangular c
    rw [map_mul]
    exact hg.mul hh
  inv_mem' {g} hg := by
    have he : g ^ (orderOf g - 1) = g⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [← he]
    change (matrixHom (g ^ _)).BlockTriangular c
    rw [map_pow]
    exact hg.pow _

private abbrev Block (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1)) := {i : Fin (m + 1) // c i = k}
private abbrev BlockSpace (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1)) := Block c k → ZMod 2

/-- The literal diagonal submatrix on a block. -/
private noncomputable def blockMatrix (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1)) (g : LinearGroup (m + 1)) :
    Matrix (Block c k) (Block c k) (ZMod 2) :=
  (matrix g).submatrix Subtype.val Subtype.val

@[simp] private theorem blockMatrix_one (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1)) :
    blockMatrix c k 1 = 1 := by
  change (matrixHom 1).submatrix _ _ = _
  rw [map_one, Matrix.submatrix_one _ Subtype.val_injective]

set_option backward.isDefEq.respectTransparency false in
private theorem blockMatrix_mul (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1))
    (g h : triangularGroup c) :
    blockMatrix c k (g.val * h.val) = blockMatrix c k g.val * blockMatrix c k h.val := by
  ext i j
  change (matrixHom (g.val * h.val)) i.val j.val = _
  rw [map_mul, Matrix.mul_apply]
  change (∑ t : Fin (m + 1), matrix g.val i.val t * matrix h.val t j.val) =
    ∑ t : Block c k, matrix g.val i.val t.val * matrix h.val t.val j.val
  rw [← Finset.sum_subtype (Finset.univ.filter (fun t => c t = k))
    (by simp) (fun t => matrix g.val i.val t * matrix h.val t j.val)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t _ ht
  have htk : c t ≠ k := by simpa using ht
  rcases lt_or_gt_of_ne htk with ht | ht
  · rw [g.property (show c t < c i.val by simpa only [i.property] using ht), zero_mul]
  · rw [h.property (show c j.val < c t by simpa only [j.property] using ht), mul_zero]

/-- The diagonal linear action on one block. -/
private noncomputable def diagonalFactor (c : Fin (m + 1) → Fin (m + 1)) (k : Fin (m + 1))
    (g : triangularGroup c) : BinaryLinear.GL (BlockSpace c k) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (blockMatrix c k g.val))
    (Matrix.toLin' (blockMatrix c k g⁻¹.val))
    (by
      rw [← Matrix.toLin'_mul, ← blockMatrix_mul, Subgroup.coe_inv, mul_inv_cancel, blockMatrix_one,
        Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← blockMatrix_mul, Subgroup.coe_inv, inv_mul_cancel, blockMatrix_one,
        Matrix.toLin'_one])

/-- All diagonal actions, with each geometric block retained. -/
private noncomputable def diagonalAction (c : Fin (m + 1) → Fin (m + 1)) :
    triangularGroup c →* (∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) where
  toFun g k := diagonalFactor c k g
  map_one' := by
    funext k
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toLin' (blockMatrix c k 1) = LinearMap.id
    rw [blockMatrix_one, Matrix.toLin'_one]
  map_mul' g h := by
    funext k
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toLin' (blockMatrix c k (g.val * h.val)) =
      (Matrix.toLin' (blockMatrix c k g.val)).comp (Matrix.toLin' (blockMatrix c k h.val))
    rw [blockMatrix_mul, Matrix.toLin'_mul]

@[simp] private theorem diagonalAction_apply (c : Fin (m + 1) → Fin (m + 1)) (g : triangularGroup c)
    (k : Fin (m + 1)) (v : BlockSpace c k) (i : Block c k) :
    diagonalAction c g k v i = ∑ j : Block c k, matrix g.val i.val j.val * v j := rfl


/-- Coordinates grouped by their block label, without changing any vector. -/
private def splitCoordinates (c : Fin (m + 1) → Fin (m + 1)) :
    Space (m + 1) ≃ₗ[ZMod 2] (∀ k : Fin (m + 1), BlockSpace c k) where
  toFun v _ i := v i.val
  invFun v i := v (c i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv v := by
    funext k i
    obtain ⟨i, rfl⟩ := i
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The simultaneous literal block-diagonal embedding. -/
private noncomputable def diagonalLift (c : Fin (m + 1) → Fin (m + 1))
    (a : ∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) : LinearGroup (m + 1) :=
  ((splitCoordinates c).trans (LinearEquiv.piCongrRight a)).trans (splitCoordinates c).symm

@[simp] private theorem diagonalLift_apply (c : Fin (m + 1) → Fin (m + 1))
    (a : ∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) (v : Space (m + 1)) (i : Fin (m + 1)) :
    diagonalLift c a v i = a (c i) (fun j => v j.val) ⟨i, rfl⟩ := rfl

private theorem diagonalLift_mem (c : Fin (m + 1) → Fin (m + 1))
    (a : ∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) : diagonalLift c a ∈ triangularGroup c := by
  intro i j hij
  rw [matrix_apply, diagonalLift_apply]
  have hz : (fun t : Block c (c i) => standardBasis j t.val) = 0 := by
    funext t
    have hne : j ≠ t.val := by
      intro he
      have := t.property
      rw [← he] at this
      exact (ne_of_lt hij) this
    simp [standardBasis, Pi.basisFun_apply, hne.symm]
  rw [hz, map_zero]
  rfl

private theorem blockMatrix_diagonalLift (c : Fin (m + 1) → Fin (m + 1))
    (a : ∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) (k : Fin (m + 1)) :
    blockMatrix c k (diagonalLift c a) = LinearMap.toMatrix' (a k).toLinearMap := by
  ext i j
  change matrix (diagonalLift c a) i.val j.val = _
  rw [matrix_apply, diagonalLift_apply]
  obtain ⟨i, rfl⟩ := i
  change a (c i) (fun t => standardBasis j.val t.val) ⟨i, rfl⟩ = _
  rw [LinearMap.toMatrix'_apply]
  have hv : (fun t : Block c (c i) => standardBasis j.val t.val) = Pi.single j 1 := by
    funext t
    simp [standardBasis, Pi.basisFun_apply, Pi.single_apply, Subtype.ext_iff]
  rw [hv]
  rfl

/-- The displayed diagonal embedding is a right inverse to all block actions. -/
@[simp] private theorem diagonalAction_lift (c : Fin (m + 1) → Fin (m + 1))
    (a : ∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) :
    diagonalAction c ⟨diagonalLift c a, diagonalLift_mem c a⟩ = a := by
  funext k
  apply LinearEquiv.toLinearMap_injective
  change Matrix.toLin' (blockMatrix c k (diagonalLift c a)) = (a k).toLinearMap
  rw [blockMatrix_diagonalLift, Matrix.toLin'_toMatrix']

private theorem diagonalAction_surjective (c : Fin (m + 1) → Fin (m + 1)) :
    Function.Surjective (diagonalAction c) :=
  fun a => ⟨⟨diagonalLift c a, diagonalLift_mem c a⟩, diagonalAction_lift c a⟩


/-- Kernel elements have identity diagonal submatrices. -/
private theorem blockMatrix_eq_one_of_mem_ker (c : Fin (m + 1) → Fin (m + 1))
    (g : triangularGroup c) (hg : g ∈ (diagonalAction c).ker) (k : Fin (m + 1)) :
    blockMatrix c k g.val = 1 := by
  have he := congrFun (MonoidHom.mem_ker.mp hg) k
  have hl := congrArg LinearEquiv.toLinearMap he
  change Matrix.toLin' (blockMatrix c k g.val) = LinearMap.id at hl
  apply Matrix.toLin'.injective
  simpa using hl

/-- With consecutive blocks, the diagonal kernel lies in the full-flag two-group. -/
private theorem ker_le_standardBorel (c : Fin (m + 1) → Fin (m + 1)) (hc : Monotone c) :
    ((diagonalAction c).ker).map (triangularGroup c).subtype ≤ standardBorel := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_standardBorel_iff]
  intro i j hji
  change j < i at hji
  rcases (hc hji.le).lt_or_eq with hlt | heq
  · exact g.property hlt
  · have he := congrFun (congrFun (blockMatrix_eq_one_of_mem_ker c g hg (c i))
      ⟨i, rfl⟩) ⟨j, heq⟩
    simpa [blockMatrix, Matrix.one_apply, ne_of_gt hji] using he

private theorem diagonalKernel_isPGroup (c : Fin (m + 1) → Fin (m + 1)) (hc : Monotone c) :
    IsPGroup 2 (diagonalAction c).ker := by
  let f : (diagonalAction c).ker →* standardBorel :=
    { toFun g := ⟨g.val.val, ker_le_standardBorel c hc (Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro g h he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : standardBorel => x.val) he))
  exact standardBorel_isPGroup.of_injective f hf

private theorem diagonalTarget_twoCore (c : Fin (m + 1) → Fin (m + 1)) :
    pCore 2 (∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  funext k
  let f := Pi.evalMonoidHom (fun k : Fin (m + 1) => BinaryLinear.GL (BlockSpace c k)) k
  have hf : Function.Surjective f := by
    intro a
    exact ⟨Function.update 1 k a, Function.update_self ..⟩
  have hle : (pCore 2 (∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k))).map f ≤
      pCore 2 (BinaryLinear.GL (BlockSpace c k)) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  rw [linearGroup_twoCore_eq_bot] at hle
  exact hle (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

/-- No extra normal two-subgroup survives the diagonal action. -/
private theorem ker_diagonalAction_eq_twoCore (c : Fin (m + 1) → Fin (m + 1)) (hc : Monotone c) :
    (diagonalAction c).ker = pCore 2 (triangularGroup c) := by
  let : ∀ k : Fin (m + 1), Finite (BinaryLinear.GL (BlockSpace c k)) := fun k =>
    Finite.of_injective (fun g : BinaryLinear.GL (BlockSpace c k) => (g : BlockSpace c k → BlockSpace c k))
      DFunLike.coe_injective
  have h := (diagonalAction c).comap_pCore_of_ker_isPGroup
    (diagonalAction_surjective c) (diagonalKernel_isPGroup c hc)
  rwa [diagonalTarget_twoCore] at h

/-- The actual block-triangular group modulo its two-core. -/
private noncomputable def diagonalQuotientEquiv (c : Fin (m + 1) → Fin (m + 1)) (hc : Monotone c) :
    (triangularGroup c ⧸ pCore 2 (triangularGroup c)) ≃*
      (∀ k : Fin (m + 1), BinaryLinear.GL (BlockSpace c k)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_diagonalAction_eq_twoCore c hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (diagonalAction_surjective c))

@[simp] private theorem diagonalQuotientEquiv_mk (c : Fin (m + 1) → Fin (m + 1)) (hc : Monotone c)
    (g : triangularGroup c) :
    diagonalQuotientEquiv c hc (QuotientGroup.mk' _ g) = diagonalAction c g := rfl


/-- Label a coordinate by the number of flag cuts strictly preceding it. -/
private noncomputable def cutLabel (cuts : Set (Fin m)) (i : Fin (m + 1)) : Fin (m + 1) := by
  classical
  exact ⟨(Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < i.val)).card,
    lt_of_le_of_lt (Finset.card_filter_le _ _) (by simp)⟩

private theorem cutLabel_monotone (cuts : Set (Fin m)) : Monotone (cutLabel cuts) := by
  classical
  intro i j hij
  change (Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < i.val)).card ≤
    (Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < j.val)).card
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

private theorem cutLabel_lt_iff (cuts : Set (Fin m)) (i j : Fin (m + 1)) :
    cutLabel cuts j < cutLabel cuts i ↔
      ∃ k ∈ cuts, j.val ≤ k.val ∧ k.val < i.val := by
  classical
  change (Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < j.val)).card <
    (Finset.univ.filter (fun k : Fin m => k ∈ cuts ∧ k.val < i.val)).card ↔ _
  constructor
  · intro h
    obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_notMem_of_card_lt_card h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hk hkj
    exact ⟨k, hk.1, Nat.le_of_not_gt (hkj hk.1), hk.2⟩
  · rintro ⟨k, hk, hkj, hki⟩
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, lt_trans ht.2 (lt_of_le_of_lt hkj hki)⟩
    · intro he
      have hkm : k ∈ Finset.univ.filter (fun t : Fin m => t ∈ cuts ∧ t.val < i.val) := by
        simp [hk, hki]
      rw [← he] at hkm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkm
      omega

/-- The ordered-block group is precisely the actual partial-flag stabilizer. -/
private theorem triangularGroup_cutLabel (cuts : Set (Fin m)) :
    triangularGroup (cutLabel cuts) = cutStabilizer standardBasis cuts := by
  ext g
  rw [mem_standard_cutStabilizer_iff]
  change (∀ ⦃i j : Fin (m + 1)⦄, cutLabel cuts j < cutLabel cuts i → matrix g i j = 0) ↔ _
  constructor
  · intro h k hk i j hki hjk
    exact h ((cutLabel_lt_iff cuts i j).mpr ⟨k, hk, hjk, hki⟩)
  · intro h i j hij
    obtain ⟨k, hk, hjk, hki⟩ := (cutLabel_lt_iff cuts i j).mp hij
    exact h k hk i j hki hjk



private noncomputable def flagCoordinates (b : Basis m) (cuts : Set (Fin m)) :
    cutStabilizer b cuts ≃* triangularGroup (cutLabel cuts) :=
  ((MulAut.conj b.equivFun).subgroupMap (cutStabilizer b cuts)).trans
    (MulEquiv.subgroupCongr (by
      change (cutStabilizer b cuts).map (MulAut.conj b.equivFun).toMonoidHom = _
      rw [cutStabilizer_map_conj, triangularGroup_cutLabel]
      congr 1
      ext i j
      simp [standardBasis, Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]))

private def linearOrder (n : ℕ) : ℕ := ∏ j : Fin n, (2^n - 2^j.val)
private theorem coordinate_card {α : Type*} [Fintype α] :
    Nat.card (BinaryLinear.GL (α → ZMod 2)) = linearOrder (Nat.card α) := by
  rw [Nat.card_eq_fintype_card (α := α)]
  let e : (α → ZMod 2) ≃ₗ[ZMod 2] Space (Fintype.card α) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fintype.equivFin α).symm
  rw [Nat.card_congr (linearGroupCongr e).toEquiv,
    ← Nat.card_congr (matrixEquivLinear _).toEquiv, Matrix.card_GL_field]
  simp [linearOrder]
private def blockCount (s : Finset (Fin m)) (k : Fin (m + 1)) : ℕ :=
  (Finset.univ.filter fun i : Fin (m + 1) => (s.filter fun j => j.val < i.val).card = k.val).card
private theorem blockCount_eq (s : Finset (Fin m)) (k : Fin (m + 1)) :
    blockCount s k = Nat.card (Block (cutLabel (s : Set (Fin m))) k) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blockCount cutLabel
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Fin.ext_iff]
  have he : s.filter (fun j => j.val < i.val) =
      Finset.univ.filter (fun j : Fin m => j ∈ (s : Set (Fin m)) ∧ j.val < i.val) := by
    ext j
    simp
  rw [he]
  apply Iff.of_eq
  congr 3
private def leviOrder (s : Finset (Fin m)) : ℕ :=
  ∏ k : Fin (m + 1), linearOrder (blockCount s k)
private theorem quotient_card (b : Basis m) (cuts : Set (Fin m)) :
    Nat.card (cutStabilizer b cuts ⧸ pCore 2 (cutStabilizer b cuts)) =
      leviOrder cuts.toFinset := by
  classical
  let e := flagCoordinates b cuts
  rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv,
    Nat.card_congr (diagonalQuotientEquiv _ (cutLabel_monotone cuts)).toEquiv, Nat.card_pi]
  simp_rw [coordinate_card]
  simp_rw [leviOrder, blockCount_eq, Set.coe_toFinset]
private theorem cut_certificate (hm : m = 3 ∨ m = 4) :
    ∀ s : Finset (Fin m), 7 ∣ leviOrder s → s.card ≤ 2 := by
  rcases hm with rfl | rfl <;> decide +kernel
private theorem cutLabel_le_two (cuts : Set (Fin m)) (h : cuts.toFinset.card ≤ 2)
    (i : Fin (m + 1)) : (cutLabel cuts i).val ≤ 2 := by
  classical
  change (Finset.univ.filter (fun j : Fin m => j ∈ cuts ∧ j.val < i.val)).card ≤ 2
  apply le_trans (Finset.card_le_card (t := cuts.toFinset) ?_) h
  intro j hj
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset] using (Finset.mem_filter.mp hj).2.1

private def Strict (c : Fin (m + 1) → Fin (m + 1))
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) : Prop :=
  ∀ i j, c j ≤ c i → A i j = 0

private theorem strict_difference (c : Fin (m + 1) → Fin (m + 1))
    (g : triangularGroup c) (hg : g ∈ (diagonalAction c).ker) :
    Strict c (matrix g.val - 1) := by
  intro i j hij
  change matrix g.val i j - (1 : Matrix _ _ (ZMod 2)) i j = 0
  apply sub_eq_zero.mpr
  rcases hij.lt_or_eq with hlt | heq
  · rw [g.property hlt, Matrix.one_apply, if_neg (fun he => (ne_of_lt hlt) (congrArg c he.symm))]
  · have he := congrFun (congrFun (blockMatrix_eq_one_of_mem_ker c g hg (c i))
      ⟨i, rfl⟩) ⟨j, heq⟩
    simpa [blockMatrix, Matrix.one_apply, Subtype.ext_iff] using he

private theorem strict_triple_zero (c : Fin (m + 1) → Fin (m + 1))
    (hc : ∀ i, (c i).val ≤ 2)
    (A B C : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))
    (hA : Strict c A) (hB : Strict c B) (hC : Strict c C) : A * B * C = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  by_cases ha : c l ≤ c i
  · rw [hA i l ha, zero_mul, zero_mul]
  by_cases hb : c k ≤ c l
  · rw [hB l k hb, mul_zero, zero_mul]
  have hc' : c j ≤ c k := by
    have hi := hc i
    have hj := hc j
    change ¬ (c l).val ≤ (c i).val at ha
    change ¬ (c k).val ≤ (c l).val at hb
    change (c j).val ≤ (c k).val
    omega
  rw [hC k j hc', mul_zero]

private theorem kernel_commutator_commutes (c : Fin (m + 1) → Fin (m + 1))
    (hc : ∀ i, (c i).val ≤ 2)
    (g h k : (diagonalAction c).ker) : Commute ⁅g, h⁆ k := by
  let M := matrixHom (m := m)
  let a := M g.val.val - 1
  let b := M h.val.val - 1
  let d := M k.val.val - 1
  have tz (x y z : (diagonalAction c).ker) :
      (M x.val.val - 1) * (M y.val.val - 1) * (M z.val.val - 1) = 0 :=
    strict_triple_zero c hc _ _ _ (strict_difference c x.val x.property)
      (strict_difference c y.val y.property) (strict_difference c z.val z.property)
  have invprod (x : (diagonalAction c).ker) : M x.val.val * M x⁻¹.val.val = 1 := by
    change M x.val.val * M x.val.val⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]
  have hx : M ⁅g.val.val, h.val.val⁆ = 1 + (a * b - b * a) := by
    have he : a * b - b * a = M g.val.val * M h.val.val - M h.val.val * M g.val.val := by
      dsimp [a,b]
      noncomm_ring
    have hr (x : (diagonalAction c).ker) :
        (a * b - b * a) * M x.val.val = a * b - b * a := by
      have h1 := tz g h x
      have h2 := tz h g x
      change a * b * (M x.val.val - 1) = 0 at h1
      change b * a * (M x.val.val - 1) = 0 at h2
      rw [mul_sub, mul_one, sub_eq_zero] at h1 h2
      rw [sub_mul, h1, h2]
    calc
      _ = (a * b - b * a) * M g⁻¹.val.val * M h⁻¹.val.val + 1 := by
        rw [he, sub_mul, sub_mul, commutatorElement_def, map_mul, map_mul, map_mul]
        have hcancel : M h.val.val * M g.val.val * M g⁻¹.val.val * M h⁻¹.val.val = 1 := by
          rw [mul_assoc (M h.val.val) (M g.val.val), invprod, mul_one, invprod]
        rw [hcancel, sub_add_cancel]
        rfl
      _ = 1 + (a * b - b * a) := by
        rw [hr,hr]
        exact add_comm _ _
  apply Subtype.ext
  apply Subtype.ext
  apply (slEquivLinear (m + 1)).symm.injective
  apply Subtype.ext
  change M (⁅g.val.val, h.val.val⁆ * k.val.val) = M (k.val.val * ⁅g.val.val, h.val.val⁆)
  rw [map_mul,map_mul,hx]
  have h1 : (a * b - b * a) * d = 0 := by
    rw [sub_mul]
    exact (congrArg₂ (· - ·) (tz g h k) (tz h g k)).trans (sub_self _)
  have h2 : d * (a * b - b * a) = 0 := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc]
    exact (congrArg₂ (· - ·) (tz k g h) (tz k h g)).trans (sub_self _)
  have hd : M k.val.val = 1 + d := by dsimp [d]; noncomm_ring
  rw [hd]
  simp only [add_mul, mul_add, one_mul, mul_one, h1, h2]
  abel


private theorem kernel_third_eq_bot (c : Fin (m + 1) → Fin (m + 1))
    (hc : ∀ i, (c i).val ≤ 2) :
    ⁅⁅(⊤ : Subgroup (diagonalAction c).ker), (⊤ : Subgroup (diagonalAction c).ker)⁆, (⊤ : Subgroup (diagonalAction c).ker)⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ]
  apply commutator_le.mpr
  intro g _ h _
  exact mem_center_iff.mpr (fun k => (kernel_commutator_commutes c hc g h k).symm.eq)

private theorem third_map (A : Type*) [Group A] {H : Type*} [Group H]
    (f : A →* H) (h : ⁅⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆, (⊤ : Subgroup A)⁆ = ⊥) :
    ⁅⁅f.range, f.range⁆, f.range⁆ = ⊥ := by
  have he := congrArg (fun P : Subgroup A => P.map f) h
  simpa only [map_commutator,← MonoidHom.range_eq_map,Subgroup.map_bot] using he

/-- A full Sylow overgroup of order divisible by seven in binary dimension
four or five has two-core of nilpotency class at most two. -/
theorem sylow_overgroup_twoCore_third_eq_bot {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) (J : Subgroup (LinearGroup n))
    (hSJ : (S : Subgroup _) ≤ J) (h7 : 7 ∣ Nat.card J) :
    ⁅⁅J.pCoreIn 2, J.pCoreIn 2⁆, J.pCoreIn 2⁆ = ⊥ := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨b,cuts,_,rfl⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S J hSJ
  have h7q : 7 ∣ Nat.card (cutStabilizer b cuts ⧸ pCore 2 (cutStabilizer b cuts)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := cutStabilizer b cuts)).exists_card_eq
    rw [← (pCore 2 (cutStabilizer b cuts)).card_mul_index,hk] at h7
    exact ((by decide : Nat.Coprime 7 2).pow_right k).dvd_of_dvd_mul_left h7
  rw [quotient_card] at h7q
  have hcuts := cut_certificate (by omega : m = 3 ∨ m = 4) cuts.toFinset h7q
  let e := flagCoordinates b cuts
  let c := cutLabel cuts
  let f : (diagonalAction c).ker →* LinearGroup (m + 1) :=
    (cutStabilizer b cuts).subtype.comp
      (e.symm.toMonoidHom.comp (diagonalAction c).ker.subtype)
  have hr : f.range = (cutStabilizer b cuts).pCoreIn 2 := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,range_subtype]
    rw [ker_diagonalAction_eq_twoCore c (cutLabel_monotone cuts),pCore_map_iso]
    rfl
  rw [← hr]
  exact third_map _ f (kernel_third_eq_bot c (cutLabel_le_two cuts hcuts))

/-- The actual two-core of a subgroup normalized by the full Sylow has the
same class-two bound whenever its order is divisible by seven. -/
theorem normalized_twoCore_third_eq_bot {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) (B : Subgroup (LinearGroup n))
    (hSB : (S : Subgroup (LinearGroup n)) ≤ normalizer (B : Set (LinearGroup n))) (h7 : 7 ∣ Nat.card B) :
    ⁅⁅B.pCoreIn 2, B.pCoreIn 2⁆, B.pCoreIn 2⁆ = ⊥ := by
  let J : Subgroup (LinearGroup n) := B ⊔ (S : Subgroup (LinearGroup n))
  have hBJ : B ≤ J := le_sup_left
  have hSJ : (S : Subgroup (LinearGroup n)) ≤ J := le_sup_right
  have hJB : J ≤ normalizer (B : Set (LinearGroup n)) := sup_le B.le_normalizer hSB
  have hc : B.pCoreIn 2 ≤ J.pCoreIn 2 := pCoreIn_mono_of_normalizes hBJ hJB
  have hJ7 : 7 ∣ Nat.card J := h7.trans (card_dvd_of_le hBJ)
  have hz : ⁅⁅J.pCoreIn 2, J.pCoreIn 2⁆, J.pCoreIn 2⁆ = ⊥ :=
    sylow_overgroup_twoCore_third_eq_bot hn S J hSJ hJ7
  exact eq_bot_iff.mpr ((commutator_mono (commutator_mono hc hc) hc).trans hz.le)

end BinaryLinear.SevenFlagCore
