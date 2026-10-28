module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Coordinates

/-!
# Diagonal actions of binary five-dimensional flags

An ordered partition of the five coordinates defines an actual block-triangular
subgroup. Its diagonal submatrices give a surjective homomorphism to the product
of the corresponding binary general linear groups. The displayed block-diagonal
embedding supplies a right inverse. For consecutive blocks the kernel lies in
the full-flag two-group, and every diagonal factor has trivial two-core. Thus
the kernel is exactly the intrinsic two-core.

Counting the cuts preceding each coordinate identifies this subgroup with the
actual standard partial-flag stabilizer. This is the common quotient calculation
for the nonadjacent two-node and solvable-flag arguments in Aschbacher–Smith,
combined manuscript of 1 March 2004, 13.8.25, printed pp.959–960 (PDF pp.976–977).
The factor identifications and residual markings are separate statements.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi.TwoNodes
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups

private instance : Finite (LinearGroup 5) := Finite.of_injective
  (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

noncomputable def matrixHom : LinearGroup 5 →* Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.SpecialLinearGroup.coeMonoidHom.comp (slEquivLinear 5).symm.toMonoidHom

@[simp] theorem matrixHom_apply (g : LinearGroup 5) : matrixHom g = matrix g := rfl

/-- Actual automorphisms upper triangular with respect to an ordered partition. -/
noncomputable def triangularGroup (c : Fin 5 → Fin 5) : Subgroup (LinearGroup 5) where
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

abbrev Block (c : Fin 5 → Fin 5) (k : Fin 5) := {i : Fin 5 // c i = k}
abbrev BlockSpace (c : Fin 5 → Fin 5) (k : Fin 5) := Block c k → ZMod 2

/-- The literal diagonal submatrix on a block. -/
noncomputable def blockMatrix (c : Fin 5 → Fin 5) (k : Fin 5) (g : LinearGroup 5) :
    Matrix (Block c k) (Block c k) (ZMod 2) :=
  (matrix g).submatrix Subtype.val Subtype.val

@[simp] theorem blockMatrix_one (c : Fin 5 → Fin 5) (k : Fin 5) :
    blockMatrix c k 1 = 1 := by
  change (matrixHom 1).submatrix _ _ = _
  rw [map_one, Matrix.submatrix_one _ Subtype.val_injective]

set_option backward.isDefEq.respectTransparency false in
theorem blockMatrix_mul (c : Fin 5 → Fin 5) (k : Fin 5)
    (g h : triangularGroup c) :
    blockMatrix c k (g.val * h.val) = blockMatrix c k g.val * blockMatrix c k h.val := by
  ext i j
  change (matrixHom (g.val * h.val)) i.val j.val = _
  rw [map_mul, Matrix.mul_apply]
  change (∑ t : Fin 5, matrix g.val i.val t * matrix h.val t j.val) =
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
noncomputable def diagonalFactor (c : Fin 5 → Fin 5) (k : Fin 5)
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
noncomputable def diagonalAction (c : Fin 5 → Fin 5) :
    triangularGroup c →* (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) where
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

@[simp] theorem diagonalAction_apply (c : Fin 5 → Fin 5) (g : triangularGroup c)
    (k : Fin 5) (v : BlockSpace c k) (i : Block c k) :
    diagonalAction c g k v i = ∑ j : Block c k, matrix g.val i.val j.val * v j := rfl


/-- Coordinates grouped by their block label, without changing any vector. -/
def splitCoordinates (c : Fin 5 → Fin 5) :
    Space 5 ≃ₗ[ZMod 2] (∀ k : Fin 5, BlockSpace c k) where
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
noncomputable def diagonalLift (c : Fin 5 → Fin 5)
    (a : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) : LinearGroup 5 :=
  ((splitCoordinates c).trans (LinearEquiv.piCongrRight a)).trans (splitCoordinates c).symm

@[simp] theorem diagonalLift_apply (c : Fin 5 → Fin 5)
    (a : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) (v : Space 5) (i : Fin 5) :
    diagonalLift c a v i = a (c i) (fun j => v j.val) ⟨i, rfl⟩ := rfl

theorem diagonalLift_mem (c : Fin 5 → Fin 5)
    (a : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) : diagonalLift c a ∈ triangularGroup c := by
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

theorem blockMatrix_diagonalLift (c : Fin 5 → Fin 5)
    (a : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) (k : Fin 5) :
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
@[simp] theorem diagonalAction_lift (c : Fin 5 → Fin 5)
    (a : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) :
    diagonalAction c ⟨diagonalLift c a, diagonalLift_mem c a⟩ = a := by
  funext k
  apply LinearEquiv.toLinearMap_injective
  change Matrix.toLin' (blockMatrix c k (diagonalLift c a)) = (a k).toLinearMap
  rw [blockMatrix_diagonalLift, Matrix.toLin'_toMatrix']

theorem diagonalAction_surjective (c : Fin 5 → Fin 5) :
    Function.Surjective (diagonalAction c) :=
  fun a => ⟨⟨diagonalLift c a, diagonalLift_mem c a⟩, diagonalAction_lift c a⟩


/-- Kernel elements have identity diagonal submatrices. -/
theorem blockMatrix_eq_one_of_mem_ker (c : Fin 5 → Fin 5)
    (g : triangularGroup c) (hg : g ∈ (diagonalAction c).ker) (k : Fin 5) :
    blockMatrix c k g.val = 1 := by
  have he := congrFun (MonoidHom.mem_ker.mp hg) k
  have hl := congrArg LinearEquiv.toLinearMap he
  change Matrix.toLin' (blockMatrix c k g.val) = LinearMap.id at hl
  apply Matrix.toLin'.injective
  simpa using hl

/-- With consecutive blocks, the diagonal kernel lies in the full-flag two-group. -/
theorem ker_le_standardBorel (c : Fin 5 → Fin 5) (hc : Monotone c) :
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

theorem diagonalKernel_isPGroup (c : Fin 5 → Fin 5) (hc : Monotone c) :
    IsPGroup 2 (diagonalAction c).ker := by
  let f : (diagonalAction c).ker →* standardBorel :=
    { toFun g := ⟨g.val.val, ker_le_standardBorel c hc (Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro g h he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : standardBorel => x.val) he))
  exact standardBorel_isPGroup.of_injective f hf

private theorem diagonalTarget_twoCore (c : Fin 5 → Fin 5) :
    pCore 2 (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  funext k
  let f := Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace c k)) k
  have hf : Function.Surjective f := by
    intro a
    exact ⟨Function.update 1 k a, Function.update_self ..⟩
  have hle : (pCore 2 (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k))).map f ≤
      pCore 2 (BinaryLinear.GL (BlockSpace c k)) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  rw [linearGroup_twoCore_eq_bot] at hle
  exact hle (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

/-- No extra normal two-subgroup survives the diagonal action. -/
theorem ker_diagonalAction_eq_twoCore (c : Fin 5 → Fin 5) (hc : Monotone c) :
    (diagonalAction c).ker = pCore 2 (triangularGroup c) := by
  let : ∀ k : Fin 5, Finite (BinaryLinear.GL (BlockSpace c k)) := fun k =>
    Finite.of_injective (fun g : BinaryLinear.GL (BlockSpace c k) => (g : BlockSpace c k → BlockSpace c k))
      DFunLike.coe_injective
  have h := (diagonalAction c).comap_pCore_of_ker_isPGroup
    (diagonalAction_surjective c) (diagonalKernel_isPGroup c hc)
  rwa [diagonalTarget_twoCore] at h

/-- The actual block-triangular group modulo its two-core. -/
noncomputable def diagonalQuotientEquiv (c : Fin 5 → Fin 5) (hc : Monotone c) :
    (triangularGroup c ⧸ pCore 2 (triangularGroup c)) ≃*
      (∀ k : Fin 5, BinaryLinear.GL (BlockSpace c k)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_diagonalAction_eq_twoCore c hc).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (diagonalAction_surjective c))

@[simp] theorem diagonalQuotientEquiv_mk (c : Fin 5 → Fin 5) (hc : Monotone c)
    (g : triangularGroup c) :
    diagonalQuotientEquiv c hc (QuotientGroup.mk' _ g) = diagonalAction c g := rfl


/-- Label a coordinate by the number of flag cuts strictly preceding it. -/
noncomputable def cutLabel (cuts : Set (Fin 4)) (i : Fin 5) : Fin 5 := by
  classical
  exact ⟨(Finset.univ.filter (fun k : Fin 4 => k ∈ cuts ∧ k.val < i.val)).card,
    lt_of_le_of_lt (Finset.card_filter_le _ _) (by decide)⟩

theorem cutLabel_monotone (cuts : Set (Fin 4)) : Monotone (cutLabel cuts) := by
  classical
  intro i j hij
  change (Finset.univ.filter (fun k : Fin 4 => k ∈ cuts ∧ k.val < i.val)).card ≤
    (Finset.univ.filter (fun k : Fin 4 => k ∈ cuts ∧ k.val < j.val)).card
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

theorem cutLabel_lt_iff (cuts : Set (Fin 4)) (i j : Fin 5) :
    cutLabel cuts j < cutLabel cuts i ↔
      ∃ k ∈ cuts, j.val ≤ k.val ∧ k.val < i.val := by
  classical
  change (Finset.univ.filter (fun k : Fin 4 => k ∈ cuts ∧ k.val < j.val)).card <
    (Finset.univ.filter (fun k : Fin 4 => k ∈ cuts ∧ k.val < i.val)).card ↔ _
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
      have hkm : k ∈ Finset.univ.filter (fun t : Fin 4 => t ∈ cuts ∧ t.val < i.val) := by
        simp [hk, hki]
      rw [← he] at hkm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkm
      omega

/-- The ordered-block group is precisely the actual partial-flag stabilizer. -/
theorem triangularGroup_cutLabel (cuts : Set (Fin 4)) :
    triangularGroup (cutLabel cuts) = flagStabilizer standardBasis cuts := by
  ext g
  rw [mem_standard_flagStabilizer_iff]
  change (∀ ⦃i j : Fin 5⦄, cutLabel cuts j < cutLabel cuts i → matrix g i j = 0) ↔ _
  constructor
  · intro h k hk i j hki hjk
    exact h ((cutLabel_lt_iff cuts i j).mpr ⟨k, hk, hjk, hki⟩)
  · intro h i j hij
    obtain ⟨k, hk, hjk, hki⟩ := (cutLabel_lt_iff cuts i j).mp hij
    exact h k hk i j hki hjk

end BinaryLinear.SmallParabolicLevi.TwoNodes

end
