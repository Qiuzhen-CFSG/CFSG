module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds
public import Theory.Mathieu.M12.SmallParabolicPair.SwapCoreCoordinates
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Marked quaternion coordinates and the nonsplit outer swap

The original four lifted generators give the same central product of quaternion
factors as in the degree-12 model. A word in the fixed ATLAS generators gives an
outer element interchanging those factors whose square is the original `z`.
Thus the factor swap here is not the involutory swap in `QuaternionSwapModel`.
All permutation calculations are kernel checked. The word was found with GAP;
no GAP group identification or cardinality is used as a proof.

Source: Aschbacher--Smith, E.2.16 (p.228), F.1.12(I)(13) (p.263), and
14.2.21 (p.988), `refs/quasithin.pdf`. This module retains the degree-24
coordinates from Extension/Seeds and assumes only its marked `InnerModel`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension
namespace FirstParabolic
set_option maxRecDepth 100000

def zPerm : Equiv.Perm (Fin 24) where
  toFun := ![0,14,23,3,4,17,12,22,8,9,20,15,6,18,1,11,16,5,13,19,10,21,7,2]
  invFun := ![0,14,23,3,4,17,12,22,8,9,20,15,6,18,1,11,16,5,13,19,10,21,7,2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem z_val : z.val = zPerm := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

def leftIPerm : Equiv.Perm (Fin 24) where
  toFun := ![16,13,7,3,21,10,15,23,8,9,17,6,11,14,18,12,0,20,1,19,5,4,2,22]
  invFun := ![16,18,22,3,21,20,11,2,8,9,5,12,15,1,13,6,0,10,14,19,17,4,23,7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem leftI_val : leftI.val = leftIPerm := by decide +kernel

def leftJPerm : Equiv.Perm (Fin 24) where
  toFun := ![4,23,1,3,0,15,20,18,8,9,6,5,10,7,2,17,21,11,22,19,12,16,13,14]
  invFun := ![4,2,14,3,0,11,10,13,8,9,12,17,20,22,23,5,21,15,7,19,6,16,18,1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem leftJ_val : leftJ.val = leftJPerm := by decide +kernel

def rightIPerm : Equiv.Perm (Fin 24) where
  toFun := ![0,18,7,19,4,10,11,23,9,8,17,12,15,1,13,6,16,20,14,3,5,21,2,22]
  invFun := ![0,13,22,19,4,20,15,2,9,8,5,6,11,14,18,12,16,10,1,3,17,21,23,7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem rightI_val : rightI.val = rightIPerm := by decide +kernel

def rightJPerm : Equiv.Perm (Fin 24) where
  toFun := ![0,2,14,9,4,15,10,18,19,3,12,5,20,7,23,17,16,11,22,8,6,21,13,1]
  invFun := ![0,23,1,9,4,11,20,13,19,3,6,17,10,22,2,5,16,15,7,8,12,21,18,14]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem rightJ_val : rightJ.val = rightJPerm := by decide +kernel

def quaternionPerm (i j : Equiv.Perm (Fin 24)) : QuaternionGroup 2 → Equiv.Perm (Fin 24)
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

/-- Quaternion coordinates in the fixed degree-24 carrier. -/
def quaternionWord (i j : Carrier) : QuaternionGroup 2 → Carrier
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

theorem quaternionWord_left_val (q : QuaternionGroup 2) :
    (quaternionWord leftI leftJ q).val = quaternionPerm leftIPerm leftJPerm q := by
  cases q <;> simp [quaternionWord, quaternionPerm, leftI_val, leftJ_val]

theorem quaternionWord_right_val (q : QuaternionGroup 2) :
    (quaternionWord rightI rightJ q).val = quaternionPerm rightIPerm rightJPerm q := by
  cases q <;> simp [quaternionWord, quaternionPerm, rightI_val, rightJ_val]

def leftLift : QuaternionGroup 2 →* Carrier where
  toFun := quaternionWord leftI leftJ
  map_one' := by apply Subtype.ext; rw [quaternionWord_left_val]; decide +kernel
  map_mul' q r := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, quaternionWord_left_val]
    have h : ∀ q r : QuaternionGroup 2,
        quaternionPerm leftIPerm leftJPerm (q*r) =
          quaternionPerm leftIPerm leftJPerm q * quaternionPerm leftIPerm leftJPerm r := by
      decide +kernel
    exact h q r

def rightLift : QuaternionGroup 2 →* Carrier where
  toFun := quaternionWord rightI rightJ
  map_one' := by apply Subtype.ext; rw [quaternionWord_right_val]; decide +kernel
  map_mul' q r := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, quaternionWord_right_val]
    have h : ∀ q r : QuaternionGroup 2,
        quaternionPerm rightIPerm rightJPerm (q*r) =
          quaternionPerm rightIPerm rightJPerm q * quaternionPerm rightIPerm rightJPerm r := by
      decide +kernel
    exact h q r

theorem map_leftLift (m : InnerModel) (q : QuaternionGroup 2) :
    m.embedding (M12SmallPair.leftEmbedding q) = leftLift q := by
  have hi := map_leftI m.embedding m.embedding_originalA m.embedding_originalB
  have hj := map_leftJ m.embedding m.embedding_originalA m.embedding_originalB
  cases q <;> simp [M12SmallPair.leftEmbedding, M12SmallPair.quaternionMap,
    leftLift, quaternionWord, hi, hj]

theorem map_rightLift (m : InnerModel) (q : QuaternionGroup 2) :
    m.embedding (M12SmallPair.rightEmbedding q) = rightLift q := by
  have hi := map_rightI m.embedding m.embedding_originalA m.embedding_originalB
  have hj := map_rightJ m.embedding m.embedding_originalA m.embedding_originalB
  cases q <;> simp [M12SmallPair.rightEmbedding, M12SmallPair.quaternionMap,
    rightLift, quaternionWord, hi, hj]

def leftFactor : Subgroup Carrier := leftLift.range
def rightFactor : Subgroup Carrier := rightLift.range
/-- The literal image of the two original quaternion pairs. -/
def quaternionCore : Subgroup Carrier := leftFactor ⊔ rightFactor

theorem quaternionCore_eq_map (m : InnerModel) :
    quaternionCore = M12SmallPair.core.map m.embedding := by
  unfold quaternionCore M12SmallPair.core leftFactor rightFactor
    M12SmallPair.leftFactor M12SmallPair.rightFactor
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]
  congr 1
  · congr 1; apply MonoidHom.ext; intro q; exact (map_leftLift m q).symm
  · congr 1; apply MonoidHom.ext; intro q; exact (map_rightLift m q).symm

/-- The marked degree-12 to degree-24 core equivalence. -/
noncomputable def quaternionCoreEquiv (m : InnerModel) :
    M12SmallPair.core ≃* quaternionCore :=
  (Subgroup.equivMapOfInjective _ m.embedding m.embedding_injective).trans
    (MulEquiv.subgroupCongr (quaternionCore_eq_map m).symm)

theorem quaternionCoreEquiv_apply (m : InnerModel) (q : M12SmallPair.core) :
    (quaternionCoreEquiv m q : Carrier) = m.embedding q := rfl

/-- Reuse of the existing intrinsic quaternion central product, with its markings. -/
noncomputable def splitQuaternionCoreEquiv (m : InnerModel) :
    QuaternionSwapModel.QK ≃* quaternionCore :=
  M12SmallPair.SwapCoreCoordinates.coreEquiv.trans (quaternionCoreEquiv m)

noncomputable def quaternionData (m : InnerModel) :
    Subgroup.QuaternionCentralProductData quaternionCore :=
  M12SmallPair.coreQuaternionData.map (quaternionCoreEquiv m)

theorem card_quaternionCore (m : InnerModel) : Nat.card quaternionCore = 32 :=
  (quaternionData m).card

theorem quaternionCore_extraspecial (m : InnerModel) :
    IsExtraspecial 2 quaternionCore := (quaternionData m).extraspecial

theorem mem_quaternionCore (m : InnerModel) (g : Carrier) :
    g ∈ quaternionCore ↔ ∃ q r : QuaternionGroup 2, leftLift q * rightLift r = g := by
  rw [quaternionCore_eq_map m]
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨q,r,rfl⟩ := (M12SmallPair.mem_core x).mp hx
    exact ⟨q,r, by rw [map_mul, map_leftLift, map_rightLift]⟩
  · rintro ⟨q,r,rfl⟩
    refine ⟨_, (M12SmallPair.mem_core _).mpr ⟨q,r,rfl⟩, ?_⟩
    rw [map_mul, map_leftLift, map_rightLift]

theorem quaternionCore_le_inner (m : InnerModel) : quaternionCore ≤ inner := by
  rw [quaternionCore_eq_map m, ← m.embedding_range]
  exact Subgroup.map_le_range _ _

theorem z_mem_quaternionCore (m : InnerModel) : z ∈ quaternionCore := by
  rw [quaternionCore_eq_map m]
  exact ⟨_,M12SmallPair.z_mem_core,
    map_z m.embedding m.embedding_originalA m.embedding_originalB⟩

theorem natural_le_quaternionCore (m : InnerModel) : natural ≤ quaternionCore := by
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl | rfl)
  · exact z_mem_quaternionCore m
  · rw [quaternionCore_eq_map m]
    exact ⟨_,M12SmallPair.natural_le_core M12SmallPair.v_mem_natural,
      map_v m.embedding m.embedding_originalA m.embedding_originalB⟩

private def outerWord : List (Fin 3) → Equiv.Perm (Fin 24)
  | [] => 1
  | i :: w => (if i = 0 then generatorA else if i = 1 then generatorB else generatorB⁻¹) *
      outerWord w

private theorem outerWord_mem (w : List (Fin 3)) : outerWord w ∈ group := by
  have ha : generatorA ∈ group := Subgroup.subset_closure (by simp)
  have hb : generatorB ∈ group := Subgroup.subset_closure (by simp)
  induction w with
  | nil => exact group.one_mem
  | cons i w ih =>
    apply group.mul_mem _ ih
    split_ifs
    · exact ha
    · exact hb
    · exact group.inv_mem hb

/-- A strict factor-swap lift, with its literal degree-24 action. -/
def nonsplitSwapPerm : Equiv.Perm (Fin 24) where
  toFun := ![9,6,20,4,3,22,14,5,16,0,2,18,1,11,12,13,8,7,15,21,23,19,17,10]
  invFun := ![9,12,10,4,3,7,1,17,16,0,23,13,14,15,6,18,8,22,11,21,2,19,5,20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem nonsplitSwapPerm_mem : nonsplitSwapPerm ∈ group := by
  have h : nonsplitSwapPerm = outerWord [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1] := by decide +kernel
  rw [h]
  exact outerWord_mem _

def nonsplitSwap : Carrier := ⟨nonsplitSwapPerm, nonsplitSwapPerm_mem⟩

theorem nonsplitSwap_square : nonsplitSwap ^ 2 = z := by
  apply Subtype.ext
  change nonsplitSwapPerm ^ 2 = z.val
  exact (show nonsplitSwapPerm ^ 2 = zPerm by decide +kernel).trans z_val.symm

theorem nonsplitSwap_left (q : QuaternionGroup 2) :
    nonsplitSwap * leftLift q * nonsplitSwap⁻¹ = rightLift q := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change nonsplitSwapPerm * (quaternionWord leftI leftJ q).val * nonsplitSwapPerm⁻¹ =
    (quaternionWord rightI rightJ q).val
  rw [quaternionWord_left_val, quaternionWord_right_val]
  have h : ∀ q : QuaternionGroup 2,
      nonsplitSwapPerm * quaternionPerm leftIPerm leftJPerm q * nonsplitSwapPerm⁻¹ =
        quaternionPerm rightIPerm rightJPerm q := by decide +kernel
  exact h q

theorem nonsplitSwap_right (q : QuaternionGroup 2) :
    nonsplitSwap * rightLift q * nonsplitSwap⁻¹ = leftLift q := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  change nonsplitSwapPerm * (quaternionWord rightI rightJ q).val * nonsplitSwapPerm⁻¹ =
    (quaternionWord leftI leftJ q).val
  rw [quaternionWord_right_val, quaternionWord_left_val]
  have h : ∀ q : QuaternionGroup 2,
      nonsplitSwapPerm * quaternionPerm rightIPerm rightJPerm q * nonsplitSwapPerm⁻¹ =
        quaternionPerm leftIPerm leftJPerm q := by decide +kernel
  exact h q

theorem nonsplitSwap_mem_firstParabolic : nonsplitSwap ∈ firstParabolic := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change nonsplitSwapPerm * z.val = z.val * nonsplitSwapPerm
  calc
    nonsplitSwapPerm * z.val = nonsplitSwapPerm * zPerm := congrArg (nonsplitSwapPerm * ·) z_val
    _ = zPerm * nonsplitSwapPerm := by decide +kernel
    _ = z.val * nonsplitSwapPerm := congrArg (· * nonsplitSwapPerm) z_val.symm

/-- The proposed outer core is generated by the actual quaternion core and lift. -/
def outerCore : Subgroup Carrier := quaternionCore ⊔ Subgroup.zpowers nonsplitSwap

private def blockPreserver : Subgroup Carrier where
  carrier := {g | ∀ x, (∃ i, blockLabel i = x) ↔ ∃ i, blockLabel i = g.val x}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb x
    exact (hb x).trans (ha (b.val x))
  inv_mem' := by
    intro a ha x
    simpa using (ha (a.val⁻¹ x)).symm

theorem inner_preserves_block (g : Carrier) (hg : g ∈ inner) (x : Fin 24) :
    (∃ i, blockLabel i = x) ↔ ∃ i, blockLabel i = g.val x := by
  have h : inner ≤ blockPreserver := by
    apply (Subgroup.closure_le _).mpr
    rintro a (rfl | rfl)
    · change ∀ x, (∃ i, blockLabel i = x) ↔ ∃ i, blockLabel i = innerAPerm x
      decide +kernel
    · change ∀ x, (∃ i, blockLabel i = x) ↔ ∃ i, blockLabel i = innerBPerm x
      decide +kernel
  exact h hg x

theorem nonsplitSwap_not_mem_inner : nonsplitSwap ∉ inner := by
  intro h
  have he := (inner_preserves_block nonsplitSwap h (blockLabel 0)).mp ⟨0,rfl⟩
  have hn : ¬ ∃ i, blockLabel i = nonsplitSwap.val (blockLabel 0) := by decide +kernel
  exact hn he

end FirstParabolic
end Sporadic.Mathieu.M12ExceptionalExtension
