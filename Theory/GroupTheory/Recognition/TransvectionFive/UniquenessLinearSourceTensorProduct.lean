module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRankOneStabilizer
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.ZMod
public import Theory.LinearAlgebra.BinaryTwoTransitivity
import Mathlib.Tactic.FinCases

/-!
# The binary rectangle tensor symmetry group

The full additive symmetry group of the two-by-three rank-one locus is
GL₃(2) × S₃. The three-space factor acts on both rows, while S₃ permutes
the three nonzero vectors of the two-space factor. These actions commute
and their product is faithful. Its orbit on rank-one vectors is all 21
vectors, and the preceding point-stabilizer theorem proves surjectivity.
The exported action equation retains the two original tensor factors.

The finite computations concern only six-bit vectors, three-bit vectors,
and the six permutations of three letters. XOR preservation is proved
algebraically. This is the concrete action identification needed for
Aschbacher, *Sporadic Groups* (1994), 40.3 and 40.5(1), pp.217–219;
no ambient group identification or splitting is assumed.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
private abbrev Small := BitVec 3
private def pack (u v : Small) : Code := u.zeroExtend 6 ^^^ (v.zeroExtend 6 <<< 3)
private def lo (x : Code) : Small := x.truncate 3
private def hi (x : Code) : Small := (x >>> 3).truncate 3
private theorem unpack_pack : ∀ u v : Small, lo (pack u v) = u ∧ hi (pack u v) = v := by decide
private theorem pack_unpack : ∀ x : Code, pack (lo x) (hi x) = x := by decide
private theorem pack_xor : ∀ u v a b : Small,
    pack (u ^^^ a) (v ^^^ b) = pack u v ^^^ pack a b := by decide
private theorem unpack_xor : ∀ x y : Code,
    lo (x ^^^ y) = lo x ^^^ lo y ∧ hi (x ^^^ y) = hi x ^^^ hi y := by decide
private theorem pure_pack : ∀ u v : Small,
    pure (pack u v) = true ↔ (u ≠ 0 ∨ v ≠ 0) ∧ (u = 0 ∨ v = 0 ∨ u = v) := by decide
private def split : Code ≃ Small × Small where
  toFun x := (lo x, hi x)
  invFun p := pack p.1 p.2
  left_inv := pack_unpack
  right_inv p := Prod.ext (unpack_pack p.1 p.2).1 (unpack_pack p.1 p.2).2

private def smallGroup : Subgroup (Equiv.Perm Small) where
  carrier := {a | ∀ u v, a (u ^^^ v) = a u ^^^ a v}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb u v
    change a (b (u ^^^ v)) = a (b u) ^^^ a (b v)
    rw [hb, ha]
  inv_mem' := by
    intro a ha u v
    change a.symm (u ^^^ v) = a.symm u ^^^ a.symm v
    apply a.injective
    rw [a.apply_symm_apply, ha, a.apply_symm_apply, a.apply_symm_apply]
private theorem small_xor (a : smallGroup) (u v : Small) :
    a.val (u ^^^ v) = a.val u ^^^ a.val v := a.property u v
private theorem small_zero (a : smallGroup) : a.val 0 = 0 := by
  have h := a.property 0 0
  simpa using h
private theorem small_eq_zero (a : smallGroup) (x : Small) : a.val x = 0 ↔ x = 0 := by
  simpa only [small_zero] using (a.val.injective.eq_iff (a := x) (b := 0))

private def rightPerm (a : smallGroup) : Equiv.Perm Code :=
  split.trans ((Equiv.prodCongr a.val a.val).trans split.symm)
private theorem right_apply (a : smallGroup) (x : Code) :
    rightPerm a x = pack (a.val (lo x)) (a.val (hi x)) := rfl
private theorem right_pack (a : smallGroup) (u v : Small) :
    rightPerm a (pack u v) = pack (a.val u) (a.val v) := by
  rw [right_apply, (unpack_pack u v).1, (unpack_pack u v).2]
private theorem right_mem (a : smallGroup) : rightPerm a ∈ rankOneGroup := by
  apply (mem_rankOneGroup _).mpr
  constructor
  · intro x y
    rw [right_apply, (unpack_xor x y).1, (unpack_xor x y).2, small_xor, small_xor,
      pack_xor, ← right_apply, ← right_apply]
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [right_apply, pure_pack, ← pack_unpack x, pure_pack]
    simp only [(unpack_pack (lo x) (hi x)).1, (unpack_pack (lo x) (hi x)).2,
      ne_eq, small_eq_zero, a.val.injective.eq_iff]
private theorem right_mul (a b : smallGroup) : rightPerm (a * b) = rightPerm a * rightPerm b := by
  apply Equiv.ext
  intro x
  change pack (a.val (b.val (lo x))) (a.val (b.val (hi x))) = rightPerm a (rightPerm b x)
  rw [right_apply b, right_pack]

private def leftApply (p : Equiv.Perm (Fin 3)) (x : Code) : Code :=
  pack ((if p 0 = 1 then 0 else lo x) ^^^ (if p 1 = 1 then 0 else hi x))
    ((if p 0 = 0 then 0 else lo x) ^^^ (if p 1 = 0 then 0 else hi x))
private theorem left_one : ∀ x : Code, leftApply 1 x = x := by decide
private theorem left_mul : ∀ (p q : Equiv.Perm (Fin 3)) (x : Code),
    leftApply (p * q) x = leftApply p (leftApply q x) := by decide
private theorem left_xor : ∀ (p : Equiv.Perm (Fin 3)) (x y : Code),
    leftApply p (x ^^^ y) = leftApply p x ^^^ leftApply p y := by
  intro p x y
  unfold leftApply
  rw [(unpack_xor x y).1, (unpack_xor x y).2]
  split_ifs
  all_goals rw [← pack_xor]
  all_goals congr 1 <;> ac_rfl
private theorem left_pure : ∀ (p : Equiv.Perm (Fin 3)) (x : Code),
    pure (leftApply p x) = pure x := by decide
private def leftPerm (p : Equiv.Perm (Fin 3)) : Equiv.Perm Code where
  toFun := leftApply p
  invFun := leftApply p⁻¹
  left_inv x := by rw [← left_mul, inv_mul_cancel, left_one]
  right_inv x := by rw [← left_mul, mul_inv_cancel, left_one]
private theorem left_mem (p : Equiv.Perm (Fin 3)) : leftPerm p ∈ rankOneGroup :=
  (mem_rankOneGroup _).mpr ⟨left_xor p, left_pure p⟩
private theorem leftPerm_mul (p q : Equiv.Perm (Fin 3)) :
    leftPerm (p * q) = leftPerm p * leftPerm q := Equiv.ext (left_mul p q)
private theorem right_left_commute (a : smallGroup) (p : Equiv.Perm (Fin 3)) :
    leftPerm p * rightPerm a = rightPerm a * leftPerm p := by
  apply Equiv.ext
  intro x
  change leftApply p (rightPerm a x) = rightPerm a (leftApply p x)
  rw [right_apply]
  simp only [leftApply, (unpack_pack _ _).1, (unpack_pack _ _).2, right_pack,
    small_xor, apply_ite a.val, small_zero]

private def tensorHom : (smallGroup × Equiv.Perm (Fin 3)) →* Equiv.Perm Code where
  toFun a := rightPerm a.1 * leftPerm a.2
  map_one' := by
    apply Equiv.ext
    intro x
    change rightPerm 1 (leftApply 1 x) = x
    rw [left_one, right_apply]
    exact pack_unpack x
  map_mul' a b := by
    change rightPerm (a.1 * b.1) * leftPerm (a.2 * b.2) =
      rightPerm a.1 * leftPerm a.2 * (rightPerm b.1 * leftPerm b.2)
    rw [right_mul, leftPerm_mul]
    calc
      (rightPerm a.1 * rightPerm b.1) * (leftPerm a.2 * leftPerm b.2) =
        rightPerm a.1 * (rightPerm b.1 * leftPerm a.2) * leftPerm b.2 := by group
      _ = _ := by rw [← right_left_commute]; group
private theorem tensor_mem (a : smallGroup × Equiv.Perm (Fin 3)) : tensorHom a ∈ rankOneGroup :=
  rankOneGroup.mul_mem (right_mem a.1) (left_mem a.2)

private def pureCode (i : Fin 3) (u : Small) : Code :=
  pack (if i = 1 then 0 else u) (if i = 0 then 0 else u)
private theorem pureCode_zero : ∀ i : Fin 3, pureCode i 0 = 0 := by decide
private theorem pureCode_unique : ∀ (i j : Fin 3) (u v : Small),
    u ≠ 0 → v ≠ 0 → pureCode i u = pureCode j v → i = j ∧ u = v := by decide
private theorem pureCode_injective : ∀ i : Fin 3, Function.Injective (pureCode i) := by
  change ∀ (i : Fin 3) (u v : Small), pureCode i u = pureCode i v → u = v
  decide
private theorem pureCode_covers : ∀ x : Code, pure x = true →
    ∃ (i : Fin 3) (u : Small), u ≠ 0 ∧ x = pureCode i u := by decide
private theorem left_pureCode : ∀ (p : Equiv.Perm (Fin 3)) (i : Fin 3) (u : Small),
    leftApply p (pureCode i u) = pureCode (p i) u := by decide
private theorem right_pureCode (a : smallGroup) (i : Fin 3) (u : Small) :
    rightPerm a (pureCode i u) = pureCode i (a.val u) := by
  simp only [pureCode, right_pack, apply_ite a.val, small_zero]
private theorem tensor_pureCode (a : smallGroup × Equiv.Perm (Fin 3)) (i : Fin 3) (u : Small) :
    tensorHom a (pureCode i u) = pureCode (a.2 i) (a.1.val u) := by
  change rightPerm a.1 (leftApply a.2 (pureCode i u)) = _
  rw [left_pureCode, right_pureCode]
private theorem tensor_injective : Function.Injective tensorHom := by
  intro a b hab
  have h (i : Fin 3) (u : Small) := congrArg (fun f : Equiv.Perm Code => f (pureCode i u)) hab
  simp only [tensor_pureCode] at h
  have hp : a.2 = b.2 := by
    apply Equiv.ext
    intro i
    exact (pureCode_unique _ _ _ _ ((small_eq_zero a.1 1).not.mpr (by decide))
      ((small_eq_zero b.1 1).not.mpr (by decide)) (h i 1)).1
  apply Prod.ext ?_ hp
  apply Subtype.ext
  apply Equiv.ext
  intro u
  have hh := h 0 u
  rw [hp] at hh
  exact pureCode_injective (b.2 0) hh

private def smallShear (k : Fin 4) (u : Small) : Small :=
  match k.val with
  | 0 => u ^^^ ((u &&& 1) <<< 1)
  | 1 => u ^^^ ((u &&& 2) >>> 1)
  | 2 => u ^^^ ((u &&& 1) <<< 2)
  | _ => u ^^^ ((u &&& 2) <<< 1)
private theorem smallShear_square : ∀ (k : Fin 4) (u : Small),
    smallShear k (smallShear k u) = u := by decide
private theorem smallShear_xor : ∀ (k : Fin 4) (u v : Small),
    smallShear k (u ^^^ v) = smallShear k u ^^^ smallShear k v := by decide
private def smallShearAut (k : Fin 4) : smallGroup :=
  ⟨⟨smallShear k, smallShear k, smallShear_square k, smallShear_square k⟩, smallShear_xor k⟩
private theorem shear_zero_tensor : tensorHom (1, Equiv.swap 1 2) = shearPerm 0 := by
  apply Equiv.ext
  intro x
  rw [shearPerm_apply]
  exact (by decide : ∀ x : Code, tensorHom (1, Equiv.swap 1 2) x = shear 0 x) x
private theorem shear_succ_tensor (k : Fin 4) : tensorHom (smallShearAut k, 1) = shearPerm k.succ := by
  apply Equiv.ext
  intro x
  rw [shearPerm_apply]
  exact (by decide : ∀ (k : Fin 4) (x : Code),
    tensorHom (smallShearAut k, 1) x = shear k.succ x) k x

private def mover (v u : Small) : Small :=
  (![![0,1,2,3,4,5,6,7],![0,4,2,6,1,5,3,7],![0,1,4,5,2,3,6,7],![0,1,5,4,3,2,6,7],![0,1,2,3,4,5,6,7],![0,1,2,3,5,4,7,6],![0,1,2,3,6,7,4,5],![0,1,2,3,7,6,5,4]]) v.toFin u.toFin
private theorem mover_square : ∀ v u : Small, mover v (mover v u) = u := by decide
private theorem mover_xor : ∀ v u w : Small,
    mover v (u ^^^ w) = mover v u ^^^ mover v w := by decide
private theorem mover_point : ∀ v : Small, v ≠ 0 → mover v 4 = v := by decide
private def moverAut (v : Small) : smallGroup :=
  ⟨⟨mover v, mover v, mover_square v, mover_square v⟩, mover_xor v⟩
private theorem tensor_orbit (x : Code) (hx : pure x = true) :
    ∃ a : smallGroup × Equiv.Perm (Fin 3), tensorHom a 4 = x := by
  obtain ⟨i, u, hu, rfl⟩ := pureCode_covers x hx
  refine ⟨(moverAut u, Equiv.swap 0 i), ?_⟩
  change tensorHom (moverAut u, Equiv.swap 0 i) (pureCode 0 4) = _
  rw [tensor_pureCode, Equiv.swap_apply_left]
  change pureCode i (mover u 4) = _
  rw [mover_point u hu]

private theorem tensor_range : tensorHom.range = rankOneGroup := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩; exact tensor_mem a
  · intro f hf
    have hp : pure (f 4) = true := ((mem_rankOneGroup f).mp hf).2 4 |>.trans (by decide)
    obtain ⟨a, ha⟩ := tensor_orbit (f 4) hp
    let b := tensorHom a
    have hd : b⁻¹ * f ∈ rankOneGroup := rankOneGroup.mul_mem
      (rankOneGroup.inv_mem (tensor_mem a)) hf
    have hd4 : (b⁻¹ * f) 4 = 4 := by
      change b.symm (f 4) = 4
      rw [← ha]; exact b.symm_apply_apply 4
    have hs : Subgroup.closure (Set.range shearPerm) ≤ tensorHom.range := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨k, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨(1, Equiv.swap 1 2), shear_zero_tensor⟩
      · exact ⟨(smallShearAut j, 1), shear_succ_tensor j⟩
    have hc := hs (rankOneGroup_point_stabilizer (b⁻¹ * f) hd hd4)
    have hm := tensorHom.range.mul_mem (show b ∈ tensorHom.range from ⟨a, rfl⟩) hc
    simpa only [mul_inv_cancel_left] using hm

private def tensorEquiv : rankOneGroup ≃* (smallGroup × Equiv.Perm (Fin 3)) :=
  (MulEquiv.ofBijective (tensorHom.codRestrict rankOneGroup tensor_mem)
    ⟨fun _ _ h => tensor_injective (congrArg Subtype.val h), by
      intro f
      have hf : f.val ∈ tensorHom.range := by rw [tensor_range]; exact f.property
      obtain ⟨a, ha⟩ := hf
      exact ⟨a, Subtype.ext ha⟩⟩).symm

private abbrev Three := Fin 3 → ZMod 2
private def decodeThree (u : Small) : Three := fun i => if u.getLsbD i.val then 1 else 0
private def encodeThree (v : Three) : Small :=
  BitVec.cons (decide (v 2 = 1)) (BitVec.cons (decide (v 1 = 1)) (BitVec.cons (decide (v 0 = 1)) 0))
private theorem decode_encode : ∀ v : Three, decodeThree (encodeThree v) = v := by decide
private theorem encode_decode : ∀ u : Small, encodeThree (decodeThree u) = u := by decide
private theorem decode_xor : ∀ u v : Small, decodeThree (u ^^^ v) = decodeThree u + decodeThree v := by decide
private theorem encode_add : ∀ u v : Three, encodeThree (u + v) = encodeThree u ^^^ encodeThree v := by decide
private theorem decode_injective : Function.Injective decodeThree :=
  Function.LeftInverse.injective encode_decode

private def smallLinear (a : smallGroup) : Three ≃ₗ[ZMod 2] Three where
  toFun v := decodeThree (a.val (encodeThree v))
  invFun v := decodeThree (a.val.symm (encodeThree v))
  left_inv v := by dsimp only; rw [encode_decode, a.val.symm_apply_apply, decode_encode]
  right_inv v := by dsimp only; rw [encode_decode, a.val.apply_symm_apply, decode_encode]
  map_add' v w := by rw [encode_add, a.property, decode_xor]
  map_smul' c v := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp only [map_zero, zero_smul]
      rw [show encodeThree 0 = 0 from by decide]
      rw [small_zero]
      decide
    · simp
private theorem smallLinear_decode (a : smallGroup) (u : Small) :
    smallLinear a (decodeThree u) = decodeThree (a.val u) := by
  change decodeThree (a.val (encodeThree (decodeThree u))) = _
  rw [encode_decode]
private def smallLinearHom : smallGroup →* (Three ≃ₗ[ZMod 2] Three) where
  toFun := smallLinear
  map_one' := by apply LinearEquiv.ext; intro v; exact decode_encode v
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    change decodeThree (a.val (b.val (encodeThree v))) =
      decodeThree (a.val (encodeThree (decodeThree (b.val (encodeThree v)))))
    rw [encode_decode]
private theorem smallLinearHom_injective : Function.Injective smallLinearHom := by
  intro a b hab
  apply Subtype.ext
  apply Equiv.ext
  intro u
  apply decode_injective
  have h := congrArg (fun f : Three ≃ₗ[ZMod 2] Three => f (decodeThree u)) hab
  exact (smallLinear_decode a u).symm.trans (h.trans (smallLinear_decode b u))

private def smallOfLinear (f : Three ≃ₗ[ZMod 2] Three) : smallGroup :=
  ⟨{ toFun := fun u => encodeThree (f (decodeThree u))
     invFun := fun u => encodeThree (f.symm (decodeThree u))
     left_inv := fun u => by dsimp only; rw [decode_encode, f.symm_apply_apply, encode_decode]
     right_inv := fun u => by dsimp only; rw [decode_encode, f.apply_symm_apply, encode_decode] },
    fun u v => by
      change encodeThree (f (decodeThree (u ^^^ v))) =
        encodeThree (f (decodeThree u)) ^^^ encodeThree (f (decodeThree v))
      rw [decode_xor, map_add, encode_add]⟩
private theorem smallLinearHom_surjective : Function.Surjective smallLinearHom := by
  intro f
  refine ⟨smallOfLinear f, ?_⟩
  apply LinearEquiv.ext
  intro v
  change decodeThree (encodeThree (f (decodeThree (encodeThree v)))) = f v
  rw [decode_encode, decode_encode]

/-- The binary two-by-three rank-one symmetry group is the product of the
full natural binary three-space group and the symmetric group on the three
nonzero vectors of the other tensor factor. -/
def rankOneGroupEquivLinearSymmetric : rankOneGroup ≃*
    (((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) × Equiv.Perm (Fin 3)) :=
  tensorEquiv.trans (MulEquiv.prodCongr
    (MulEquiv.ofBijective smallLinearHom ⟨smallLinearHom_injective, smallLinearHom_surjective⟩)
    (MulEquiv.refl _))

/-- A pure tensor with a specified nonzero two-space factor. Labels 0, 1 and
2 denote the first row, the second row and their diagonal, respectively. -/
def tensorCode (i : Fin 3) (v : Fin 3 → ZMod 2) : Code := pureCode i (encodeThree v)

/-- The product identification is the actual tensor action: its symmetric
factor permutes the three row directions and its linear factor acts on the
same binary three-space in each direction. -/
theorem rankOneGroupEquivLinearSymmetric_action (g : rankOneGroup)
    (i : Fin 3) (v : Fin 3 → ZMod 2) :
    g.val (tensorCode i v) = tensorCode ((rankOneGroupEquivLinearSymmetric g).2 i)
      ((rankOneGroupEquivLinearSymmetric g).1 v) := by
  have hg : tensorHom (tensorEquiv g) = g.val :=
    congrArg Subtype.val (tensorEquiv.symm_apply_apply g)
  change g.val (pureCode i (encodeThree v)) =
    pureCode ((tensorEquiv g).2 i) (encodeThree (smallLinear (tensorEquiv g).1 v))
  rw [← hg, tensor_pureCode]
  change pureCode _ _ = pureCode _ (encodeThree (decodeThree _))
  rw [encode_decode]

private theorem tensor_sum (x : Code) :
    tensorCode 0 (decodeThree (lo x)) ^^^ tensorCode 1 (decodeThree (hi x)) = x := by
  have h : ∀ x : Code,
      tensorCode 0 (decodeThree (lo x)) ^^^ tensorCode 1 (decodeThree (hi x)) = x := by decide
  exact h x

private theorem tensor_cubic_fixed : ∀ x : Code,
    tensorCode 1 (decodeThree (lo x)) ^^^ tensorCode 2 (decodeThree (hi x)) = x → x = 0 := by decide

/-- The order-three scalar in the two-space tensor factor has no nonzero
fixed point on the full rectangle, including its rank-two elements. -/
theorem rankOneGroup_cubic_fixed (g : rankOneGroup)
    (hg : rankOneGroupEquivLinearSymmetric g = (1, Equiv.swap 0 1 * Equiv.swap 1 2))
    (x : Code) (hx : g.val x = x) : x = 0 := by
  apply tensor_cubic_fixed x
  have he := congrArg (fun a : Code => g.val a) (tensor_sum x)
  rw [(mem_rankOneGroup g.val).mp g.property |>.1,
    rankOneGroupEquivLinearSymmetric_action, rankOneGroupEquivLinearSymmetric_action, hg] at he
  exact he.trans hx

private theorem nonpure_pair : ∀ x : Code, x ≠ 0 → pure x = false →
    decodeThree (lo x) ≠ 0 ∧ decodeThree (hi x) ≠ 0 ∧
      decodeThree (lo x) ≠ decodeThree (hi x) := by decide

/-- All 42 nonzero rank-two vectors form one orbit of the actual tensor
symmetry group. Only the natural three-space factor is needed. -/
theorem rankOneGroup_transitive_nonpure (x y : Code) (hx : x ≠ 0) (hy : y ≠ 0)
    (hpx : pure x = false) (hpy : pure y = false) :
    ∃ g : rankOneGroup, g.val x = y := by
  obtain ⟨hx₀, hx₁, hxd⟩ := nonpure_pair x hx hpx
  obtain ⟨hy₀, hy₁, hyd⟩ := nonpure_pair y hy hpy
  obtain ⟨a, ha₀, ha₁⟩ := BinaryLinear.exists_linearEquiv_pair
    (decodeThree (lo x)) (decodeThree (hi x))
    (decodeThree (lo y)) (decodeThree (hi y)) hx₀ hx₁ hy₀ hy₁ hxd hyd
  refine ⟨⟨rightPerm (smallOfLinear a), right_mem _⟩, ?_⟩
  change pack (encodeThree (a (decodeThree (lo x))))
    (encodeThree (a (decodeThree (hi x)))) = y
  rw [ha₀, ha₁, encode_decode, encode_decode, pack_unpack]

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus
