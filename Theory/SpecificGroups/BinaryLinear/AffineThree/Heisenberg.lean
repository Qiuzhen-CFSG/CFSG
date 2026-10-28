module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.QuaternionCentralProductFactorNormality
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The five-coordinate binary Heisenberg group

The cross term pairs a binary row with a binary column. Its two commuting
quaternion subgroups give the plus extraspecial group of order 32. The cubic
actor fixes precisely the center and the coordinate swap exchanges the factors.
These coordinates are used for the actual affine three-space translation
centralizer in Aschbacher–Smith 12.2.27(2), printed p.807.
-/

@[expose] public section
namespace BinaryLinear.Affine.ThreeCore
abbrev F := ZMod 2
@[ext] structure Q where
  z : F
  a : F
  b : F
  c : F
  d : F
  deriving DecidableEq

def coordinates : Q ≃ F × F × F × F × F where
  toFun x := (x.z,x.a,x.b,x.c,x.d)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : Fintype Q := Fintype.ofEquiv _ coordinates.symm
instance : Mul Q := ⟨fun x y =>
  ⟨x.z+y.z+x.a*y.c+x.b*y.d,x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩⟩
instance : One Q := ⟨⟨0,0,0,0,0⟩⟩
instance : Inv Q := ⟨fun x => ⟨-x.z+x.a*x.c+x.b*x.d,-x.a,-x.b,-x.c,-x.d⟩⟩
instance : Group Q where
  mul_assoc x y w := by
    apply Q.ext
    · change (x.z+y.z+x.a*y.c+x.b*y.d)+w.z+(x.a+y.a)*w.c+(x.b+y.b)*w.d =
        x.z+(y.z+w.z+y.a*w.c+y.b*w.d)+x.a*(y.c+w.c)+x.b*(y.d+w.d)
      ring
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
  one_mul x := by
    apply Q.ext
    · change 0+x.z+0*x.c+0*x.d=x.z
      ring
    · exact zero_add _
    · exact zero_add _
    · exact zero_add _
    · exact zero_add _
  mul_one x := by
    apply Q.ext
    · change x.z+0+x.a*0+x.b*0=x.z
      ring
    · exact add_zero _
    · exact add_zero _
    · exact add_zero _
    · exact add_zero _
  inv_mul_cancel x := by
    apply Q.ext
    · change (-x.z+x.a*x.c+x.b*x.d)+x.z+(-x.a)*x.c+(-x.b)*x.d=0
      ring
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · exact neg_add_cancel _

 theorem card_Q : Nat.card Q = 32 := by
  rw [Nat.card_congr coordinates]
  simp

 theorem center_iff (x : Q) : x ∈ Subgroup.center Q ↔
    x.a = 0 ∧ x.b = 0 ∧ x.c = 0 ∧ x.d = 0 := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide +kernel

def centerCoordinates : Subgroup.center Q ≃ F where
  toFun x := x.val.z
  invFun z := ⟨⟨z,0,0,0,0⟩, (center_iff _).mpr ⟨rfl,rfl,rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨ha,hb,hc,hd⟩ := (center_iff x.val).mp x.property
    apply Q.ext
    · rfl
    · exact ha.symm
    · exact hb.symm
    · exact hc.symm
    · exact hd.symm
  right_inv _ := rfl

 theorem center_card : Nat.card (Subgroup.center Q) = 2 :=
  (Nat.card_congr centerCoordinates).trans (Nat.card_zmod 2)

 theorem square_central (x : Q) : x^2 ∈ Subgroup.center Q := by
  rw [center_iff]
  revert x
  decide +kernel

 theorem quotient_elementary : IsElementaryAbelian 2 (Q ⧸ Subgroup.center Q) := by
  have hs (q : Q ⧸ Subgroup.center Q) : q^2=1 := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact square_central x
  have hi (q : Q ⧸ Subgroup.center Q) : q⁻¹=q :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs q)
  refine {
    is_comm := ⟨?_⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro a b
  simpa only [hi] using mul_inv_rev a b

 theorem extraspecial : IsExtraspecial 2 Q where
  center_order_p := center_card
  quotient_elementary_abelian := quotient_elementary
  quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
    intro ht
    have hh := center_card
    rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, card_Q] at hh
    contradiction)

def qi (side : Bool) : Q := if side then ⟨0,1,0,1,1⟩ else ⟨0,1,0,1,0⟩
def qj (side : Bool) : Q := if side then ⟨0,0,1,0,1⟩ else ⟨0,0,1,1,1⟩

def quaternionEmbedding (side : Bool) : QuaternionGroup 2 →* Q where
  toFun q := match q with
    | .a n => (qi side)^n.val
    | .xa n => qj side * (qi side)^n.val
  map_one' := by cases side <;> decide +kernel
  map_mul' := by cases side <;> decide +kernel

theorem quaternionEmbedding_injective (side : Bool) :
    Function.Injective (quaternionEmbedding side) := by
  cases side <;> decide +kernel

theorem quaternion_factors_commute : ∀ a b : QuaternionGroup 2,
    quaternionEmbedding false a * quaternionEmbedding true b =
      quaternionEmbedding true b * quaternionEmbedding false a := by decide +kernel

theorem quaternion_product_surjective : Function.Surjective
    (fun p : QuaternionGroup 2 × QuaternionGroup 2 =>
      quaternionEmbedding false p.1 * quaternionEmbedding true p.2) := by decide +kernel

def swap : MulAut Q where
  toFun x := ⟨x.z,x.b,x.a,x.d,x.c⟩
  invFun x := ⟨x.z,x.b,x.a,x.d,x.c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := by decide +kernel

def cubic : MulAut Q where
  toFun x := ⟨x.z,x.b,x.a+x.b,x.c+x.d,x.c⟩
  invFun x := ⟨x.z,x.a+x.b,x.a,x.d,x.c+x.d⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

theorem cubic_fixed_iff (x : Q) : cubic x = x ↔ x ∈ Subgroup.center Q := by
  rw [center_iff]
  revert x
  decide +kernel

theorem swap_le_other_factor : ∀ (side : Bool) (q : QuaternionGroup 2),
    ∃ r : QuaternionGroup 2, swap (quaternionEmbedding side q) =
      quaternionEmbedding (!side) r := by decide +kernel

theorem swap_moves_left : swap (qi false) ∉ (quaternionEmbedding false).range := by
  change ¬ ∃ q, quaternionEmbedding false q = swap (qi false)
  decide +kernel

theorem cubic_cube : cubic^3 = 1 := by
  apply MulEquiv.ext
  intro x
  change cubic (cubic (cubic x)) = x
  revert x
  decide +kernel

theorem cubic_order : orderOf cubic = 3 := by
  apply orderOf_eq_prime cubic_cube
  intro h
  have hh := DFunLike.congr_fun h (qi false)
  have hn : cubic (qi false) ≠ qi false := by decide +kernel
  exact hn hh

theorem swap_inverts_cubic : swap * cubic * swap = cubic⁻¹ := by
  apply MulEquiv.ext
  intro x
  change swap (cubic (swap x)) = cubic.symm x
  revert x
  decide +kernel

end BinaryLinear.Affine.ThreeCore
