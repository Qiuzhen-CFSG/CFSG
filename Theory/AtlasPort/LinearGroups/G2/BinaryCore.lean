module

public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.DeriveFintype

/-!
# The five-root binary G₂ subgroup

The first five positive root coordinates have multiplication
`(a,b,c,d,e)(a',b',c',d',e') =
(a+a'+b'e+c'd,b+b',c+c',d+d',e+e')`.
Two explicit anisotropic planes give commuting embedded quaternion groups
with common involution and generate this group. Its embedding into the
split-octonion automorphism group is injective by the existing root-coordinate
normal form. Thus the actual subgroup has order 32 and is extraspecial of
plus type. The plane `d=e=0` gives an actual elementary eight inside it.

Identification with the two-core of a parabolic is deliberately a separate
statement: this file proves the intrinsic root calculation.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988; the root conventions
and multiplication law are those of the licensed ATLAS port in
`Theory.AtlasPort.LinearGroups.G2.Unipotent`.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Atlas.G2.BinaryCore
open Atlas.G2.Explicit
@[ext] structure Coordinates where
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
  d : ZMod 2
  e : ZMod 2
  deriving DecidableEq, Fintype
instance coordsOne : One Coordinates := ⟨⟨0,0,0,0,0⟩⟩
instance coordsMul : Mul Coordinates := ⟨fun x y =>
  ⟨x.a+y.a+y.b*x.e+y.c*x.d, x.b+y.b, x.c+y.c, x.d+y.d, x.e+y.e⟩⟩
instance coordsInv : Inv Coordinates := ⟨fun x =>
  ⟨-x.a+x.b*x.e+x.c*x.d,-x.b,-x.c,-x.d,-x.e⟩⟩
instance : Group Coordinates where
  mul_assoc x y z := by
    apply Coordinates.ext
    · change (x.a+y.a+y.b*x.e+y.c*x.d)+z.a+z.b*(x.e+y.e)+z.c*(x.d+y.d) =
        x.a+(y.a+z.a+z.b*y.e+z.c*y.d)+(y.b+z.b)*x.e+(y.c+z.c)*x.d
      ring
    · change (x.b+y.b)+z.b = x.b+(y.b+z.b)
      ring
    · change (x.c+y.c)+z.c = x.c+(y.c+z.c)
      ring
    · change (x.d+y.d)+z.d = x.d+(y.d+z.d)
      ring
    · change (x.e+y.e)+z.e = x.e+(y.e+z.e)
      ring
  one_mul x := by
    apply Coordinates.ext
    · change 0+x.a+x.b*0+x.c*0 = x.a
      ring
    · exact zero_add x.b
    · exact zero_add x.c
    · exact zero_add x.d
    · exact zero_add x.e
  mul_one x := by
    apply Coordinates.ext
    · change x.a+0+0*x.e+0*x.d = x.a
      ring
    · exact add_zero x.b
    · exact add_zero x.c
    · exact add_zero x.d
    · exact add_zero x.e
  inv_mul_cancel x := by
    apply Coordinates.ext
    · change (-x.a+x.b*x.e+x.c*x.d)+x.a+x.b*(-x.e)+x.c*(-x.d) = 0
      ring
    · exact neg_add_cancel x.b
    · exact neg_add_cancel x.c
    · exact neg_add_cancel x.d
    · exact neg_add_cancel x.e

@[simp] theorem mul_a (x y : Coordinates) : (x*y).a = x.a+y.a+y.b*x.e+y.c*x.d := rfl
@[simp] theorem mul_b (x y : Coordinates) : (x*y).b = x.b+y.b := rfl
@[simp] theorem mul_c (x y : Coordinates) : (x*y).c = x.c+y.c := rfl
@[simp] theorem mul_d (x y : Coordinates) : (x*y).d = x.d+y.d := rfl
@[simp] theorem mul_e (x y : Coordinates) : (x*y).e = x.e+y.e := rfl

def parameters (x : Coordinates) : Fin 6 → ZMod 2 := ![x.a,x.b,x.c,x.d,x.e,0]

theorem parameters_mul (x y : Coordinates) :
    parameters (x*y) = unipotentProductParameters (parameters x) (parameters y) := by
  have hneg : ∀ a : ZMod 2, -a = a := by decide +kernel
  have hthree : (3 : ZMod 2) = 1 := by decide +kernel
  funext i
  fin_cases i <;> simp [parameters, unipotentProductParameters, hthree, sub_eq_add_neg, hneg,
    add_comm, add_assoc]

def embedding : Coordinates →* Model (ZMod 2) where
  toFun x := unipotentProduct (parameters x)
  map_one' := by
    change unipotentProduct ![0,0,0,0,0,0] = 1
    exact unipotentProduct_zero
  map_mul' x y := by rw [parameters_mul, ← unipotentProduct_mul]

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have hp := unipotentProduct_injective h
  have hc := congrFun hp
  exact Coordinates.ext (hc 0) (hc 1) (hc 2) (hc 3) (hc 4)


def leftI : Coordinates := ⟨0,0,1,1,0⟩
def leftJ : Coordinates := ⟨0,1,0,1,1⟩
def rightI : Coordinates := ⟨0,0,1,1,1⟩
def rightJ : Coordinates := ⟨0,1,0,0,1⟩

def quaternionMap (i j : Coordinates) : QuaternionGroup 2 → Coordinates
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

def leftEmbedding : QuaternionGroup 2 →* Coordinates where
  toFun := quaternionMap leftI leftJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightEmbedding : QuaternionGroup 2 →* Coordinates where
  toFun := quaternionMap rightI rightJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem left_injective : Function.Injective leftEmbedding := by decide +kernel
theorem right_injective : Function.Injective rightEmbedding := by decide +kernel

instance : DecidablePred (· ∈ leftEmbedding.range) := fun _ =>
  inferInstanceAs (Decidable (∃ q, leftEmbedding q = _))
instance : DecidablePred (· ∈ rightEmbedding.range) := fun _ =>
  inferInstanceAs (Decidable (∃ q, rightEmbedding q = _))

def quaternionData : Subgroup.QuaternionCentralProductData Coordinates where
  left := leftEmbedding.range
  right := rightEmbedding.range
  left_model := ⟨(MonoidHom.ofInjective left_injective).symm⟩
  right_model := ⟨(MonoidHom.ofInjective right_injective).symm⟩
  intersection_card := by
    let : DecidablePred (· ∈ leftEmbedding.range ⊓ rightEmbedding.range) :=
      fun x => inferInstanceAs (Decidable (x ∈ leftEmbedding.range ∧ x ∈ rightEmbedding.range))
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  commute := by decide +kernel
  span := by
    apply top_unique
    intro x _
    have h : ∀ x : Coordinates, ∃ q r : QuaternionGroup 2,
        leftEmbedding q * rightEmbedding r = x := by decide +kernel
    obtain ⟨q,r,rfl⟩ := h x
    exact Subgroup.mul_mem_sup ⟨q,rfl⟩ ⟨r,rfl⟩

theorem extraspecial_coordinates : IsExtraspecial 2 Coordinates := quaternionData.extraspecial

theorem card_coordinates : Nat.card Coordinates = 32 := quaternionData.card


/-- The actual five-root subgroup; identification with the parabolic core is separate. -/
def core : Subgroup (Model (ZMod 2)) := embedding.range
noncomputable def coreEquiv : Coordinates ≃* core := MonoidHom.ofInjective embedding_injective

theorem core_le_unipotent : core ≤ unipotent := by
  rintro g ⟨x,rfl⟩
  exact unipotentProduct_mem _

theorem card_core : Nat.card core = 32 := by
  rw [← Nat.card_congr coreEquiv.toEquiv, card_coordinates]

def elementaryCoordinates : Subgroup Coordinates where
  carrier := {x | x.d = 0 ∧ x.e = 0}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro x y hx hy
    change (x*y).d = 0 ∧ (x*y).e = 0
    simp [hx.1,hx.2,hy.1,hy.2]
  inv_mem' := by
    intro x hx
    change -x.d = 0 ∧ -x.e = 0
    simp [hx.1,hx.2]
instance : DecidablePred (· ∈ elementaryCoordinates) := fun _ =>
  inferInstanceAs (Decidable (_ = (0 : ZMod 2) ∧ _ = (0 : ZMod 2)))

theorem card_elementaryCoordinates : Nat.card elementaryCoordinates = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel


instance elementaryCoordinates_elementary : IsElementaryAbelian 2 elementaryCoordinates where
  is_comm := ⟨by decide +kernel⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

def elementary : Subgroup (Model (ZMod 2)) := elementaryCoordinates.map embedding
instance elementary_elementary : IsElementaryAbelian 2 elementary := IsElementaryAbelian.map embedding

theorem card_elementary : Nat.card elementary = 8 := by
  change Nat.card (elementaryCoordinates.map embedding) = 8
  rw [← Nat.card_congr (elementaryCoordinates.equivMapOfInjective embedding embedding_injective).toEquiv]
  exact card_elementaryCoordinates

theorem elementary_le_core : elementary ≤ core := Subgroup.map_le_range _ _

noncomputable def coreQuaternionData : Subgroup.QuaternionCentralProductData core where
  left := quaternionData.left.map coreEquiv.toMonoidHom
  right := quaternionData.right.map coreEquiv.toMonoidHom
  left_model := ⟨(coreEquiv.subgroupMap _).symm.trans (MonoidHom.ofInjective left_injective).symm⟩
  right_model := ⟨(coreEquiv.subgroupMap _).symm.trans (MonoidHom.ofInjective right_injective).symm⟩
  intersection_card := by
    rw [← Subgroup.map_inf _ _ coreEquiv.toMonoidHom coreEquiv.injective]
    exact (Nat.card_congr ((quaternionData.left ⊓ quaternionData.right).equivMapOfInjective
      coreEquiv.toMonoidHom coreEquiv.injective).toEquiv).symm.trans quaternionData.intersection_card
  commute := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩
    rw [← map_mul, ← map_mul, quaternionData.commute b hb c hc]
  span := by
    rw [← Subgroup.map_sup, quaternionData.span,
      Subgroup.map_top_of_surjective coreEquiv.toMonoidHom coreEquiv.surjective]

theorem extraspecial_core : IsExtraspecial 2 core := coreQuaternionData.extraspecial

end Atlas.G2.BinaryCore
