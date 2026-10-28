module
public import Theory.SpecificGroups.ReeTwo.InvertingModelSixStructure
public import Theory.GroupTheory.SquareRootCentralizerCharacteristic
import all Theory.GroupTheory.SquareRootCentralizerCharacteristic

/-!
# Square-root centralizer certificates for action six

Central coordinates reduce the square-root test to 512 representatives. All
roots of the mark have centralizer size 128; roots of the other central
involutions exhibit centralizer size 256.
The private import of the characteristic criterion is intentional: the count
transport unfolds its internal cardinality subtype, while the public API uses
only `Group.commutingCard` and the existing criterion.

Source: direct certificates in the verified Shinoda coordinates.
-/

@[expose] public section
namespace ReeTwo.InvertingModel.Six

abbrev Bits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
abbrev Params := Bits × Fin 4

def elt (ε : Bool) (p : Params) : Model 6 ε :=
  ⟨⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, 0, p.1.2.2.2.2.1,
    p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.2⟩, p.2⟩

def parameterEquiv (ε : Bool) : firstCore 6 ε ≃ Params where
  toFun x := ((x.val.core.b0, x.val.core.b1, x.val.core.b2, x.val.core.b3,
    x.val.core.b5, x.val.core.b6, x.val.core.b7, x.val.core.b8, x.val.core.b9), x.val.idx)
  invFun p := ⟨elt ε p, (mem_firstCore_iff _ _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply CyclicFourCentralExtension.Model.ext
    · exact Core.ext rfl rfl rfl rfl ((mem_firstCore_iff _ _).mp x.property).symm rfl rfl rfl rfl rfl
    · rfl
  right_inv p := rfl

theorem firstCore_card (ε : Bool) : Nat.card (firstCore 6 ε) = 2048 := by
  rw [Nat.card_congr (parameterEquiv ε), Nat.card_eq_fintype_card]
  decide +kernel

abbrev ReducedBits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
abbrev ReducedParams := ReducedBits × Fin 4

def reducedElt (ε : Bool) (p : ReducedParams) : Model 6 ε :=
  ⟨⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, 0, 0,
    p.1.2.2.2.2.1, p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2, 0⟩, p.2⟩


def countNat (ε : Bool) (n : Nat) : ℕ :=
  match n with
  | 0 => Fintype.card {p : ReducedParams // pmul ε (code (reducedElt ε p)) 0 = pmul ε 0 (code (reducedElt ε p))}
  | n + 1 => Fintype.card {p : ReducedParams //
      pmul ε (code (reducedElt ε p)) (n + 1) = pmul ε (n + 1) (code (reducedElt ε p))}

theorem countNat_eq (ε : Bool) (n : Nat) : countNat ε n =
    Fintype.card {p : ReducedParams // pmul ε (code (reducedElt ε p)) n = pmul ε n (code (reducedElt ε p))} := by
  cases n <;> rfl

def count {ε : Bool} (x : Model 6 ε) : ℕ := 4 * countNat ε (code x)


def inside (ε : Bool) (g : Model 6 ε) (h : g.core.b4 = 0) : firstCore 6 ε :=
  ⟨g, (mem_firstCore_iff _ _).mpr h⟩

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

set_option maxHeartbeats 8000000 in
theorem firstCore_center_test : ∀ (ε : Bool) (p : Params),
    cmul (elt ε p) (root ε 0) = cmul (root ε 0) (elt ε p) →
    cmul (elt ε p) (root ε 1) = cmul (root ε 1) (elt ε p) →
    cmul (elt ε p) (root ε 2) = cmul (root ε 2) (elt ε p) →
    cmul (elt ε p) (root ε 3) = cmul (root ε 3) (elt ε p) →
    elt ε p = 1 ∨ elt ε p = root ε 5 ∨ elt ε p = root ε 9 ∨
      elt ε p = cmul (root ε 5) (root ε 9) := by
  intro ε p h0 h1 h2 h3
  have hc0 := congrArg CyclicFourCentralExtension.Model.core h0
  have hc1 := congrArg CyclicFourCentralExtension.Model.core h1
  have hc2 := congrArg CyclicFourCentralExtension.Model.core h2
  have hc3 := congrArg CyclicFourCentralExtension.Model.core h3
  clear h0 h1 h2 h3
  rcases p with ⟨⟨b0,b1,b2,b3,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;>
    simp [elt, cmul, action, action1, action2, action3, root,
      CyclicFourCentralExtension.embed_apply,
      Core.root, Core.ofCoords, core_mul_eq, Core.mul] at hc0 hc1 hc2 hc3
  rcases hc2 with ⟨_, rfl, rfl, rfl, _⟩
  simp at hc0
  rcases hc0 with ⟨rfl, rfl⟩
  simp at hc1 hc3
  subst b6 b7
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b5 with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (by
        simp [elt, cmul, root, CyclicFourCentralExtension.embed_apply, action,
          core_mul_eq, Core.mul, Core.root, Core.ofCoords])))

theorem firstCore_center_cases (ε : Bool) (x : firstCore 6 ε)
    (hx : x ∈ Subgroup.center (firstCore 6 ε)) :
    x.val = 1 ∨ x.val = root ε 5 ∨ x.val = root ε 9 ∨ x.val = root ε 5 * root ε 9 := by
  have h (y : Model 6 ε) (hy : y.core.b4 = 0) : x.val * y = y * x.val :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (inside ε y hy)).symm
  have he : elt ε (parameterEquiv ε x) = x.val :=
    congrArg Subtype.val ((parameterEquiv ε).symm_apply_apply x)
  have ht := firstCore_center_test ε (parameterEquiv ε x)
  simp only [cmul_eq, he] at ht
  exact ht (h (root ε 0) rfl) (h (root ε 1) rfl) (h (root ε 2) rfl) (h (root ε 3) rfl)


def reduceParam (p : Params) : ReducedParams :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1,
    p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1), p.2)

def centerElt (ε : Bool) (u v : ZMod 2) : Model 6 ε :=
  ⟨⟨0, 0, 0, 0, 0, u, 0, 0, 0, v⟩, 0⟩

def centerWord (ε : Bool) (u v : ZMod 2) : firstCore 6 ε := inside ε (centerElt ε u v) rfl

theorem centerWord_eq (ε : Bool) (u v : ZMod 2) :
    centerWord ε u v = inside ε (root ε 5) rfl ^ u.val * centralInvolution 6 ε ^ v.val := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ (ε : Bool) (u v : ZMod 2),
    centerElt ε u v = root ε 5 ^ u.val * root ε 9 ^ v.val) ε u v

theorem centerWord_mem_center (ε : Bool) (u v : ZMod 2) :
    centerWord ε u v ∈ Subgroup.center (firstCore 6 ε) := by
  rw [centerWord_eq]
  apply (Subgroup.center (firstCore 6 ε)).mul_mem
  · apply (Subgroup.center (firstCore 6 ε)).pow_mem
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (root_five_commute_iff ε x.val).mpr ((mem_firstCore_iff _ _).mp x.property)
  · exact (Subgroup.center (firstCore 6 ε)).pow_mem (centralInvolution_mem_center 6 ε) _

theorem centerWord_square (ε : Bool) (u v : ZMod 2) : centerWord ε u v ^ 2 = 1 := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ (ε : Bool) (u v : ZMod 2), centerElt ε u v ^ 2 = 1) ε u v



theorem decomposition (ε : Bool) (p : Params) :
    elt ε p = cmul (reducedElt ε (reduceParam p))
      (centerElt ε p.1.2.2.2.2.1 p.1.2.2.2.2.2.2.2.2) := by
  rcases p with ⟨⟨b0,b1,b2,b3,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;> apply CyclicFourCentralExtension.Model.ext
  all_goals simp [elt, reducedElt, reduceParam, centerElt, cmul,
    action, action1, action2, action3, core_mul_eq, Core.mul]

def regroup : Params ≃ ReducedParams × (ZMod 2 × ZMod 2) where
  toFun p := (reduceParam p, p.1.2.2.2.2.1, p.1.2.2.2.2.2.2.2.2)
  invFun p := ((p.1.1.1, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2.1, p.2.1,
    p.1.1.2.2.2.2.1, p.1.1.2.2.2.2.2.1, p.1.1.2.2.2.2.2.2, p.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1000000 in
theorem commutingCard_eq (ε : Bool) (x : firstCore 6 ε) : Group.commutingCard x = count x.val := by
  let f := (parameterEquiv ε).trans regroup
  let P (r : ReducedParams) := pmul ε (code (reducedElt ε r)) (code x.val) =
    pmul ε (code x.val) (code (reducedElt ε r))
  have hi (y : firstCore 6 ε) : y * x = x * y ↔ P (f y).1 := by
    let p := parameterEquiv ε y
    let r := inside ε (reducedElt ε (reduceParam p)) rfl
    let c := centerWord ε p.1.2.2.2.2.1 p.1.2.2.2.2.2.2.2.2
    have he : elt ε p = y.val := congrArg Subtype.val ((parameterEquiv ε).symm_apply_apply y)
    have hd : y = r * c := by
      apply Subtype.ext
      change y.val = reducedElt ε (reduceParam p) * centerElt ε _ _
      simpa only [cmul_eq, he] using decomposition ε p
    have hc : c ∈ Subgroup.center (firstCore 6 ε) := centerWord_mem_center _ _ _
    have hh : y * x = x * y ↔ r * x = x * r := by
      rw [hd, mul_assoc r c x, ← Subgroup.mem_center_iff.mp hc x,
        ← mul_assoc r x c, ← mul_assoc x r c, mul_right_cancel_iff]
    rw [hh]
    change r * x = x * r ↔ pmul ε (code r.val) (code x.val) = pmul ε (code x.val) (code r.val)
    rw [pmul_code, pmul_code, code_injective.eq_iff]
    exact Subtype.ext_iff
  let e : {p : ReducedParams × (ZMod 2 × ZMod 2) // P p.1} ≃
      {r : ReducedParams // P r} × (ZMod 2 × ZMod 2) :=
    { toFun p := (⟨p.val.1, p.property⟩, p.val.2)
      invFun p := ⟨(p.1.val, p.2), p.1.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  unfold Group.commutingCard
  let e1 : {y : firstCore 6 ε // y * x = x * y} ≃
      {p : ReducedParams × (ZMod 2 × ZMod 2) // P p.1} :=
    { toFun y := ⟨f y.val, (hi y.val).mp y.property⟩
      invFun p := ⟨f.symm p.val, (hi (f.symm p.val)).mpr (by
        simpa only [f.apply_symm_apply] using p.property)⟩
      left_inv y := Subtype.ext (f.symm_apply_apply y.val)
      right_inv p := Subtype.ext (f.apply_symm_apply p.val) }
  calc
    _ = Nat.card ({r : ReducedParams // P r} × (ZMod 2 × ZMod 2)) :=
      Nat.card_congr (e1.trans e)
    _ = count x.val := by
      rw [Nat.card_prod]
      have hcard : Nat.card (ZMod 2 × ZMod 2) = 4 := by
        rw [Nat.card_eq_fintype_card]
        decide +kernel
      rw [hcard, Nat.card_eq_fintype_card]
      change _ = 4 * countNat ε (code x.val)
      rw [countNat_eq, Nat.mul_comm]

theorem commutingCard_mul_center {ε : Bool} (x c : firstCore 6 ε)
    (hc : c ∈ Subgroup.center (firstCore 6 ε)) : Group.commutingCard (x * c) = Group.commutingCard x := by
  apply Nat.card_congr
  refine (Equiv.refl (firstCore 6 ε)).subtypeEquiv ?_
  intro y
  change y * (x * c) = (x * c) * y ↔ y * x = x * y
  rw [← mul_assoc y x c, mul_assoc x c y,
    ← Subgroup.mem_center_iff.mp hc y, ← mul_assoc x y c, mul_right_cancel_iff]

end ReeTwo.InvertingModel.Six
