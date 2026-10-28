module
public import Theory.SpecificGroups.ReeTwo.FixingModelTwoCoordinates

/-!
# The intrinsic first core for fixing action two

Finite commutation tests identify the center and second center. Centralizing
the second center is exactly the relation `b0 + b1 + b3 + b4 = 0`.
An explicit parametrization gives order 2048, and the center has order four.
Source: the verified Shinoda coordinates, through `FixingModelTwoCoordinates`.
-/

@[expose] public section
namespace ReeTwo.FixingModel.Two
open scoped commutatorElement

def root (ε : Bool) (i : CoreRoot) : Model 2 ε := CyclicFourCentralExtension.embed (Core.root i)
def actor (ε : Bool) : Model 2 ε := CyclicFourCentralExtension.actor

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

def special (ε : Bool) : Model 2 ε :=
  CyclicFourCentralExtension.embed ⟨0,0,0,0,0,1,1,1,1,0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem center_test : ∀ (ε : Bool) (g : Model 2 ε),
    cmul g (root ε 0) = cmul (root ε 0) g →
    cmul g (root ε 2) = cmul (root ε 2) g →
    cmul g (root ε 4) = cmul (root ε 4) g →
    cmul g (actor ε) = cmul (actor ε) g → g = 1 ∨ g = root ε 9 := by
  intro ε g h0 h2 h4 ha
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  have hc0 := congrArg CyclicFourCentralExtension.Model.core h0
  have hc2 := congrArg CyclicFourCentralExtension.Model.core h2
  have hc4 := congrArg CyclicFourCentralExtension.Model.core h4
  have hca := congrArg CyclicFourCentralExtension.Model.core ha
  clear h0 h2 h4 ha
  fin_cases t <;>
    simp [cmul, action, action1, action2, action3, root, actor,
      CyclicFourCentralExtension.embed_apply, CyclicFourCentralExtension.actor,
      Core.root, Core.ofCoords, core_mul_eq, Core.mul] at hc0 hc2 hc4 hca
  rcases hc2 with ⟨_, rfl, rfl, rfl, rfl, _⟩
  simp at hc0
  rcases hc0 with ⟨rfl, rfl⟩
  simp at hc4
  subst b5
  simp at hca
  have h6 : b6 = 0 := hca.1.symm
  have h7 : b7 = 0 := hca.2.1
  subst b6 b7
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  · left; rfl
  · right; rfl

theorem center_cases (ε : Bool) (g : Model 2 ε)
    (hg : g ∈ Subgroup.center (Model 2 ε)) : g = 1 ∨ g = root ε 9 := by
  apply center_test ε g <;> simp only [cmul_eq]
  all_goals exact (Subgroup.mem_center_iff.mp hg _).symm

def commuteModLast {ε : Bool} (x y : Model 2 ε) : Prop :=
  cmul x y = cmul y x ∨ cmul x y = cmul (root ε 9) (cmul y x)
instance {ε : Bool} (x y : Model 2 ε) : Decidable (commuteModLast x y) := by
  unfold commuteModLast
  infer_instance

private def truncate (ε : Bool) (g : Model 2 ε) : Core := { g.core with b9 := 0 }

private theorem truncate_root_nine (ε : Bool) (g : Model 2 ε) :
    truncate ε (cmul (root ε 9) g) = truncate ε g := by
  rcases g with ⟨x, t⟩
  fin_cases t <;> apply Core.ext
  all_goals simp [truncate, cmul, root, CyclicFourCentralExtension.embed_apply,
    action, Core.root, Core.ofCoords, core_mul_eq, Core.mul]

private theorem truncate_commuteModLast (ε : Bool) (x y : Model 2 ε)
    (h : commuteModLast x y) : truncate ε (cmul x y) = truncate ε (cmul y x) := by
  rcases h with h | h
  · exact congrArg (truncate ε) h
  · exact (congrArg (truncate ε) h).trans (truncate_root_nine ε _)

set_option maxHeartbeats 8000000 in
theorem second_center_test (ε : Bool) (g : Model 2 ε)
    (h0 : commuteModLast g (root ε 0)) (h2 : commuteModLast g (root ε 2))
    (h4 : commuteModLast g (root ε 4)) (ha : commuteModLast g (actor ε)) :
    g = 1 ∨ g = special ε ∨ g = root ε 9 ∨ g = cmul (special ε) (root ε 9) := by
  have hc0 := truncate_commuteModLast ε _ _ h0
  have hc2 := truncate_commuteModLast ε _ _ h2
  have hc4 := truncate_commuteModLast ε _ _ h4
  have hca := truncate_commuteModLast ε _ _ ha
  clear h0 h2 h4 ha
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;>
    simp [truncate, cmul, action, action1, action2, action3, root, actor,
      CyclicFourCentralExtension.embed_apply, CyclicFourCentralExtension.actor,
      Core.root, Core.ofCoords, core_mul_eq, Core.mul] at hc0 hc2 hc4 hca
  rcases hc2 with ⟨_, rfl, rfl, rfl, rfl⟩
  simp at hc0
  subst b2
  simp at hca
  have he : ∀ u v : ZMod 2, u + v = 0 → v = u := by decide
  have h6 : b6 = b5 := he _ _ hca.2.2.1
  have h7 : b7 = b5 := he _ _ hca.2.2.2
  subst b6 b7
  have h8 : b8 = b5 := by
    have hh : b5 + b5 = 0 := (by decide : ∀ z : ZMod 2, z + z = 0) b5
    simpa [hh] using hca.1.symm
  subst b8
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b5 with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (by
        simp [cmul, root, special, CyclicFourCentralExtension.embed_apply, action,
          core_mul_eq, Core.mul, Core.root, Core.ofCoords])))


theorem commuteModLast_of_mem_second_center (ε : Bool) (g : Model 2 ε)
    (hg : g ∈ Subgroup.upperCentralSeries (Model 2 ε) 2) (y : Model 2 ε) :
    commuteModLast g y := by
  have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hg y
  rw [Subgroup.upperCentralSeries_one] at h
  unfold commuteModLast
  simp only [cmul_eq]
  rcases center_cases ε _ h with h | h
  · left
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he
  · right
    have he := congrArg (fun t => t * y * g) h
    simpa [commutatorElement_def, mul_assoc] using he

theorem second_center_cases (ε : Bool) (g : Model 2 ε)
    (hg : g ∈ Subgroup.upperCentralSeries (Model 2 ε) 2) :
    g = 1 ∨ g = special ε ∨ g = root ε 9 ∨ g = special ε * root ε 9 := by
  simpa only [cmul_eq] using second_center_test ε g
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)

set_option maxHeartbeats 8000000 in
theorem special_commute_test (ε : Bool) (g : Model 2 ε) :
    cmul g (special ε) = cmul (special ε) g ↔
      g.core.b0 + g.core.b1 + g.core.b3 + g.core.b4 = 0 := by
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;>
    simp [cmul, action, action1, action2, action3, special,
      CyclicFourCentralExtension.embed_apply, core_mul_eq, Core.mul, add_comm, add_left_comm]
  all_goals revert b0 b1 b3 b4 b9; decide +kernel

set_option maxHeartbeats 8000000 in
theorem special_commuteModLast (ε : Bool) (g : Model 2 ε) :
    commuteModLast (special ε) g := by
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;>
    simp [commuteModLast, cmul, action, action1, action2, action3, special, root,
      CyclicFourCentralExtension.embed_apply, core_mul_eq, Core.mul, Core.root, Core.ofCoords,
      add_comm, add_left_comm]
  all_goals revert b0 b1 b3 b4 b9; decide +kernel

theorem special_commute_iff (ε : Bool) (g : Model 2 ε) :
    g * special ε = special ε * g ↔ g.core.b0 + g.core.b1 + g.core.b3 + g.core.b4 = 0 := by
  simpa only [cmul_eq] using special_commute_test ε g

theorem root_nine_commute (ε : Bool) (g : Model 2 ε) : root ε 9 * g = g * root ε 9 :=
  (Subgroup.mem_center_iff.mp (mark_mem_center 2 ε) g).symm

theorem special_mem_second_center (ε : Bool) :
    special ε ∈ Subgroup.upperCentralSeries (Model 2 ε) 2 := by
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro g
  rw [Subgroup.upperCentralSeries_one]
  have h := special_commuteModLast ε g
  unfold commuteModLast at h
  simp only [cmul_eq] at h
  rcases h with h | h
  · have he : ⁅special ε, g⁆ = 1 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact (Subgroup.center (Model 2 ε)).one_mem
  · have he : ⁅special ε, g⁆ = root ε 9 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact mark_mem_center 2 ε

@[simp] theorem mem_firstCore_iff (ε : Bool) (g : Model 2 ε) :
    g ∈ firstCore 2 ε ↔ g.core.b0 + g.core.b1 + g.core.b3 + g.core.b4 = 0 := by
  constructor
  · intro h
    apply (special_commute_iff ε g).mp
    exact (Subgroup.mem_centralizer_iff.mp h _ (special_mem_second_center ε)).symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    rcases second_center_cases ε x hx with rfl | rfl | rfl | rfl
    · simp
    · exact ((special_commute_iff ε g).mpr h).symm
    · exact root_nine_commute ε g
    · rw [mul_assoc, root_nine_commute, ← mul_assoc,
        ((special_commute_iff ε g).mpr h).symm, mul_assoc]

abbrev Bits := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
abbrev Params := Bits × Fin 4

def elt (ε : Bool) (p : Params) : Model 2 ε :=
  ⟨⟨p.1.1 + p.1.2.2.1 + p.1.2.2.2.1,
    p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1,
    p.1.2.2.2.2.2.1, p.1.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.1, p.1.2.2.2.2.2.2.2.2⟩,p.2⟩

theorem mem_firstCore_iff_relation (ε : Bool) (g : Model 2 ε) :
    g ∈ firstCore 2 ε ↔ g.core.b0 = g.core.b1 + g.core.b3 + g.core.b4 := by
  rw [mem_firstCore_iff]
  exact (by decide : ∀ a b c d : ZMod 2, a + b + c + d = 0 ↔ a = b + c + d) _ _ _ _

def parameterEquiv (ε : Bool) : firstCore 2 ε ≃ Params where
  toFun x := ((x.val.core.b1, x.val.core.b2, x.val.core.b3, x.val.core.b4,
    x.val.core.b5, x.val.core.b6, x.val.core.b7, x.val.core.b8, x.val.core.b9), x.val.idx)
  invFun p := ⟨elt ε p, (mem_firstCore_iff_relation _ _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply CyclicFourCentralExtension.Model.ext
    · exact Core.ext ((mem_firstCore_iff_relation _ _).mp x.property).symm rfl rfl rfl rfl rfl rfl rfl rfl rfl
    · rfl
  right_inv _ := rfl

theorem firstCore_card (ε : Bool) : Nat.card (firstCore 2 ε) = 2048 := by
  rw [Nat.card_congr (parameterEquiv ε), Nat.card_eq_fintype_card]
  decide +kernel

def inside (ε : Bool) (g : Model 2 ε)
    (h : g.core.b0 + g.core.b1 + g.core.b3 + g.core.b4 = 0) : firstCore 2 ε :=
  ⟨g, (mem_firstCore_iff _ _).mpr h⟩

def test0 (ε : Bool) : Model 2 ε := CyclicFourCentralExtension.embed ⟨1,1,0,0,0,0,0,0,0,0⟩
def test3 (ε : Bool) : Model 2 ε := CyclicFourCentralExtension.embed ⟨1,0,0,1,0,0,0,0,0,0⟩
def test4 (ε : Bool) : Model 2 ε := CyclicFourCentralExtension.embed ⟨1,0,0,0,1,0,0,0,0,0⟩

set_option maxHeartbeats 8000000 in
theorem firstCore_center_test (ε : Bool) (g : Model 2 ε)
    (h0 : cmul g (test0 ε) = cmul (test0 ε) g)
    (h2 : cmul g (root ε 2) = cmul (root ε 2) g)
    (h3 : cmul g (test3 ε) = cmul (test3 ε) g)
    (h4 : cmul g (test4 ε) = cmul (test4 ε) g) :
    g = 1 ∨ g = special ε ∨ g = root ε 9 ∨ g = cmul (special ε) (root ε 9) := by
  have hc0 := congrArg CyclicFourCentralExtension.Model.core h0
  have hc2 := congrArg CyclicFourCentralExtension.Model.core h2
  have hc3 := congrArg CyclicFourCentralExtension.Model.core h3
  have hc4 := congrArg CyclicFourCentralExtension.Model.core h4
  clear h0 h2 h3 h4
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  fin_cases t <;>
    simp [cmul, action, action1, action2, action3, root, test0, test3, test4,
      CyclicFourCentralExtension.embed_apply, Core.root, Core.ofCoords, core_mul_eq, Core.mul]
        at hc0 hc2 hc3 hc4
  rcases hc2 with ⟨_, rfl, rfl, rfl, rfl, _⟩
  simp at hc0 hc3 hc4
  rcases hc0 with ⟨rfl, hc0⟩
  have he : ∀ u v w : ZMod 2, u + v + w = u → w = v := by decide
  have h5 : b5 = b8 := he _ _ _ (by simpa using hc4.2)
  have h6 : b6 = b8 := he _ _ _ hc3.2
  have h7 : b7 = b8 := he _ _ _ hc0
  subst b5 b6 b7
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b8 with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (by
        simp [cmul, root, special, CyclicFourCentralExtension.embed_apply, action,
          core_mul_eq, Core.mul, Core.root, Core.ofCoords])))


theorem firstCore_center_cases (ε : Bool) (x : firstCore 2 ε)
    (hx : x ∈ Subgroup.center (firstCore 2 ε)) :
    x.val = 1 ∨ x.val = special ε ∨ x.val = root ε 9 ∨ x.val = special ε * root ε 9 := by
  have h (y : Model 2 ε) (hy : y.core.b0 + y.core.b1 + y.core.b3 + y.core.b4 = 0) :
      x.val * y = y * x.val :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (inside ε y hy)).symm
  have ht := firstCore_center_test ε x.val
  simp only [cmul_eq] at ht
  exact ht (h (test0 ε) (by change (1 : ZMod 2) + 1 + 0 + 0 = 0; decide)) (h (root ε 2) rfl) (h (test3 ε) (by change (1 : ZMod 2) + 0 + 1 + 0 = 0; decide)) (h (test4 ε) (by change (1 : ZMod 2) + 0 + 0 + 1 = 0; decide))

def centerElt (ε : Bool) (u v : ZMod 2) : Model 2 ε :=
  ⟨⟨0,0,0,0,0,u,u,u,u,v⟩,0⟩

def centerWord (ε : Bool) (u v : ZMod 2) : firstCore 2 ε := inside ε (centerElt ε u v) rfl

theorem centerWord_eq (ε : Bool) (u v : ZMod 2) :
    centerWord ε u v = inside ε (special ε) rfl ^ u.val * centralInvolution 2 ε ^ v.val := by
  apply Subtype.ext
  exact (by decide +kernel : ∀ (ε : Bool) (u v : ZMod 2),
    centerElt ε u v = special ε ^ u.val * root ε 9 ^ v.val) ε u v

theorem centerWord_mem_center (ε : Bool) (u v : ZMod 2) :
    centerWord ε u v ∈ Subgroup.center (firstCore 2 ε) := by
  rw [centerWord_eq]
  apply (Subgroup.center (firstCore 2 ε)).mul_mem
  · apply (Subgroup.center (firstCore 2 ε)).pow_mem
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (special_commute_iff ε x.val).mpr ((mem_firstCore_iff _ _).mp x.property)
  · exact (Subgroup.center (firstCore 2 ε)).pow_mem (centralInvolution_mem_center 2 ε) _

def centerEquiv (ε : Bool) : (ZMod 2 × ZMod 2) ≃ Subgroup.center (firstCore 2 ε) where
  toFun p := ⟨centerWord ε p.1 p.2, centerWord_mem_center ε p.1 p.2⟩
  invFun x := (x.val.val.core.b5, x.val.val.core.b9)
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change centerElt ε x.val.val.core.b5 x.val.val.core.b9 = x.val.val
    rcases firstCore_center_cases ε x.val x.property with h | h | h | h
    all_goals rw [h]
    all_goals first
      | rfl
      | simp only [← cmul_eq]
        simp [centerElt, cmul, special, root, action, CyclicFourCentralExtension.embed_apply,
          core_mul_eq, Core.mul, Core.root, Core.ofCoords]

theorem firstCore_center_card (ε : Bool) : Nat.card (Subgroup.center (firstCore 2 ε)) = 4 := by
  rw [Nat.card_congr (centerEquiv ε).symm, Nat.card_eq_fintype_card]
  decide +kernel

end ReeTwo.FixingModel.Two
