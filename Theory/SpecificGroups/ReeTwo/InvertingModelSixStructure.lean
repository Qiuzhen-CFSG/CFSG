module
public import Theory.SpecificGroups.ReeTwo.InvertingModelSixCoordinates

/-!
# The intrinsic first core for action six

Finite commutation tests identify the center and second center. Centralizing
the second center is exactly the vanishing of the fifth coordinate.
Source: the verified Shinoda coordinates, through `InvertingModelSixCoordinates`.
-/

@[expose] public section
namespace ReeTwo.InvertingModel.Six
open scoped commutatorElement

def root (ε : Bool) (i : CoreRoot) : Model 6 ε := CyclicFourCentralExtension.embed (Core.root i)
def actor (ε : Bool) : Model 6 ε := CyclicFourCentralExtension.actor

private theorem core_mul_eq (x y : Core) : x * y = Core.mul x y := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem center_test : ∀ (ε : Bool) (g : Model 6 ε),
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
  have h7 : b7 = 0 := hca.2
  have h6 : b6 = 0 := by simpa [h7] using hca.1.symm
  subst b6 b7
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  · left; rfl
  · right; rfl

theorem center_cases (ε : Bool) (g : Model 6 ε)
    (hg : g ∈ Subgroup.center (Model 6 ε)) : g = 1 ∨ g = root ε 9 := by
  apply center_test ε g <;> simp only [cmul_eq]
  all_goals exact (Subgroup.mem_center_iff.mp hg _).symm

def commuteModLast {ε : Bool} (x y : Model 6 ε) : Prop :=
  cmul x y = cmul y x ∨ cmul x y = cmul (root ε 9) (cmul y x)
instance {ε : Bool} (x y : Model 6 ε) : Decidable (commuteModLast x y) := by
  unfold commuteModLast
  infer_instance

private def truncate (ε : Bool) (g : Model 6 ε) : Core := { g.core with b9 := 0 }

private theorem truncate_root_nine (ε : Bool) (g : Model 6 ε) :
    truncate ε (cmul (root ε 9) g) = truncate ε g := by
  rcases g with ⟨x, t⟩
  fin_cases t <;> apply Core.ext
  all_goals simp [truncate, cmul, root, CyclicFourCentralExtension.embed_apply,
    action, Core.root, Core.ofCoords, core_mul_eq, Core.mul]

private theorem truncate_commuteModLast (ε : Bool) (x y : Model 6 ε)
    (h : commuteModLast x y) : truncate ε (cmul x y) = truncate ε (cmul y x) := by
  rcases h with h | h
  · exact congrArg (truncate ε) h
  · exact (congrArg (truncate ε) h).trans (truncate_root_nine ε _)

set_option maxHeartbeats 8000000 in
theorem second_center_test (ε : Bool) (g : Model 6 ε)
    (h0 : commuteModLast g (root ε 0)) (h2 : commuteModLast g (root ε 2))
    (h4 : commuteModLast g (root ε 4)) (ha : commuteModLast g (actor ε)) :
    g = 1 ∨ g = root ε 5 ∨ g = root ε 9 ∨ g = cmul (root ε 5) (root ε 9) := by
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
  rcases hca with ⟨h6, rfl, rfl⟩
  have h6' : b6 = 0 := by simpa using h6.symm
  subst b6
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b5 with rfl | rfl <;>
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b9 with rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (by
        simp [cmul, root, CyclicFourCentralExtension.embed_apply, action,
          core_mul_eq, Core.mul, Core.root, Core.ofCoords])))

theorem commuteModLast_of_mem_second_center (ε : Bool) (g : Model 6 ε)
    (hg : g ∈ Subgroup.upperCentralSeries (Model 6 ε) 2) (y : Model 6 ε) :
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

theorem second_center_cases (ε : Bool) (g : Model 6 ε)
    (hg : g ∈ Subgroup.upperCentralSeries (Model 6 ε) 2) :
    g = 1 ∨ g = root ε 5 ∨ g = root ε 9 ∨ g = root ε 5 * root ε 9 := by
  simpa only [cmul_eq] using second_center_test ε g
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)
    (commuteModLast_of_mem_second_center ε g hg _)

set_option maxHeartbeats 8000000 in
theorem root_five_test : ∀ (ε : Bool) (g : Model 6 ε),
    (cmul g (root ε 5) = cmul (root ε 5) g ↔ g.core.b4 = 0) ∧
    commuteModLast (root ε 5) g := by
  intro ε g
  rcases g with ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) b4 with rfl | rfl
  all_goals fin_cases t
  all_goals simp [commuteModLast, cmul, action, action1, action2, action3, root,
    CyclicFourCentralExtension.embed_apply, Core.root, Core.ofCoords, core_mul_eq, Core.mul,
    add_comm]

theorem root_five_commute_iff (ε : Bool) (g : Model 6 ε) :
    g * root ε 5 = root ε 5 * g ↔ g.core.b4 = 0 := by
  simpa only [cmul_eq] using (root_five_test ε g).1

theorem root_nine_commute (ε : Bool) (g : Model 6 ε) : root ε 9 * g = g * root ε 9 :=
  (Subgroup.mem_center_iff.mp (mark_mem_center 6 ε) g).symm

theorem root_five_mem_second_center (ε : Bool) :
    root ε 5 ∈ Subgroup.upperCentralSeries (Model 6 ε) 2 := by
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro g
  rw [Subgroup.upperCentralSeries_one]
  have h := (root_five_test ε g).2
  unfold commuteModLast at h
  simp only [cmul_eq] at h
  rcases h with h | h
  · have he : ⁅root ε 5, g⁆ = 1 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact (Subgroup.center (Model 6 ε)).one_mem
  · have he : ⁅root ε 5, g⁆ = root ε 9 := by rw [commutatorElement_def, h]; simp [mul_assoc]
    rw [he]
    exact mark_mem_center 6 ε

@[simp] theorem mem_firstCore_iff (ε : Bool) (g : Model 6 ε) :
    g ∈ firstCore 6 ε ↔ g.core.b4 = 0 := by
  constructor
  · intro h
    apply (root_five_commute_iff ε g).mp
    exact (Subgroup.mem_centralizer_iff.mp h _ (root_five_mem_second_center ε)).symm
  · intro h
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    rcases second_center_cases ε x hx with rfl | rfl | rfl | rfl
    · simp
    · exact ((root_five_commute_iff ε g).mpr h).symm
    · exact root_nine_commute ε g
    · rw [mul_assoc, root_nine_commute, ← mul_assoc,
        ((root_five_commute_iff ε g).mpr h).symm, mul_assoc]

end ReeTwo.InvertingModel.Six
