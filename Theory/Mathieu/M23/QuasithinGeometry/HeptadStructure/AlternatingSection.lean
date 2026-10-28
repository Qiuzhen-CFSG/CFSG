module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.AlternatingSection.Faithful
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.AlternatingSection.Generation

/-!
# An alternating section in the concrete M23 heptad stabilizer

Fix point 0 outside the chosen heptad. Restriction to the heptad is faithful
on its stabilizer, and two explicitly certified permutations put the full
alternating group in its image. Inverting this restriction constructs the
section. In particular the source three-cycle lifts to the displayed ambient
permutation, whose only fixed point outside the heptad is 0.

This argument uses neither a splitting theorem nor the order or structure of
the pointwise heptad kernel.

Source: Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1, specialized to
M23; Aschbacher--Smith, §5.2, printed p.655 (PDF p.672).
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.AlternatingSection
open scoped Pointwise

/-- The explicit three-cycle lift, fixing point 0 and stabilizing the heptad. -/
noncomputable def cycleElement : pointComplement :=
  ⟨⟨⟨cycleLift, cycleLift_mem⟩, by
    apply MulAction.mem_stabilizer_finset'.mpr
    change ∀ a ∈ omega, cycleLift a ∈ omega
    decide +kernel⟩, rfl⟩

/-- The explicit seven-cycle lift, fixing point 0 and stabilizing the heptad. -/
noncomputable def rotationElement : pointComplement :=
  ⟨⟨⟨rotationLift, rotationLift_mem⟩, by
    apply MulAction.mem_stabilizer_finset'.mpr
    change ∀ a ∈ omega, rotationLift a ∈ omega
    decide +kernel⟩, rfl⟩

@[simp] theorem cycleElement_action : pointAction cycleElement = labelCycle := by
  apply Equiv.ext
  intro i
  apply label.injective
  exact (heptadAction_apply cycleElement.val i).trans (cycleLift_label i)

@[simp] theorem rotationElement_action : pointAction rotationElement = labelRotation := by
  apply Equiv.ext
  intro i
  apply label.injective
  exact (heptadAction_apply rotationElement.val i).trans (rotationLift_label i)

/-- Every alternating label permutation lifts while fixing the complementary point 0. -/
theorem alternating_le_pointAction_range : alternatingGroup (Fin 7) ≤ pointAction.range :=
  alternating_le_of_cycles pointAction.range
    ⟨cycleElement, cycleElement_action⟩ ⟨rotationElement, rotationElement_action⟩

/-- The lift with the fixed-point condition retained in its codomain. -/
noncomputable def pointSection : alternatingGroup (Fin 7) →* pointComplement :=
  (MonoidHom.ofInjective pointAction_injective).symm.toMonoidHom.comp
    ((alternatingGroup (Fin 7)).subtype.codRestrict pointAction.range
      (fun a => alternating_le_pointAction_range a.property))

@[simp] theorem pointSection_action (a : alternatingGroup (Fin 7)) :
    pointAction (pointSection a) = (a : Equiv.Perm (Fin 7)) :=
  MonoidHom.apply_ofInjective_symm pointAction_injective _

/-- The alternating section of the actual labelled heptad action. -/
noncomputable def s : alternatingGroup (Fin 7) →* heptadStabilizer :=
  pointComplement.subtype.comp pointSection

/-- The section induces exactly the supplied permutation on the seven labels. -/
@[simp] theorem heptadAction_s (a : alternatingGroup (Fin 7)) :
    heptadAction (s a) = (a : Equiv.Perm (Fin 7)) := pointSection_action a

/-- Ambient point-action formula on the heptad. -/
@[simp] theorem s_label (a : alternatingGroup (Fin 7)) (i : Fin 7) :
    (s a : M23) • label i = label ((a : Equiv.Perm (Fin 7)) i) := by
  rw [← heptadAction_apply, heptadAction_s]

/-- Every member of this complement fixes the chosen ambient point. -/
@[simp] theorem s_zero (a : alternatingGroup (Fin 7)) :
    (s a : M23) • (0 : Fin 23) = 0 :=
  MulAction.mem_stabilizer_iff.mp (pointSection a).property

/-- In particular the section embeds the actual alternating group. -/
theorem s_injective : Function.Injective s := by
  intro a b h
  apply Subtype.ext
  simpa only [heptadAction_s] using congrArg heptadAction h

/-- The fixed point and labelled action uniquely determine every lift. -/
theorem s_eq_of_action (a : alternatingGroup (Fin 7)) (g : heptadStabilizer)
    (h0 : (g : M23) • (0 : Fin 23) = 0)
    (ha : heptadAction g = (a : Equiv.Perm (Fin 7))) : s a = g := by
  have h : pointSection a = (⟨g, h0⟩ : pointComplement) := by
    apply pointAction_injective
    exact (pointSection_action a).trans ha.symm
  exact congrArg Subtype.val h

/-- The source cycle on labels 1,2,3, with zero-based indices in Fin 7. -/
def c : alternatingGroup (Fin 7) :=
  ⟨labelCycle, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

@[simp] theorem c_val : (c : Equiv.Perm (Fin 7)) = Equiv.swap 0 1 * Equiv.swap 1 2 := rfl

/-- The section sends the source cycle to the certified ambient permutation. -/
theorem s_c_perm : ((s c : M23) : Equiv.Perm (Fin 23)) = cycleLift := by
  have h : pointSection c = cycleElement := by
    apply pointAction_injective
    rw [pointSection_action, cycleElement_action]
    rfl
  exact congrArg (fun g : pointComplement => g.val.val.val) h

/-- The seven-cycle generator of the alternating label action. -/
def r : alternatingGroup (Fin 7) :=
  ⟨labelRotation, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

/-- The second generator also has a fully explicit permutation on all 23 points. -/
theorem s_r_perm : ((s r : M23) : Equiv.Perm (Fin 23)) = rotationLift := by
  have h : pointSection r = rotationElement := by
    apply pointAction_injective
    rw [pointSection_action, rotationElement_action]
    rfl
  exact congrArg (fun g : pointComplement => g.val.val.val) h

/-- Explicit ambient action of the exceptional three-cycle. -/
theorem s_c_apply (q : Fin 23) : (s c : M23) • q = cycleLift q :=
  Equiv.congr_fun s_c_perm q

/-- On the sixteen complementary points, the fixed point is exactly 0. -/
theorem s_c_fixed_iff (q : Fin 23) (hq : q ∈ pairComplement omega) :
    (s c : M23) • q = q ↔ q = 0 := by
  rw [s_c_apply]
  exact cycleLift_fixed_iff q hq

/-- The unique fixed point is retained as an actual point of the M23 domain. -/
theorem s_c_unique_fixed :
    ∃! q : Fin 23, q ∈ pairComplement omega ∧ (s c : M23) • q = q := by
  refine ⟨0, ⟨by decide +kernel, s_zero c⟩, ?_⟩
  intro q hq
  exact (s_c_fixed_iff q hq.1).mp hq.2

/-- The statement also applies to any supplied alternating element with the source cycle. -/
theorem unique_fixed_of_three_cycle (a : alternatingGroup (Fin 7))
    (ha : (a : Equiv.Perm (Fin 7)) = Equiv.swap 0 1 * Equiv.swap 1 2) :
    ∃! q : Fin 23, q ∈ pairComplement omega ∧ (s a : M23) • q = q := by
  have h : a = c := Subtype.ext ha
  subst a
  exact s_c_unique_fixed

end Sporadic.Mathieu.M23Geometry.AlternatingSection
