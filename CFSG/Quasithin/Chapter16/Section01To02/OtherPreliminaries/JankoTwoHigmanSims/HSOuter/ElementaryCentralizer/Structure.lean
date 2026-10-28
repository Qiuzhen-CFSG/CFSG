module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Structure.Witnesses

/-!
# The S5 quotient and faithful kernel action of the outer HS centralizer

The transition certificates give a kernel-word-times-representative normal
form in the nine-generator candidate. Its conjugation action on five specified
kernel elements has image S5 and kernel exactly the published subgroup Q.
Consequently Q is normal and contains its centralizer. Transferring these
facts to the whole centralizer uses only the explicit coverage hypothesis.
No centralizer order or splitting is assumed.

Source: Aschbacher–Smith 16.1.5(10), printed pp.1172–1173; GLS3 Table 5.3m,
class 2C. The separate exhaustive-generation proof must discharge `hcover`.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer
open Subgroup StructureWitnesses

private theorem signed_even (i : Fin 9) :
    signedGenerator ⟨2 * i.val, by omega⟩ = candidateGenerator i := by
  fin_cases i <;> rfl

private theorem signed_odd (i : Fin 9) :
    signedGenerator ⟨2 * i.val + 1, by omega⟩ = (candidateGenerator i)⁻¹ := by
  fin_cases i <;> rfl

/-- Every element of the generated candidate has one of the 120 certified coset
representatives, with a word in the exact published kernel on the left. -/
theorem candidate_normalForm (g : C) (hg : g ∈ candidate) :
    ∃ (x : E16) (j : Fin 120), g = kernelHom x * representative j := by
  have step (s : Fin 18) (g : C)
      (h : ∃ (x : E16) (j : Fin 120), g = kernelHom x * representative j) :
      ∃ (x : E16) (j : Fin 120),
        signedGenerator s * g = kernelHom x * representative j := by
    obtain ⟨x, j, rfl⟩ := h
    obtain ⟨y, hy⟩ := signed_conjugates s x
    refine ⟨y * coordinates (transitionCode s j), nextRepresentative s j, ?_⟩
    rw [map_mul, ← mul_assoc, hy, mul_assoc, signed_transition, ← mul_assoc]
  apply Subgroup.closure_induction_left (p := fun g _ =>
    ∃ (x : E16) (j : Fin 120), g = kernelHom x * representative j) ?_ ?_ ?_ hg
  · exact ⟨1, 0, by rw [map_one, representative_zero, one_mul]⟩
  · rintro _ ⟨i, rfl⟩ g _ ih
    simpa only [signed_even] using step ⟨2 * i.val, by omega⟩ g ih
  · rintro _ ⟨i, rfl⟩ g _ ih
    simpa only [signed_odd] using step ⟨2 * i.val + 1, by omega⟩ g ih

/-- The conjugation specification for the actual five-point action. -/
@[expose] def ActsOnMarked (g : C) (p : S5) : Prop :=
  ∀ i : Fin 5, g * marked i = marked (p i) * g

private theorem acts_unique {g : C} {p q : S5}
    (hp : ActsOnMarked g p) (hq : ActsOnMarked g q) : p = q := by
  apply Equiv.ext
  intro i
  exact marked_injective (mul_right_cancel ((hp i).symm.trans (hq i)))

private theorem kernel_acts (x : E16) : ActsOnMarked (kernelHom x) 1 := by
  intro i
  simp only [Equiv.Perm.one_apply]
  change kernelHom x * kernelHom _ = kernelHom _ * kernelHom x
  rw [← map_mul, ← map_mul, mul_comm]

private theorem acts_mul {g h : C} {p q : S5}
    (hg : ActsOnMarked g p) (hh : ActsOnMarked h q) :
    ActsOnMarked (g * h) (p * q) := by
  intro i
  change (g * h) * marked i = marked (p (q i)) * (g * h)
  rw [mul_assoc, hh i, ← mul_assoc, hg (q i), mul_assoc]

private theorem normalForm_acts (x : E16) (j : Fin 120) :
    ActsOnMarked (kernelHom x * representative j) (representativeAction j) := by
  simpa only [one_mul] using acts_mul (kernel_acts x) (representative_conjugates j)

private theorem exists_action (hcover : candidate = ⊤) (g : C) :
    ∃ p : S5, ActsOnMarked g p := by
  obtain ⟨x, j, rfl⟩ := candidate_normalForm g (hcover.symm ▸ mem_top g)
  exact ⟨_, normalForm_acts x j⟩

/-- Conjugation on the five marked elements of Q, assuming only exhaustive
coverage by the concrete candidate. -/
noncomputable def kernelAction (hcover : candidate = ⊤) : C →* S5 where
  toFun g := Classical.choose (exists_action hcover g)
  map_one' := acts_unique (Classical.choose_spec (exists_action hcover 1))
    (by intro i; simp)
  map_mul' g h := acts_unique (Classical.choose_spec (exists_action hcover (g * h)))
    (acts_mul (Classical.choose_spec (exists_action hcover g))
      (Classical.choose_spec (exists_action hcover h)))

theorem kernelAction_spec (hcover : candidate = ⊤) (g : C) :
    ActsOnMarked g (kernelAction hcover g) :=
  Classical.choose_spec (exists_action hcover g)

theorem kernelAction_representative (hcover : candidate = ⊤) (j : Fin 120) :
    kernelAction hcover (representative j) = representativeAction j :=
  acts_unique (kernelAction_spec hcover _) (representative_conjugates j)

theorem kernelAction_surjective (hcover : candidate = ⊤) :
    Function.Surjective (kernelAction hcover) := by
  intro p
  obtain ⟨j, rfl⟩ := representativeAction_surjective p
  exact ⟨representative j, kernelAction_representative hcover j⟩

/-- The action kernel is precisely Q, not merely an abstract group of order 16. -/
theorem kernelAction_ker (hcover : candidate = ⊤) : (kernelAction hcover).ker = Q := by
  ext g
  change kernelAction hcover g = 1 ↔ g ∈ Q
  constructor
  · intro hg
    obtain ⟨x, j, rfl⟩ := candidate_normalForm g (hcover.symm ▸ mem_top g)
    have hj : representativeAction j = 1 :=
      (acts_unique (kernelAction_spec hcover _) (normalForm_acts x j)).symm.trans hg
    have hj0 : j = 0 := representativeAction_injective (hj.trans representativeAction_zero.symm)
    rw [hj0, representative_zero, mul_one]
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact acts_unique (kernelAction_spec hcover _) (kernel_acts x)

/-- Normality is relative to the actual centralizer C. -/
theorem kernel_normal (hcover : candidate = ⊤) : Q.Normal := by
  rw [← kernelAction_ker hcover]
  infer_instance

/-- The actual quotient of the actual centralizer by Q is S5. -/
noncomputable def quotientEquiv (hcover : candidate = ⊤) :
    letI := kernel_normal hcover
    C ⧸ Q ≃* S5 := by
  letI := kernel_normal hcover
  exact (QuotientGroup.quotientMulEquivOfEq (kernelAction_ker hcover).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (kernelAction_surjective hcover))

/-- Faithfulness modulo Q: every element centralizing the whole kernel lies in Q. -/
theorem kernel_selfCentralizing (hcover : candidate = ⊤) :
    Subgroup.centralizer (Q : Set C) ≤ Q := by
  intro g hg
  rw [← kernelAction_ker hcover]
  change kernelAction hcover g = 1
  apply acts_unique (kernelAction_spec hcover g)
  intro i
  exact (Subgroup.mem_centralizer_iff.mp hg (marked i) (marked_mem i)).symm

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer
