module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.HalfActions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions

/-!
# Source generator comparisons for the actual half-spin actions

The concrete even triality group acts on both orbit relations of axis 2.
Commutation with `k3` and `z3` constructs the `B3(A2)` action; its orbit
kernel is exactly the subgroup in Aschbacher 27.3(6). Covariance identifies
the loop and even automorphism generators with the signed maps of 27.3.
The odd second automorphism transports `B1(A2)` to `B3(A2)`, with its
point map equal to the actual triple permutation and its form preserved.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3, printed p. 146.
-/

@[expose] public section
noncomputable section
open Atlas.Fischer
namespace Sporadic.Monster.Construction.TrialitySpin.HalfActions
open SpinActions

/-- The three source loop generators in the even triality subgroup. -/
def psiOne (d : ParkerLoop) : NPlus :=
  ⟨psi1N d, Subgroup.subset_closure (Or.inl ⟨d, Or.inl rfl⟩)⟩
def psiTwo (d : ParkerLoop) : NPlus :=
  ⟨psi2N d, Subgroup.subset_closure (Or.inl ⟨d, Or.inr (Or.inl rfl)⟩)⟩
def psiThree (d : ParkerLoop) : NPlus :=
  ⟨psi3N d, Subgroup.subset_closure (Or.inl ⟨d, Or.inr (Or.inr rfl)⟩)⟩

/-- An even standard automorphism as its actual second triality permutation. -/
def standardEven (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega) : NPlus :=
  ⟨psiAut2N α, Subgroup.subset_closure (Or.inr ⟨α.val, α.prop, hα,
    by simp [psiAut2N, psiAut2, hα]⟩)⟩

theorem commutes_k3 (g : NPlus) (a : Triple) :
    permutations g (k3.val a) = k3.val (permutations g a) :=
  congrArg (fun p : N => p.val a) (NPlus_commute_k3 g.val g.prop).eq

theorem commutes_z3 (g : NPlus) (a : Triple) :
    permutations g (z3 a) = z3 (permutations g a) := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := normalForm_bijective.surjective (inclusion g)
  have hval : (normalForm d e α).val = g.val := congrArg Subtype.val hw
  have hα := (normalForm_mem_NPlus_iff d e α).mp (hval.symm ▸ g.prop)
  change g.val.val (z3 a) = z3 (g.val.val a)
  rw [← hval]
  rcases a with ⟨a,b,c⟩
  change psiAut1 α.val (psi2 e (psi1 d (z3 (a,b,c)))) =
    z3 (psiAut1 α.val (psi2 e (psi1 d (a,b,c))))
  simp [psiAut1, hα, diagonal]

/-- The second-axis module with the `k3` orbit relation. -/
def thirdSecondRepresentation : Representation ℝ NPlus B3A2 :=
  B3Axis2.inducedRepresentation permutations preserves_axis2 commutes_k3 commutes_z3

/-- Source 27.3(6), on the actual acting subgroup. -/
theorem thirdSecondRepresentation_kernel :
    thirdSecondRepresentation.ker = axis2K3Kernel.subgroupOf NPlus := by
  ext g
  change thirdSecondRepresentation g = 1 ↔ g.val ∈ axis2K3Kernel
  rw [← NPlus_axis2_k3_kernel g.val g.prop]
  rw [show thirdSecondRepresentation g = 1 ↔
      ∀ a ∈ A2, permutations g a = a ∨ permutations g a = k3.val a from
    B3Axis2.inducedRepresentation_kernel_iff permutations preserves_axis2
      commutes_k3 commutes_z3 g]
  constructor
  · intro h b
    exact h (axis2 b) ⟨b,rfl⟩
  · rintro h a ⟨b,rfl⟩
    exact h b

theorem thirdSecondRepresentation_isometry (g : NPlus) (v w : B3A2) :
    B3Axis2.form (thirdSecondRepresentation g v) (thirdSecondRepresentation g w) =
      B3Axis2.form v w :=
  B3Axis2.inducedRepresentation_isometry permutations preserves_axis2 commutes_k3 commutes_z3 g v w

theorem thirdSecondRepresentation_monomial (g : NPlus)
    (a : B3Axis2.geometry.signedOrbits.toPairing.Orbit) :
    ∃ b, thirdSecondRepresentation g (B3Axis2.basis a) = B3Axis2.basis b ∨
      thirdSecondRepresentation g (B3Axis2.basis a) = -B3Axis2.basis b :=
  B3Axis2.inducedRepresentation_monomial permutations preserves_axis2 commutes_k3 commutes_z3 g a

theorem secondRepresentation_psiOne (d : ParkerLoop) :
    secondRepresentation (psiOne d) = (psi1B1 d).toLinearMap :=
  induced_psi1B1 permutations preserves_axis2 commutes_k1 commutes_z1 (psiOne d) d rfl

theorem secondRepresentation_psiTwo (d : ParkerLoop) :
    secondRepresentation (psiTwo d) = (psi2B1 d).toLinearMap :=
  induced_psi2B1 permutations preserves_axis2 commutes_k1 commutes_z1 (psiTwo d) d rfl

theorem secondRepresentation_psiThree (d : ParkerLoop) :
    secondRepresentation (psiThree d) = (psi3B1 d).toLinearMap :=
  induced_psi3B1 permutations preserves_axis2 commutes_k1 commutes_z1 (psiThree d) d rfl

theorem secondRepresentation_standardEven (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) :
    secondRepresentation (standardEven α hα) = (psiAut2Even α.val α.prop hα).toLinearMap :=
  induced_psiAut2Even permutations preserves_axis2 commutes_k1 commutes_z1
    (standardEven α hα) α.val α.prop hα rfl

theorem thirdSecondRepresentation_psiOne (d : ParkerLoop) :
    thirdSecondRepresentation (psiOne d) = (psi1B3 d).toLinearMap :=
  induced_psi1B3 permutations preserves_axis2 commutes_k3 commutes_z3 (psiOne d) d rfl

theorem thirdSecondRepresentation_psiTwo (d : ParkerLoop) :
    thirdSecondRepresentation (psiTwo d) = (psi2B3 d).toLinearMap :=
  induced_psi2B3 permutations preserves_axis2 commutes_k3 commutes_z3 (psiTwo d) d rfl

/-- The `B1(A2)` basis relation and source 27.3(1). -/
theorem secondRepresentation_psiOne_delta (d b : ParkerLoop) :
    secondRepresentation (psiOne d) (delta2 b) = delta2 (parkerLoopMultiply d b) := by
  rw [secondRepresentation_psiOne]
  exact psi1B1_delta d b

/-- Source 27.3(2), including both the square and overlap signs. -/
theorem secondRepresentation_psiTwo_delta (d b : ParkerLoop) :
    secondRepresentation (psiTwo d) (delta2 b) =
      delta2 (parkerSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) b) := by
  rw [secondRepresentation_psiTwo]
  exact psi2B1_delta d b

/-- Source 27.3(3), with the actual even generator. -/
theorem secondRepresentation_standardEven_delta (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    secondRepresentation (standardEven α hα) (delta2 b) = delta2 (α.val b) := by
  rw [secondRepresentation_standardEven]
  exact psiAut2Even_delta α.val α.prop hα b

/-- The odd second generator is an isometry between the two different orbit modules. -/
def oddSecondTransport (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega) :
    B1A2 ≃ₗ[ℝ] B3A2 := psiAut2Odd α.val α.prop hα

theorem oddSecondTransport_vector (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (a : A2) :
    oddSecondTransport α hα (secondAxisDomain.vector a) =
      B3Axis2.geometry.vector (firstSecond.pointMap thirdSecond (loopInverseEquiv.trans α.val) a) := by
  obtain ⟨b,rfl⟩ := axis2Equiv.surjective a
  change psiAut2Odd α.val α.prop hα (delta2 b) = _
  calc
    _ = B3Axis2.delta (parkerSign (golayQuarterWeight b.1) (α.val b)) :=
      psiAut2Odd_delta α.val α.prop hα b
    _ = _ := by
      rw [AxisRealization.pointMap_param]
      change B3Axis2.delta (parkerSign (golayQuarterWeight b.1) (α.val b)) =
        B3Axis2.delta (α.val (loopInverse b))
      rw [loopInverse, parkerStandard_preserves_sign]

theorem oddSecondTransport_point (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (a : A2) :
    (firstSecond.pointMap thirdSecond (loopInverseEquiv.trans α.val) a).val =
      (psiAut2N α).val a.val := psiAut2Odd_point α.val α.prop hα a

theorem oddSecondTransport_delta (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    oddSecondTransport α hα (delta2 b) =
      B3Axis2.delta (parkerSign (golayQuarterWeight b.1) (α.val b)) :=
  psiAut2Odd_delta α.val α.prop hα b

theorem oddSecondTransport_isometry (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (v w : B1A2) :
    B3Axis2.form (oddSecondTransport α hα v) (oddSecondTransport α hα w) =
      secondAxisDomain.form v w := psiAut2Odd_isometry α.val α.prop hα v w

end Sporadic.Monster.Construction.TrialitySpin.HalfActions
