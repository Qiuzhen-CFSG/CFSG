module
public import Theory.SpecificGroups.OmegaSixThree.VertexComparison
public import Theory.SpecificGroups.OmegaSixThree.VertexCardinality
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Complete
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.SplitMarking
/-!
# The marked unitary extension is the actual orthogonal vertex

Compose the matched exceptional isomorphism with the faithful exterior vertex
embedding. The two generator equations identify split-form Frobenius with
conjugation by the literal graph involution, so the map extends to the actual
semidirect product. Its base fixes e₅ and its outer coset negates e₅, proving
injectivity. The already established vertex order gives surjectivity.

Source: Aschbacher–Smith F.5.1(1) and F.5.3(6), printed pp.300–301.
-/

open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
open Theory.SpecificGroups.ClassicalUnitary
open SixTernaryCoordinates OmegaSixThree.OrthogonalityGraph
public noncomputable section
namespace OmegaSixThree.VertexComparison

def standardToOmega : StandardSU →* omegaPlusSixThree :=
  pspToOmega.comp specialEquivPSp.toMonoidHom

theorem standardToOmega_generator (i : Fin 2) :
    standardToOmega (unitaryGenerator i) = pspToOmega (projectiveGenerator i) := by
  change pspToOmega (specialEquivPSp (unitaryGenerator i)) = _
  rw [specialEquivPSp_generator]

theorem standardToOmega_graph (a : StandardSU) :
    standardToOmega (SplitMarking.graphAut a) =
      vertexGraphInvolution * standardToOmega a * vertexGraphInvolution⁻¹ := by
  have h : standardToOmega.comp SplitMarking.graphAut.toMonoidHom =
      (MulAut.conj vertexGraphInvolution).toMonoidHom.comp standardToOmega := by
    apply special_hom_ext
    intro i
    change standardToOmega (SplitMarking.graphAut (unitaryGenerator i)) =
      vertexGraphInvolution * standardToOmega (unitaryGenerator i) * vertexGraphInvolution⁻¹
    fin_cases i
    · change standardToOmega (SplitMarking.graphAut (unitaryGenerator 0)) =
        vertexGraphInvolution * standardToOmega (unitaryGenerator 0) * vertexGraphInvolution⁻¹
      rw [SplitMarking.graphAut_generator_zero, map_inv, standardToOmega_generator]
      exact pspToOmega_conjugates_generator_zero.symm
    · change standardToOmega (SplitMarking.graphAut (unitaryGenerator 1)) =
        vertexGraphInvolution * standardToOmega (unitaryGenerator 1) * vertexGraphInvolution⁻¹
      rw [SplitMarking.graphAut_generator_one, standardToOmega_generator]
      exact pspToOmega_conjugates_generator_one.symm
  exact congrArg (fun f : StandardSU →* omegaPlusSixThree => f a) h

abbrev SplitSU := SplitMarking.splitForm.specialSubgroup
abbrev SplitExtension := UnitaryFourOuter.Extension SplitMarking.F starRingAut
  SplitMarking.star_involutive

def splitBaseToOmega : SplitSU →* omegaPlusSixThree :=
  standardToOmega.comp SplitMarking.splitEquivStandard.toMonoidHom

theorem splitBaseToOmega_injective : Function.Injective splitBaseToOmega :=
  pspToOmega_injective.comp (specialEquivPSp.injective.comp
    SplitMarking.splitEquivStandard.injective)

theorem splitBaseToOmega_fixes_vector (a : SplitSU) :
    (splitBaseToOmega a).val (e 5) = e 5 :=
  pspToOmega_fixes_vector _

theorem splitBaseToOmega_graph (a : SplitSU) :
    splitBaseToOmega (UnitaryFourOuter.matrixAut SplitMarking.F starRingAut
      SplitMarking.star_involutive a) =
      vertexGraphInvolution * splitBaseToOmega a * vertexGraphInvolution⁻¹ := by
  change standardToOmega (SplitMarking.splitEquivStandard
    (UnitaryFourOuter.matrixAut SplitMarking.F starRingAut SplitMarking.star_involutive a)) = _
  rw [← SplitMarking.graphAut_splitEquivStandard, standardToOmega_graph]
  rfl

def outerToOmega : UnitaryFourOuter.C2 →* omegaPlusSixThree :=
  QuaternionGroup.cyclicPowerHom 2 vertexGraphInvolution (by
    rw [pow_two]
    apply Subtype.ext
    exact graphInvolution_sq)

theorem outerToOmega_generator :
    outerToOmega UnitaryFourOuter.generator = vertexGraphInvolution :=
  QuaternionGroup.cyclicPowerHom_one _ _ _

def splitExtensionToOmega : SplitExtension →* omegaPlusSixThree :=
  SemidirectProduct.lift splitBaseToOmega outerToOmega (by
    intro c
    apply MonoidHom.ext
    intro a
    rcases UnitaryFourOuter.c2_cases c with rfl | rfl
    · simp
    · change splitBaseToOmega (UnitaryFourOuter.action _ _ _ UnitaryFourOuter.generator a) = _
      rw [UnitaryFourOuter.action_generator]
      change splitBaseToOmega (UnitaryFourOuter.matrixAut _ _ _ a) =
        outerToOmega UnitaryFourOuter.generator * splitBaseToOmega a *
          (outerToOmega UnitaryFourOuter.generator)⁻¹
      rw [outerToOmega_generator, splitBaseToOmega_graph])

theorem splitExtensionToOmega_apply (a : SplitExtension) :
    splitExtensionToOmega a = splitBaseToOmega a.left * outerToOmega a.right := by rfl

theorem graphInvolution_flips_vector : vertexGraphInvolution.val (e 5) = -e 5 := by
  decide +kernel

theorem splitExtensionToOmega_mem_vertex (a : SplitExtension) :
    splitExtensionToOmega a ∈ MulAction.stabilizer omegaPlusSixThree standardFirst := by
  change splitExtensionToOmega a • point (e 5) quadratic_e5 = point (e 5) quadratic_e5
  rw [omega_smul_point, point_eq_iff, splitExtensionToOmega_apply]
  rcases UnitaryFourOuter.c2_cases a.right with h | h
  · left
    rw [h, map_one, mul_one]
    exact splitBaseToOmega_fixes_vector a.left
  · right
    rw [h, outerToOmega_generator, Subgroup.coe_mul, LinearEquiv.mul_apply,
      graphInvolution_flips_vector, map_neg, splitBaseToOmega_fixes_vector]

theorem splitExtensionToOmega_injective : Function.Injective splitExtensionToOmega := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  change splitExtensionToOmega a = 1 at ha
  have hc : a.right = 1 := by
    rcases UnitaryFourOuter.c2_cases a.right with h | h
    · exact h
    · have hv := congrArg (fun g : omegaPlusSixThree => g.val (e 5)) ha
      rw [splitExtensionToOmega_apply, h, outerToOmega_generator,
        Subgroup.coe_mul, LinearEquiv.mul_apply, graphInvolution_flips_vector,
        map_neg, splitBaseToOmega_fixes_vector] at hv
      exact ((by decide +kernel : (-e 5 : Space) ≠ e 5) hv).elim
  have hl : a.left = 1 := by
    apply splitBaseToOmega_injective
    simpa only [splitExtensionToOmega_apply, hc, map_one, mul_one] using ha
  exact SemidirectProduct.ext hl hc

def splitExtensionToVertex : SplitExtension →*
    MulAction.stabilizer omegaPlusSixThree standardFirst :=
  splitExtensionToOmega.codRestrict _ splitExtensionToOmega_mem_vertex

theorem card_splitExtension : Nat.card SplitExtension = 51840 := by
  have hbase : Nat.card SplitSU = 25920 :=
    (Nat.card_congr (SplitMarking.splitEquivStandard.trans specialEquivPSp).toEquiv).trans
      card_projective_symplectic
  rw [SemidirectProduct.card, hbase]
  have hc : Nat.card UnitaryFourOuter.C2 = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [hc]

def splitExtensionEquivVertex : SplitExtension ≃*
    MulAction.stabilizer omegaPlusSixThree standardFirst := by
  let : Finite omegaPlusSixThree := Nat.finite_of_card_ne_zero (by rw [card_omega]; decide)
  exact MulEquiv.ofBijective splitExtensionToVertex
    (((MonoidHom.injective_codRestrict _ _ _).mpr splitExtensionToOmega_injective).bijective_of_nat_card_le
      (by rw [card_standard_vertex, card_splitExtension]))

theorem splitExtensionEquivVertex_sigma :
    (splitExtensionEquivVertex (UnitaryFourOuter.sigma SplitMarking.F starRingAut
      SplitMarking.star_involutive)).val = vertexGraphInvolution := by
  change splitExtensionToOmega (SemidirectProduct.inr UnitaryFourOuter.generator) = _
  rw [splitExtensionToOmega_apply]
  change splitBaseToOmega 1 * outerToOmega UnitaryFourOuter.generator = _
  rw [map_one, one_mul, outerToOmega_generator]

end OmegaSixThree.VertexComparison
