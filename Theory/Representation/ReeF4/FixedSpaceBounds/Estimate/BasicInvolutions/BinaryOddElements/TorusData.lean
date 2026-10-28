module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.SourceData
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.Inversion
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.OrbitTable

/-!
# The end-node orbit and the remaining binary Ree torus calculation

Twenty nonfixed characters in the actual twenty-four-weight end-node Weyl
orbit give displacement at least twenty in every end-node basic factor.
Conjugacy transports this rank to the literal binary coefficient embedding
and the quotient by cyclic invariants used in `BinaryOddDisplacement`.

`BinaryOddTorusCoverage` states the remaining group-theoretic and spectral
input without quantifying over representations. It requires a genuine
conjugator in the algebraic F4 carrier and twenty moving short-weight
characters for each binary element of order five or thirteen. It is only a
definition of the input: no unconditional coverage theorem is asserted here.
Arbitrary nonidentity algebraic torus parameters do not suffice for this
end-node conclusion.

Source: Guralnick--Malle, Classification of 2F-modules II, Lemma 8.8,
internal p.57; GLS3, Sections 1.14 and 2.8.
-/

public section

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Representation Subgroup
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- At least twenty of the twenty-four short-root orbit characters move. -/
@[expose] def EndWeightMovement (t : Fin 4 → Fˣ) : Prop :=
  ∃ s : Finset (Fin 24), 20 ≤ s.card ∧
    ∀ n ∈ s, corootCharacter t (EndNode.endOrbitWeight n) ≠ 1

omit [IsAlgClosed F] in
theorem EndWeightMovement.ne_one {t : Fin 4 → Fˣ} (ht : EndWeightMovement t) :
    t ≠ 1 := by
  obtain ⟨s, hs, ht⟩ := ht
  obtain ⟨n, hn⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  intro he
  exact ht n hn (by simp [he, corootCharacter])

theorem end_torus_displacement (B : AlgebraicFactor F)
    (hB : B.HasBasicHighestWeight (0, 1)) (t : Fin 4 → Fˣ)
    (ht : EndWeightMovement t) :
    20 ≤ Module.finrank F (LinearMap.range
      ((B.action.action (corootTorusElement t) : Module.End F B.Space) - 1)) := by
  classical
  obtain ⟨s, hs, ht⟩ := ht
  have hocc (n : s) : ∃ v, IsCorootWeightVector B (EndNode.endOrbitWeight n) v := by
    have he : reflectWord (EndNode.endOrbitWord n) EndNode.endHighestWeight =
        EndNode.endOrbitWeight n := EndNode.endOrbitWord_spec n
    rw [← he, EndNode.endHighestWeight_eq_basicCoefficient]
    exact highestWeight_word_occurs B (0, 1) hB (EndNode.endOrbitWord n)
  have hb := displacement_ge_of_weights B t
    (fun n : s => EndNode.endOrbitWeight n)
    (EndNode.endOrbitWeight_injective.comp Subtype.val_injective) hocc
    (fun n => ht n n.property)
  rw [Fintype.card_coe] at hb
  exact hs.trans hb

/-- Pure group geometry and the short-root spectrum, with the literal
coefficient embedding. This does not quantify over representations. -/
@[expose] def BinaryOddTorusCoverage (F : Type*) [Field F] [IsAlgClosed F] : Prop :=
  ∀ (f : CoefficientField 0 →+* F) (x : Model 0),
    (orderOf x = 5 ∨ orderOf x = 13) →
    ∃ (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ),
      Classification.splitEmbedding f (toSplitGroup 0 x) =
        c * corootTorusElement t * c⁻¹ ∧ EndWeightMovement t

theorem binary_fixedCodim_eq_torus_rank (B : AlgebraicFactor F)
    (f : CoefficientField 0 →+* F) (x : Model 0)
    (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ)
    (he : Classification.splitEmbedding f (toSplitGroup 0 x) =
      c * corootTorusElement t * c⁻¹) :
    Module.finrank F (B.Space ⧸ invariants
      ((B.restrict ((Classification.splitEmbedding f).comp (toSplitGroup 0))).ρ.comp
        (zpowers x).subtype)) =
    Module.finrank F (LinearMap.range
      ((B.action.action (corootTorusElement t) : Module.End F B.Space) - 1)) := by
  let ρ : Representation F (Variety.Point (F4Chevalley.Carrier (k := F))) B.Space :=
    (Units.coeHom _).comp B.action.action
  let σ : Representation F (Model 0) B.Space :=
    (B.restrict ((Classification.splitEmbedding f).comp (toSplitGroup 0))).ρ
  change Module.finrank F (B.Space ⧸ invariants (σ.comp (zpowers x).subtype)) = _
  rw [cyclic_fixedCodim_eq_rank]
  have hact : σ x = ρ (c * corootTorusElement t * c⁻¹) :=
    congrArg ρ he
  have hc := cyclic_fixedCodim_conj ρ c (corootTorusElement t)
  rw [cyclic_fixedCodim_eq_rank, cyclic_fixedCodim_eq_rank] at hc
  exact (congrArg (fun a : Module.End F B.Space =>
    Module.finrank F (LinearMap.range (a - 1))) hact).trans hc

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
