module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction
public import Theory.SpecificGroups.SU3.IsotropicLineSylowNormalizers

/-!
# The genuine unitary no-Borel condition in Section 17

Lemma 17.2(e) excludes the original D₀ from every Sylow two-normalizer of
L = C_G(tu)°. An actual model equivalence transports this exclusion. Every
isotropic-line stabilizer in the given unitary model is such a normalizer,
including for arbitrary Hermitian forms and for SU₃ itself. Consequently the
literal image of D₀ satisfies the geometric no-Borel condition of Lemma 3.11.

Source: GLS4, Chapter 2, Lemmas 17.2(e), 17.4, and Chapter 4, Lemma 3.11.
No identification of model lines with ambient cosets is needed.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17.ModelAction
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem not_le_normalizer_map {H K : Type*} [Group H] [Finite H]
    [Group K] [Finite K] (e : H ≃* K) (A : Subgroup H)
    (hA : ∀ P : Sylow 2 H, ¬ A ≤ normalizer (P : Set H)) :
    ∀ P : Sylow 2 K, ¬ A.map e.toMonoidHom ≤ normalizer (P : Set K) := by
  intro P hP
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  apply hA Q
  have he : (normalizer (P : Set K)).comap e.toMonoidHom = normalizer (Q : Set H) := by
    change _ = normalizer ((P : Subgroup K).map e.symm.toMonoidHom : Set H)
    rw [← map_equiv_normalizer_eq, map_equiv_eq_comap_symm']
    rfl
  rw [← he]
  exact (map_le_iff_le_comap).mp hP

open UnitaryThree.OddTorusNormalizer

/-- The actual source fixed-set clause excludes the image of D₀ from every
isotropic-line stabilizer in PSU₃. The basis change acts on the given form
and leaves the original model image unchanged. -/
public theorem twistedPair_projective_noBorel
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : TwoCoreLocalData Z M)
    (hfix : ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2^n)^2) (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : centralizerClosure Z (d.t * ((d.u : M) : G)) ≃*
      ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveNoBorel J (((residualPairStabilizer M d.t ⊓
      centralizerClosure Z (d.t * ((d.u : M) : G))).subgroupOf
      (centralizerClosure Z (d.t * ((d.u : M) : G)))).map e.toMonoidHom) := by
  intro l hl
  obtain ⟨P, hP⟩ := UnitaryThree.OddTorusNormalizer.IsotropicSylow.projective_stabilizer J hn hc hf l hl
  rw [hP]
  exact not_le_normalizer_map e _ (twistedPair_not_le_sylow_normalizer h r d hfix) P

/-- The same source clause excludes genuine SU₃ Borels, retaining the
special-unitary carrier and its scalar center. -/
public theorem twistedPair_special_noBorel
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (d : TwoCoreLocalData Z M)
    (hfix : ∀ gamma : G ⧸ M,
      residualPairStabilizer M d.t ⊓
          centralizerClosure Z (d.t * ((d.u : M) : G)) ≤
        MulAction.stabilizer G gamma ↔
      gamma = QuotientGroup.mk 1 ∨ gamma = d.t • (QuotientGroup.mk 1 : G ⧸ M))
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2^n)^2) (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : centralizerClosure Z (d.t * ((d.u : M) : G)) ≃* J.specialSubgroup) :
    SpecialNoBorel J (((residualPairStabilizer M d.t ⊓
      centralizerClosure Z (d.t * ((d.u : M) : G))).subgroupOf
      (centralizerClosure Z (d.t * ((d.u : M) : G)))).map e.toMonoidHom) := by
  intro l hl
  obtain ⟨P, hP⟩ := UnitaryThree.OddTorusNormalizer.IsotropicSylow.special_stabilizer J hn hc hf l hl
  rw [hP]
  exact not_le_normalizer_map e _ (twistedPair_not_le_sylow_normalizer h r d hfix) P

end BenderSuzuki.ZD.Section17.ModelAction
