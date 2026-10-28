module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.Permutations

/-!
# Permutation quotients of the full frame-torus normalizers

The geometric identification transfers the monomial action to the full
special normalizer. Its kernel is the frame torus considered as a subgroup
of that normalizer, so the first isomorphism theorem gives the relative
quotient. In characteristic two the permutation representatives prove that
the image is all of S₃.

The restriction of SU₃ → PSU₃ to the normalizers is surjective. Its scalar
kernel lies in the torus and hence in the action kernel. Descending the
homomorphism gives the projective action, with the exact projective torus
kernel and the literal conjugation formula on projective pair coordinates.

Source: GLS4, Chapter 4, Lemma 3.11(c), used in Chapter 2, Lemma 17.4.
-/

@[expose] public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open scoped Pointwise
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

section Normalizers
variable [Finite E] (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)

noncomputable def specialNormalizerAction :
    normalizer (G := J.specialSubgroup) (specialFrameTorus J P) →* Equiv.Perm (Fin 3) :=
  (specialMonomialAction J P).comp
    (MulEquiv.subgroupCongr
      (specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed)).toMonoidHom

theorem specialNormalizerAction_action (g : normalizer (G := J.specialSubgroup) (specialFrameTorus J P)) :
    HasSpecialFrameAction J P g.val (specialNormalizerAction J P q hq hcard hfixed g) :=
  specialMonomialAction_action J P
    (MulEquiv.subgroupCongr (specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed) g)

theorem specialNormalizerAction_ker :
    (specialNormalizerAction J P q hq hcard hfixed).ker =
      (specialFrameTorus J P).subgroupOf (normalizer (G := J.specialSubgroup) (specialFrameTorus J P)) := by
  ext g
  exact Iff.trans (show specialMonomialAction J P
      (MulEquiv.subgroupCongr (specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed) g) = 1 ↔
      _ from Iff.rfl) (by
    change _ ∈ (specialMonomialAction J P).ker ↔ _
    rw [specialMonomialAction_ker]
    rfl)

theorem specialNormalizerAction_surjective [CharP E 2] :
    Function.Surjective (specialNormalizerAction J P q hq hcard hfixed) :=
  (specialMonomialAction_surjective J P).comp
    (MulEquiv.subgroupCongr
      (specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed)).surjective

noncomputable def specialNormalizerQuotientEquiv [CharP E 2] :
    (normalizer (G := J.specialSubgroup) (specialFrameTorus J P) ⧸
      (specialFrameTorus J P).subgroupOf (normalizer (G := J.specialSubgroup) (specialFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq
    (specialNormalizerAction_ker J P q hq hcard hfixed).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (specialNormalizerAction J P q hq hcard hfixed)
        (specialNormalizerAction_surjective J P q hq hcard hfixed))

end Normalizers

def frameNormalizerProjection (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    normalizer (G := J.specialSubgroup) (specialFrameTorus J P) →* normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P) :=
  (J.specialToProjective.comp (normalizer (G := J.specialSubgroup) (specialFrameTorus J P)).subtype).codRestrict _
    (fun g => by
      change g.val ∈ (normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P)).comap J.specialToProjective
      rw [projectiveFrameTorus_normalizer_comap]
      exact g.property)

theorem frameNormalizerProjection_surjective (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    Function.Surjective (frameNormalizerProjection J P) := by
  intro g
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective g.val
  have hm : x ∈ normalizer (G := J.specialSubgroup) (specialFrameTorus J P) := by
    rw [← projectiveFrameTorus_normalizer_comap]
    change J.specialToProjective x ∈ normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P)
    rw [hx]
    exact g.property
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

section ProjectiveNormalizers
variable [Finite E] (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)

theorem frameNormalizerProjection_ker_le_action :
    (frameNormalizerProjection J P).ker ≤ (specialNormalizerAction J P q hq hcard hfixed).ker := by
  rw [specialNormalizerAction_ker]
  intro g hg
  apply specialToProjective_ker_le_frameTorus J P
  exact congrArg Subtype.val hg

noncomputable def projectiveNormalizerAction :
    normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P) →* Equiv.Perm (Fin 3) :=
  (frameNormalizerProjection J P).liftOfSurjective (frameNormalizerProjection_surjective J P)
    ⟨specialNormalizerAction J P q hq hcard hfixed,
      frameNormalizerProjection_ker_le_action J P q hq hcard hfixed⟩

theorem projectiveNormalizerAction_projection (g : normalizer (G := J.specialSubgroup) (specialFrameTorus J P)) :
    projectiveNormalizerAction J P q hq hcard hfixed (frameNormalizerProjection J P g) =
      specialNormalizerAction J P q hq hcard hfixed g := by
  simp [projectiveNormalizerAction, MonoidHom.liftOfSurjective]

theorem projectiveNormalizerAction_surjective [CharP E 2] :
    Function.Surjective (projectiveNormalizerAction J P q hq hcard hfixed) := by
  intro σ
  obtain ⟨g, hg⟩ := specialNormalizerAction_surjective J P q hq hcard hfixed σ
  exact ⟨frameNormalizerProjection J P g,
    (projectiveNormalizerAction_projection J P q hq hcard hfixed g).trans hg⟩

theorem projectiveNormalizerAction_ker :
    (projectiveNormalizerAction J P q hq hcard hfixed).ker =
      (projectiveFrameTorus J P).subgroupOf (normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P)) := by
  ext g
  obtain ⟨x, rfl⟩ := frameNormalizerProjection_surjective J P g
  rw [MonoidHom.mem_ker, projectiveNormalizerAction_projection]
  change x ∈ (specialNormalizerAction J P q hq hcard hfixed).ker ↔
    J.specialToProjective x.val ∈ projectiveFrameTorus J P
  rw [specialNormalizerAction_ker]
  change x.val ∈ specialFrameTorus J P ↔
    x.val ∈ (projectiveFrameTorus J P).comap J.specialToProjective
  rw [projectiveFrameTorus_comap]

theorem projectiveNormalizerAction_action (g : normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P)) :
    HasProjectiveFrameAction J P g.val (projectiveNormalizerAction J P q hq hcard hfixed g) := by
  obtain ⟨x, rfl⟩ := frameNormalizerProjection_surjective J P g
  rw [projectiveNormalizerAction_projection]
  exact (specialNormalizerAction_action J P q hq hcard hfixed x).projective J P x.val _

noncomputable def projectiveNormalizerQuotientEquiv [CharP E 2] :
    (normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P) ⧸
      (projectiveFrameTorus J P).subgroupOf (normalizer (G := ProjectiveSpecialUnitaryMatrixGroup J) (projectiveFrameTorus J P))) ≃*
        Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq
    (projectiveNormalizerAction_ker J P q hq hcard hfixed).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (projectiveNormalizerAction J P q hq hcard hfixed)
        (projectiveNormalizerAction_surjective J P q hq hcard hfixed))

end ProjectiveNormalizers

end UnitaryThree.OddTorusNormalizer
