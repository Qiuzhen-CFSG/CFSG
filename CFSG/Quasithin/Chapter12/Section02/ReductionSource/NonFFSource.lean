module

public import CFSG.Quasithin.Chapter7.NormalizedSource.Automizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.Alternatives
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.ReducedNormal.SubspaceEquiv

/-!
# Source non-FF reductions on the original chosen orbit

The full orbit W has the literal subgroup coordinates of its existing
`orbitRepresentation`. Uniqueness puts N_G(W) in N_G(L), hence its automizer
inherits non-FF from the full linear normalizer of the image of L. The
Thompson offender argument then shows that J(T) centralizes the entire orbit.

The component map is constructed by the public restriction-action API;
its original conjugation formula is verified on every vector.
The original seed and orbit remain distinct throughout. The final source
classification remains an obligation; the doubled, Mathieu and other irreducible source branches remain open.

Source: Aschbacher--Smith, 7.0.1--2 and the proof of12.2.2, printed pp.695,795,
using3.2.2(6),3.1.8 and the full known-simple Theorem A.
-/

public noncomputable section
open Stellmacher Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

abbrev sourceOrbit := ReducedNormal.subspaceImage (L ⊔ (T : Subgroup G)) D.orbitSpace

omit [Finite G] in
theorem sourceOrbit_eq : D.sourceOrbit = componentOrbit V (T : Subgroup G) :=
  D.orbitSpace_image

instance sourceOrbit_elementary : IsElementaryAbelian 2 D.sourceOrbit :=
  ReducedNormal.subspaceImage_elementary _ _

/-- Original subgroup coordinates on the full orbit. -/
def sourceOrbitCoordinates : D.orbitSpace ≃ₗ[ZMod 2] Additive D.sourceOrbit :=
  ReducedNormal.subspaceEquiv (L ⊔ (T : Subgroup G)) D.orbitSpace

omit [Finite G] in
@[simp] theorem sourceOrbitCoordinates_apply (v : D.orbitSpace) :
    ((D.sourceOrbitCoordinates v).toMul : G) = v.val.toMul.val.val := by rfl

omit [Finite G] in
/-- E.3.22 on the actual T-orbit, independently of normalization of the seed. -/
theorem sourceOrbit_weakClosure_setup : ChapterE.HypothesisE322 D.sourceOrbit T := by
  have hnorm : (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [D.sourceOrbit_eq]
    exact le_normalizer_componentOrbit _ _
  refine ⟨?_, ?_, hnorm⟩
  · intro he
    rw [D.sourceOrbit_eq] at he
    exact D.ne_bot (bot_unique ((le_componentOrbit V T).trans_eq he))
  · rw [D.sourceOrbit_eq]
    exact iSup_conjugates_le_of_le_normalizer V T T D.le_sylow
      (T : Subgroup G).le_normalizer

omit [Finite G] in
/-- L normalizes the entire orbit, with the seed left unchanged. -/
theorem sourceOrbit_component_normalizes : L ≤ normalizer (D.sourceOrbit : Set G) :=
  (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left).trans
    (ReducedNormal.subspaceImage_normalized _ _
      (Representation.BinaryOffender.Homogeneous.orbitSpan_invariant _ ⊤ D.space))

/-- Uniqueness places the full orbit normalizer in the original N_G(L). -/
theorem sourceOrbit_normalizer_le
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    normalizer (D.sourceOrbit : Set G) ≤ normalizer (L : Set G) := by
  let F := D.fundamentalSetup h
  have hnormal : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [D.sourceOrbit_eq]
    have hh := F.join_normalizes_module
    rwa [Chapter3.Section02.localJoin, D.localOrbit_eq, D.fundamentalSetup_module h] at hh
  exact D.normal_subgroup_normalizer_le h
    (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right)
    D.sourceOrbit_weakClosure_setup.nontrivial hnormal

/-- The source full linear normalizer, for the image of L on the full orbit. -/
abbrev sourceOrbitNormalizerRepresentation :=
  normalizerRepresentation (D.orbitRepresentation.comp D.orbitComponent.subtype)

/-- Non-FF for the source linear normalizer gives non-FF for the actual
ambient automizer, on the literal subgroup coordinates. -/
theorem sourceOrbit_automizer_nonFF
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ IsFFModule (ChapterE.automizerRepresentation D.sourceOrbit) := by
  let f : L →* D.orbitComponent :=
    (restrictedActionSurjection (reducedRepresentation (L ⊔ (T : Subgroup G)))
      D.orbitSpace (L.subgroupOf (L ⊔ (T : Subgroup G)))
      D.orbitSpace_component_invariant).comp
        (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom
  have hf : Function.Surjective f :=
    (restrictedActionSurjection_surjective _ _ _ D.orbitSpace_component_invariant).comp
      (subgroupOfEquivOfLe le_sup_left).symm.surjective
  apply Chapter7.NormalizedSource.automizer_nonFF D.sourceOrbit L
    D.sourceOrbit_component_normalizes (D.sourceOrbit_normalizer_le h)
    (D.orbitRepresentation.comp D.orbitComponent.subtype)
    f hf D.sourceOrbitCoordinates _ hnon
  intro l v
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

/-- The source non-FF assumption forces the original Thompson subgroup to
centralize the full orbit; normalization of the seed is not assumed. -/
theorem sourceOrbit_thompson_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.sourceOrbit : Set G) :=
  Chapter7.NormalizedSource.thompson_centralizes D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
