module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible

import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit


/-!
# Hermitian coordinates on the actual chosen orbit and automizer

The descended component marking transports through the literal subgroup
coordinates. Uniqueness places its full normalizer in N_G(L), so the component
image is normal in the actual automizer. Its coordinate action therefore embeds
in the Hermitian normalizer and has two-rank 4n; the original orbit has rank 9n.

The private implementation import is confined to checking the original
conjugation formula for the component projection. The proof of coordinate
composition is performed on linear maps before instantiating the subgroup
carriers, avoiding repeated reduction of the dependent orbit-action definitions.
These are the dimension and two-rank inputs of Table 7.2.1 and 8.2.4, not the
source exclusion. Final assembly remains with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith 3.2.9(4), 7.2.1 and 8.2.2–4, printed
pp.582–583, 698 and 714–716 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
open Chapter7.NormalizedSource.NonMathieuHermitian
private theorem intertwines_through_coordinates
    {U₁ U₂ U₃ : Type*} [AddCommGroup U₁] [AddCommGroup U₂] [AddCommGroup U₃]
    [Module (ZMod 2) U₁] [Module (ZMod 2) U₂] [Module (ZMod 2) U₃]
    (c : U₁ ≃ₗ[ZMod 2] U₂) (e : U₁ ≃ₗ[ZMod 2] U₃)
    (f : U₁ →ₗ[ZMod 2] U₁) (g : U₂ →ₗ[ZMod 2] U₂) (a : U₃ →ₗ[ZMod 2] U₃)
    (hc : ∀ w, g (c w) = c (f w)) (he : ∀ w, e (f w) = a (e w)) (v : U₂) :
    (c.symm.trans e) (g v) = a ((c.symm.trans e) v) := by
  have h : c.symm (g v) = f (c.symm v) := by
    apply c.injective
    rw [c.apply_symm_apply, ← hc, c.apply_symm_apply]
  exact (congrArg e h).trans (he (c.symm v))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original component's conjugation homomorphism into the full automizer. -/
def hermitianComponentAutomizer : L →* ChapterE.Automizer D.sourceOrbit :=
  D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)

private theorem componentAutomizer_normal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    D.hermitianComponentAutomizer.range.Normal := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  have hi : D.hermitianComponentAutomizer.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l, l.property, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h)
  exact hi ▸ Normal.map inferInstance qN W.normalizerMonoidHom.rangeRestrict_surjective

variable (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

/-- The binary coordinates on the literal ambient orbit subgroup. -/
def hermitianOrbitCoordinates : Additive D.sourceOrbit ≃ₗ[ZMod 2] Space n :=
  D.sourceOrbitCoordinates.symm.trans d.linearEquiv

omit [Finite G] in
private theorem sourceOrbitCoordinates_component (l : L) (w : D.orbitSpace) :
    ChapterE.automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l)
      (D.sourceOrbitCoordinates w) = D.sourceOrbitCoordinates
        ((D.orbitRepresentation.comp D.orbitComponent.subtype) (D.orbitComponentHom l) w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact ((D.sourceOrbitCoordinates_apply
    (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
      (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
        (D.sourceOrbitCoordinates_apply w).symm)).symm

omit [Finite G] in
private theorem hermitianOrbitCoordinates_component (l : L) (v : Additive D.sourceOrbit) :
    D.hermitianOrbitCoordinates n d
      (ChapterE.automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l) v) =
      overgroupAction n (binaryImage n) (d.groupEquiv (D.orbitComponentHom l))
        (D.hermitianOrbitCoordinates n d v) := by
  exact intertwines_through_coordinates D.sourceOrbitCoordinates d.linearEquiv
    ((D.orbitRepresentation.comp D.orbitComponent.subtype) (D.orbitComponentHom l))
    (ChapterE.automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l))
    (overgroupAction n (binaryImage n) (d.groupEquiv (D.orbitComponentHom l)))
    (D.sourceOrbitCoordinates_component l) (d.intertwines (D.orbitComponentHom l)) v

/-- Transport of the entire actual automizer, preserving the component map
and the original subgroup coordinates. -/
theorem sourceOrbit_hermitian_normalizer_embedding
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∃ j : ChapterE.Automizer D.sourceOrbit →* binaryNormalizer n,
      Function.Injective j ∧
      (∀ g v, D.hermitianOrbitCoordinates n d
        (ChapterE.automizerRepresentation D.sourceOrbit g v) =
          overgroupAction n (binaryNormalizer n) (j g)
            (D.hermitianOrbitCoordinates n d v)) ∧
      (∀ l : L, (j (D.hermitianComponentAutomizer l)).val =
        (d.groupEquiv (D.orbitComponentHom l)).val) := by
  let := D.componentAutomizer_normal h
  exact exists_normalizer_embedding (ChapterE.automizerRepresentation D.sourceOrbit) n
    D.hermitianComponentAutomizer
    (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
    (D.hermitianOrbitCoordinates n d) (D.hermitianOrbitCoordinates_component n d)
    (ChapterE.automizerRepresentation_injective D.sourceOrbit)

include d in
/-- The 4n entry of Table 7.2.1 on the actual automizer, not an arbitrary
isomorphic actor or the smaller component image alone. -/
theorem sourceOrbit_hermitian_automizer_rank
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) = 4 * n := by
  let := D.componentAutomizer_normal h
  exact rank_of_marked_normal_range (ChapterE.automizerRepresentation D.sourceOrbit) n
    D.hermitianComponentAutomizer
    (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
    (D.hermitianOrbitCoordinates n d) (D.hermitianOrbitCoordinates_component n d)
    (ChapterE.automizerRepresentation_injective D.sourceOrbit)

include d in
/-- The actual subgroup rank follows from the descended intertwiner. -/
theorem sourceOrbit_hermitian_rank : rank D.sourceOrbit = 9 * n := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  change Nat.card D.sourceOrbit = _ at hc
  rw [Nat.card_zmod, (D.hermitianOrbitCoordinates n d).finrank_eq, finrank_binary] at hc
  rw [rank, hc, Nat.log_pow (by decide)]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
