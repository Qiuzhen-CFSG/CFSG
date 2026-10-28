module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.Pair
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Source

/-!
# Assembly of the two remaining degree-five rank cases

The exact inverse-conjugate identity chooses the orientation in which
the actor rank is at least its fixed codimension. Splitting at rank five
then reduces the actual source pair to its small-image and large-image
geometry. Applying that reduction discharges the pair premise of the
parent's original zeroth-closure theorem.

Both geometric exclusions remain explicit here. This module is a checked
assembly implication, not a proof of source 12.1.3 before those exclusions
are supplied.
Source: Aschbacher--Smith, 12.1.3, printed pp.789--790 (PDF pp.806--807).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

/-- The source's two rank branches suffice after reversing the actual pair
when necessary. No Sylow containment is imposed on the inverse conjugate. -/
theorem five_centralizes_of_rank_cases
    (hsmall : ∀ g : G,
      let A := W.map (MulAut.conj g).toMonoidHom
      let I := inducedAutomizer W A
      A ≤ normalizer (W : Set G) → W ≤ normalizer (A : Set G) →
      ⁅W,A⁆ ≠ ⊥ → fixedCodim (automizerRepresentation W) I ≤ rank I →
      rank I < 5 → False)
    (hlarge : ∀ g : G,
      let A := W.map (MulAut.conj g).toMonoidHom
      let I := inducedAutomizer W A
      A ≤ normalizer (W : Set G) → W ≤ normalizer (A : Set G) →
      ⁅W,A⁆ ≠ ⊥ → 5 ≤ rank I → False)
    (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_contra hc
  obtain ⟨k, _, hkA, hkW, hkc, hko⟩ := exists_ordered g hA hW hc
  by_cases hr : rank (inducedAutomizer W (W.map (MulAut.conj k).toMonoidHom)) < 5
  · exact hsmall k hkA hkW hkc hko hr
  · exact hlarge k hkA hkW hkc (Nat.le_of_not_gt hr)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual

open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- The literal degree-five closure consumer with only the two geometric
rank exclusions still explicit. This retains final source assembly here. -/
theorem doubledFive_zeroClosure_of_rank_cases_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
    (∀ g : G,
      let W := componentOrbit V (T : Subgroup G)
      let A := W.map (MulAut.conj g).toMonoidHom
      let I := inducedAutomizer W A
      A ≤ normalizer (W : Set G) → W ≤ normalizer (A : Set G) →
      ⁅W,A⁆ ≠ ⊥ → fixedCodim (automizerRepresentation W) I ≤ rank I →
      rank I < 5 → False) →
    (∀ g : G,
      let W := componentOrbit V (T : Subgroup G)
      let A := W.map (MulAut.conj g).toMonoidHom
      let I := inducedAutomizer W A
      A ≤ normalizer (W : Set G) → W ≤ normalizer (A : Set G) →
      ⁅W,A⁆ ≠ ⊥ → 5 ≤ rank I → False) →
      indexedWeakClosure (componentOrbit V (T : Subgroup G)) T 0 ≤
        (T : Subgroup G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro S hc hsmall hlarge
  apply D.doubledFive_zeroClosure_of_pair_of_many h hmany B _ S hc
  intro g hg hn
  exact ZeroClosure.Mutual.five_centralizes_of_rank_cases hsmall hlarge g
    (hg.trans (D.doubledOrbit_E322 h).normalizes) hn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
