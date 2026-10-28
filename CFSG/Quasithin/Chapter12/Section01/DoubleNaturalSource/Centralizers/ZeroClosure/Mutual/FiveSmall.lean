module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.FiveSmallLinear
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.FiveSmallTransport
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ZeroClosure.Mutual.FiveReduction
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Application

/-!
# The small-rank mutually normalizing branch of 12.1.3

The offender budget gives rank and fixed codimension four, so the reverse
actor is also inner. The natural summand has fixed codimension two and
moved dimension two. Its literal inverse conjugate contradicts the inner
small-moved-space bound. This discharges the small-rank exclusion in the
chosen-orbit zeroth-closure reduction; the compatible model is constructed.

Nonsingular centralizer control and the large-rank exclusion remain explicit
in the closure consumer. Their proofs and final assembly belong to
`qt-d-double-natural-centralizers`; this is not yet the whole of 12.1.3.
Source: Aschbacher--Smith, 12.1.3, printed pp.789--790 (PDF806--807).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

/-- The small-image-rank branch of source 12.1.3, on the actual pair of
mutually normalizing conjugates. -/
theorem five_small_false
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hW : W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    (hnc : ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (ho : fixedCodim (automizerRepresentation W)
      (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) ≤
        rank (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)))
    (hr : rank (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) < 5) : False := by
  let A := W.map (MulAut.conj g).toMonoidHom
  let I := inducedAutomizer W A
  let A' := W.map (MulAut.conj g⁻¹).toMonoidHom
  let I' := inducedAutomizer W A'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary W A hA
  have hn : I ≠ ⊥ := inducedAutomizer_ne_bot_of_commutator_ne_bot hA hnc
  obtain ⟨hi,hr4,hc4,hp,hq⟩ := five_small_offender_parameters S I hn
    (by simpa only [hρ] using ho) hr
  have hA' := reverse_normalizes g hW
  have hW' := reverse_is_normalized g hA
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I' := inducedAutomizer_elementary W A' hA'
  have hc' : fixedCodim S.representation I' = 4 := by
    rw [hρ,reverse_rank g⁻¹ hA' hW',inv_inv]
    exact hr4
  have hi' := five_inner_of_small_fixed S I' (by omega)
  obtain ⟨hfixed,hmoved⟩ := inner_natural_dimensions S I hi
  apply reverse_subspace_false S hρ g hA hW hi' S.natural
  · change 2 ≤ finrank (ZMod 2) S.natural - finrank (ZMod 2) ↥(S.natural ⊓ S.fixed I)
    rw [hfixed,hp]
  · rw [hmoved,hq]
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual

open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)

/-- The small-rank premise of degree-five zeroth closure is discharged.
The nonsingular and large-rank source arguments remain with this owner. -/
theorem doubledFive_zeroClosure_of_large_rank_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    B.NonsingularCentralizers →
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
  intro hc hlarge
  obtain ⟨S⟩ := D.doubleNatural_sourceModel_of_many h hmany B
  let M := S.automizerModel (D.doubledOrbit_normalizer_eq h B.orbit_eq)
  exact D.doubledFive_zeroClosure_of_rank_cases_of_many h hmany B S hc
    (fun g hA hW hnc ho hr =>
      ZeroClosure.Mutual.five_small_false M.setup M.representation_eq g hA hW hnc ho hr)
    hlarge
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
