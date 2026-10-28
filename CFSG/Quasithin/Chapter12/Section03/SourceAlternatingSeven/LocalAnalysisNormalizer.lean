module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Setup
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.Representation.BinaryPermutation.SevenNormalizer
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# The normalizer action in the original A₇ case

Full natural coordinates on the original V determine its whole normalizer
representation. Conjugation by N(L) descends through the characteristic
O₂,Z kernel of the original projection. Every automorphism of A₇ comes
from a unique seven-letter permutation; triviality of the linear
centralizer then identifies the transported action with that permutation.
No faithfulness of the ambient normalizer action is assumed.

The source application derives N(V) ≤ N(L) from structural 12.2.2 and the
proved Theorems A and C. From full natural coordinates it then proves the
normalizer-action part of `LocalAnalysis`, including its
compatibility with the original projection; it does not establish the
four-dimensional exclusion or either ambient point-centralizer bound.

Source: Aschbacher--Smith, 12.3.3--4, printed pp.807--809.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- A natural marking of the entire original chosen module, compatible with
its given L/O₂,Z(L) projection. Constructing this is source Lemma 12.3.3,
including exclusion of the four-dimensional alternative and the lift from
V/C_V(L) to V. -/
structure NaturalCoordinates where
  coordinates : V ≃* Multiplicative EvenWord
  equivariant : ∀ (l : L) (v : V),
    (coordinates (V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ v)).toAdd =
      evenRepresentation (S.projection l).val (coordinates v).toAdd

/-- Conjugation on the original central quotient, not on L/O₂(L). -/
def quotientNormalizerAction : normalizer (L : Set G) →*
    MulAut (alternatingGroup (Fin 7)) :=
  (MulAut.congr S.quotient).toMonoidHom.comp
    ((quotientAut (centralPreimage (pCore 2 L))).comp L.normalizerMonoidHom)

theorem quotientNormalizerAction_projection (n : normalizer (L : Set G)) (l : L) :
    S.quotientNormalizerAction n (S.projection l) =
      S.projection (L.normalizerMonoidHom n l) := by
  change S.quotient ((quotientAut (centralPreimage (pCore 2 L))
    (L.normalizerMonoidHom n)) (S.quotient.symm (S.quotient _))) = _
  rw [S.quotient.symm_apply_apply]
  change S.quotient ((quotientAut (centralPreimage (pCore 2 L))
    (L.normalizerMonoidHom n)) (QuotientGroup.mk' (centralPreimage (pCore 2 L)) l)) = _
  rw [quotientAut_apply_mk]
  rfl

def normalizerPermutation : normalizer (L : Set G) →* Equiv.Perm (Fin 7) :=
  BinaryPermutation.SevenNormalizer.permutationOfAut.toMonoidHom.comp
    S.quotientNormalizerAction

theorem normalizerPermutation_component (l : L) :
    S.normalizerPermutation ⟨l,L.le_normalizer l.property⟩ = (S.projection l).val := by
  have he : S.quotientNormalizerAction ⟨l,L.le_normalizer l.property⟩ =
      MulAut.conj (S.projection l) := by
    apply MulEquiv.ext
    intro a
    obtain ⟨x,rfl⟩ := S.projection_surjective a
    rw [S.quotientNormalizerAction_projection]
    change S.projection (l*x*l⁻¹) = S.projection l * S.projection x * (S.projection l)⁻¹
    simp only [map_mul,map_inv]
  change BinaryPermutation.SevenNormalizer.permutationOfAut
    (S.quotientNormalizerAction _) = _
  rw [he,BinaryPermutation.SevenNormalizer.permutationOfAut_conj]

/-- The original chosen module has its whole normalizer in N(L).
The earlier A and C classification inputs are discharged. -/
theorem normalizer_le_component (S : Setup T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) :=
  CFSG.Quasithin.Chapter12.Section02.Hypothesis1223.source_chosen_normalizer_le
    S.hypothesis structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) S.chosen

namespace NaturalCoordinates
variable {S} (E : S.NaturalCoordinates)

def conjugation (n : normalizer (V : Set G)) : EvenWord ≃ₗ[ZMod 2] EvenWord :=
  let e := AddEquiv.toMultiplicative.symm
    (E.coordinates.symm.trans ((V.normalizerMonoidHom n).trans E.coordinates))
  e.toLinearEquiv (fun c x => ZMod.map_smul e.toAddMonoidHom c x)

theorem conjugation_equivariant
    (hN : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (n : normalizer (V : Set G)) (a : alternatingGroup (Fin 7)) (w : EvenWord) :
    E.conjugation n (evenRepresentation a.val w) =
      evenRepresentation (S.quotientNormalizerAction ⟨n,hN n.property⟩ a).val
        (E.conjugation n w) := by
  obtain ⟨l,rfl⟩ := S.projection_surjective a
  rw [S.quotientNormalizerAction_projection]
  let v := E.coordinates.symm (Multiplicative.ofAdd w)
  have hv : (E.coordinates v).toAdd = w := by simp only [v,E.coordinates.apply_symm_apply,toAdd_ofAdd]
  have hleft := E.equivariant l v
  rw [hv] at hleft
  have hright := E.equivariant (L.normalizerMonoidHom ⟨n,hN n.property⟩ l)
    (V.normalizerMonoidHom n v)
  change (E.coordinates (V.normalizerMonoidHom n
    (E.coordinates.symm (Multiplicative.ofAdd (evenRepresentation (S.projection l).val w))))).toAdd = _
  rw [← hleft]
  change (E.coordinates (V.normalizerMonoidHom n
    (E.coordinates.symm (E.coordinates
      (V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ v))))).toAdd = _
  rw [E.coordinates.symm_apply_apply]
  change (E.coordinates (V.normalizerMonoidHom n
    (V.normalizerMonoidHom ⟨l,S.chosen.normalizes l.property⟩ v))).toAdd =
      evenRepresentation (S.projection (L.normalizerMonoidHom ⟨n,hN n.property⟩ l)).val
        (E.coordinates (V.normalizerMonoidHom n v)).toAdd
  rw [← hright]
  congr 2
  apply Subtype.ext
  change (n:G) * ((l:G) * (v:G) * (l:G)⁻¹) * (n:G)⁻¹ =
    ((n:G)*(l:G)*(n:G)⁻¹) * ((n:G)*(v:G)*(n:G)⁻¹) * ((n:G)*(l:G)*(n:G)⁻¹)⁻¹
  group

theorem conjugation_eq_permutation
    (hN : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (n : normalizer (V : Set G)) (w : EvenWord) :
    E.conjugation n w = evenRepresentation
      (S.normalizerPermutation ⟨n,hN n.property⟩) w := by
  let c := evenWordsEquivCore.symm.trans ((E.conjugation n).trans evenWordsEquivCore)
  have hc : ∀ (a : alternatingGroup (Fin 7)) v,
      c (BinaryPermutation.coreRepresentation (Fin 7) a.val v) =
        BinaryPermutation.coreRepresentation (Fin 7)
          (S.quotientNormalizerAction ⟨n,hN n.property⟩ a).val (c v) := by
    intro a v
    exact congrArg evenWordsEquivCore
      (E.conjugation_equivariant hN n a (evenWordsEquivCore.symm v))
  have hh := BinaryPermutation.SevenNormalizer.intertwiner c
    (S.quotientNormalizerAction ⟨n,hN n.property⟩) hc (evenWordsEquivCore w)
  exact evenWordsEquivCore.injective hh

/-- The actual normalizer action induced by full natural coordinates. -/
def normalizerModel
    (hN : normalizer (V : Set G) ≤ normalizer (L : Set G)) : NormalizerModel V where
  coordinates := E.coordinates
  permutation := S.normalizerPermutation.comp (inclusion hN)
  equivariant n v := by
    have h := E.conjugation_eq_permutation hN n (E.coordinates v).toAdd
    change (E.coordinates (V.normalizerMonoidHom n
      (E.coordinates.symm (E.coordinates v)))).toAdd = _ at h
    rwa [E.coordinates.symm_apply_apply] at h

theorem normalizerModel_component
    (hN : normalizer (V : Set G) ≤ normalizer (L : Set G)) (l : L) :
    (E.normalizerModel hN).permutation ⟨l,S.chosen.normalizes l.property⟩ =
      (S.projection l).val := S.normalizerPermutation_component l

/-- Source 12.3.4(3), conditional only on full natural coordinates and the
earlier structural theorem. The marking covers the original V. -/
def sourceNormalizerModel
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : NormalizerModel V :=
  E.normalizerModel (S.normalizer_le_component structural)

theorem sourceNormalizerModel_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (l : L) :
    (E.sourceNormalizerModel structural).permutation ⟨l,S.chosen.normalizes l.property⟩ =
      (S.projection l).val := E.normalizerModel_component _ l

end NaturalCoordinates
end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
