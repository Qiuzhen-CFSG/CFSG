module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.StandardModel
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.Certificates
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Common-fixed-space bounds for the standard adjoint actors

The literal fourteen-coordinate action and all sixty displacement certificates
are proved in the imported leaves. Exhaustive elementary-subgroup coverage
conjugates each nontrivial elementary subgroup of the standard actors to a
catalogue entry with enough independent displacement equations. Conjugation
preserves common fixed codimension, giving `standardActors_gap` on the literal
trace-zero quotient by the scalar line. Its cubicity hypothesis matches the
actor-gap consumer; the checked bounds already hold without cubicity.

Source: Guralnick–Malle Lemma 4.5 and Proposition 4.8 step 3A;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

/-- Exhaustive internal subgroup coverage and the concrete certificates imply
the standard-actor bound. Coverage remains a genuine independent premise. -/
theorem standardActors_gap_of_catalogue_cover
    (hcover : ∀ (A : Subgroup (linearNormalizer adjoint)), A ≤ standardActors →
      IsElementaryTwo A → rank A ≤ 4 →
      ∃ (i : Fin 60) (g : linearNormalizer adjoint),
        A.map (MulAut.conj g).toMonoidHom = FixedBounds.catalogueSubgroup i ∧
          rank A ≤ (FixedBounds.catalogueGenerators i).length)
    (A : Subgroup (linearNormalizer adjoint)) (hAS : A ≤ standardActors)
    (hA : IsElementaryTwo A) (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation adjoint) A := by
  obtain ⟨i, g, heq, hri⟩ := hcover A hAS hA hr
  have hd := FixedBounds.catalogue_gap i
  rw [← heq, fixedCodim_map_conj] at hd
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 hri) hd

/-- Every nontrivial elementary cubic subgroup of the standard adjoint actors
has common fixed codimension greater than twice its rank. The exhaustive
catalogue coverage and all displacement certificates are discharged. -/
theorem standardActors_gap
    (A : Subgroup (linearNormalizer adjoint)) (hAS : A ≤ standardActors)
    (hA : IsElementaryTwo A) (_hc : IsCubic (normalizerRepresentation adjoint) A)
    (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation adjoint) A :=
  standardActors_gap_of_catalogue_cover FixedBounds.standardCatalogue_cover A hAS hA hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
