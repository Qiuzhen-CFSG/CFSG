module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.StandardModel
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.Coverage
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Transport
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy

/-!
# The adjoint actor gap in the full linear normalizer

Conjugating an elementary cubic actor preserves its rank, cubicity and the
codimension of its literal common fixed space. Thus coverage by the explicit
upper-unitriangular/graph subgroup reduces the endpoint actor inequality to
its finite fixed-space calculation. The transport theorem applies this
reduction to any representation actually equivalent to the adjoint quotient.

The coverage and fixed-space calculation are discharged in `adjoint_actor_gap`
by the concrete actor model. Faithfulness and irreducibility remain explicit
hypotheses, as they are inherited from the source representation by the endpoint
comparison. Thus this theorem supplies the `hactors` premise of
`endpoint_displacement_of_adjoint` without any additional actor assumptions.

Source: Guralnick–Malle author manuscript, Lemma 4.5 and Proposition 4.8
step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

/-- Full-normalizer coverage and the concrete fixed-space estimate give the actor gap. -/
theorem adjoint_actor_gap_of_standardActors
    (hcover : ∀ A : Subgroup (linearNormalizer adjoint), IsElementaryTwo A →
      ∃ g : linearNormalizer adjoint,
        A.map (MulAut.conj g).toMonoidHom ≤ standardActors)
    (hstandard : ∀ A : Subgroup (linearNormalizer adjoint), A ≤ standardActors →
      IsElementaryTwo A → IsCubic (normalizerRepresentation adjoint) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation adjoint) A)
    (A : Subgroup (linearNormalizer adjoint)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation adjoint) A) (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation adjoint) A := by
  obtain ⟨g, hg⟩ := hcover A hA
  have hcg : IsCubic (normalizerRepresentation adjoint)
      (A.map (MulAut.conj g).toMonoidHom) :=
    (Representation.OrthogonalFourMinus.RankOne.InnerTransport.cubic_conj_iff
      (normalizerRepresentation adjoint) A g).mpr hc
  have hrg : rank (A.map (MulAut.conj g).toMonoidHom) ≤ 4 := by
    rwa [rank_map_conj]
  have hgap := hstandard _ hg (hA.map_conj g) hcg hrg
  simpa only [rank_map_conj, fixedCodim_map_conj] using hgap

/-- The binary adjoint quotient satisfies the actor gap, including inner and
outer actors in the full linear normalizer. -/
theorem adjoint_actor_gap
    (hf : Function.Injective adjoint) (hi : IsIrreducible adjoint)
    (A : Subgroup (linearNormalizer adjoint)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation adjoint) A) (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation adjoint) A :=
  adjoint_actor_gap_of_standardActors (standardActors_cover hf hi) standardActors_gap A hA hc hr

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Apply the standard-actor reduction to the literal endpoint representation comparison. -/
theorem actor_gap_of_equiv_of_standardActors
    {σ : Representation (ZMod 2) Group V} (e : σ.Equiv adjoint)
    (hcover : ∀ A : Subgroup (linearNormalizer adjoint), IsElementaryTwo A →
      ∃ g : linearNormalizer adjoint,
        A.map (MulAut.conj g).toMonoidHom ≤ standardActors)
    (hstandard : ∀ A : Subgroup (linearNormalizer adjoint), A ≤ standardActors →
      IsElementaryTwo A → IsCubic (normalizerRepresentation adjoint) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation adjoint) A)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 4) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A :=
  actor_gap_of_equiv e (adjoint_actor_gap_of_standardActors hcover hstandard) A hA hc hr

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
