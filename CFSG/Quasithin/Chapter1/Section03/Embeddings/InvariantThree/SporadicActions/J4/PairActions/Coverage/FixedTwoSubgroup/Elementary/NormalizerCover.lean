module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.Reduction

/-!
# Elementary normalizers from proper Sylow-overgroup coverage

The full normalizer of a `FixedTwoElementaryNormalizer` contains the supplied
ambient Sylow subgroup. It is proper by simplicity and the certified
noncommutation of the standard generators. Thus the independent classification
of proper Sylow overgroups applies directly, retaining its actual conjugator
and its three literal ambient subgroups.

The overgroup classification remains an explicit premise. The theorem below
is only its specialization to elementary normalizers; it does not prove
`fixedTwoElementaryNormalizerCover`. Its premise is the expanded statement of
`Max4Conjugacy.ProperSylowOvergroupCover`, so that the independent incidence
proof can be used without adding a second classification obligation.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), citing Aschbacher, *Overgroups of Sylow subgroups in
sporadic groups*, Memoirs AMS 60 (1986), no.343. The ATLAS generators identify
the candidate carriers but do not themselves prove exhaustive coverage.
-/

public section

open Subgroup Janko4.LocalStructure.SymmetricLinear

attribute [local irreducible] Janko4.modelGroup max4Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- Specialize proper Sylow-overgroup coverage to the full elementary
normalizer. The independent ambient incidence premise remains undischarged. -/
theorem fixedTwoElementaryNormalizerCover_of_properSylowOvergroupCover
    (hcover : ∀ [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
      [Group.IsPerfect Janko4.Model] (S : Sylow 2 Janko4.Model)
      (H : Subgroup Janko4.Model), S.toSubgroup ≤ H → H ≠ ⊤ →
      ∃ g : Janko4.Model,
        H ≤ (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self
          Janko4.matrixB_pow_four).map (MulAut.conj g).toMonoidHom ∨
        H ≤ (centralizer ({Janko4.a} : Set Janko4.Model)).map
          (MulAut.conj g).toMonoidHom ∨
        H ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom) :
    FixedTwoElementaryNormalizerCover := by
  intro _ _ _ S hS A hA
  exact hcover S (normalizer (A : Set Janko4.Model))
    (hS ▸ hA.normalized) (fixedTwoElementaryNormalizer_ne_top hA)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
