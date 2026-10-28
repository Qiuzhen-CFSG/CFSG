module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.TwoLocalCandidates.SelfNormalizing
public import Theory.GroupTheory.SylowContainingTwoLocal

/-!
# Sylow-containing maximal two-local coverage for Held

This module isolates the final assembly from the concrete Held calculations.
For a fixed Sylow subgroup, `exists_normal_elementary_normalizer_of_sylow_le`
reduces a maximal two-local to the normalizer of a nontrivial normal
elementary abelian subgroup of that Sylow.  It therefore suffices to classify
the ambient normalizers of those subgroups **when the normalizer is maximal
two-local**.  The two `of_maximal_normalizers` adapters use precisely this
conditional catalogue to obtain the exhaustive conjugacy cover needed for
condition E.  The final `exists_sylow_two_local_cover` instantiates the adapter
with the proved concrete catalogue, discharging every coverage premise.  It
requires no simplicity, group-order, graph-preservation, pair-stabilizer or
candidate-self-normalization hypothesis.  The intrinsic self-centralizing cores
and final QT/E assembly are separate from this exhaustive cover.

The two older `of_catalogue` APIs are preserved as legacy reductions from an
impossible premise: they equate an elementary abelian subgroup with a conjugate
of a full max3/max4/max5 candidate.  Each candidate contains an element whose
square is not the identity.  `He.LegacyCatalogueSquareObstruction` proves this
obstruction and the impossibility of the legacy premise for every actual Sylow
two-subgroup.  Those APIs cannot supply concrete coverage.

Source: Aschbacher–Smith, condition E and Volume I Theorem 0.1.2(5), printed
pp. 3–4 (Volume II Theorem 0.1.1(5), pp. 481–482); GLS3, Table 5.3p.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.HeCoverage

open Subgroup

private theorem cover_of_catalogue
    (T : Sylow 2 Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ (i : Fin 3) (g : Held.He),
        R.map (T : Subgroup Held.He).subtype =
          (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (hself : ∀ i : Fin 3,
      normalizer (Held.TwoLocalCandidates.subgroup i : Set Held.He) =
        Held.TwoLocalCandidates.subgroup i)
    (M : Subgroup Held.He) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup Held.He) ≤ M) :
    ∃ (i : Fin 3) (g : Held.He),
      M = (Held.TwoLocalCandidates.subgroup i).map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨R, hR, hRn, hRe, hM⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i, g, hA⟩ := hcatalogue R hR hRn hRe
  rw [hA] at hM
  refine ⟨i, g, hM.trans ?_⟩
  calc
    normalizer ((Held.TwoLocalCandidates.subgroup i).map
      (MulAut.conj g).toMonoidHom : Set Held.He) =
        (normalizer (Held.TwoLocalCandidates.subgroup i : Set Held.He)).map
          (MulAut.conj g).toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq
        (Held.TwoLocalCandidates.subgroup i) (MulAut.conj g)).symm
    _ = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom := by rw [hself i]

/-- Legacy reduction from an impossible elementary-subgroup catalogue.
The full candidates are not elementary abelian, so this premise cannot be
instantiated.  Use `exists_sylow_two_local_cover_of_maximal_normalizers` for
the adequate normalizer catalogue. -/
public theorem exists_sylow_two_local_cover_of_catalogue
    (T : Sylow 2 Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ (i : Fin 3) (g : Held.He),
        R.map (T : Subgroup Held.He).subtype =
          (Held.TwoLocalCandidates.subgroup i).map
            (MulAut.conj g).toMonoidHom)
    (hself : ∀ i : Fin 3,
      normalizer (Held.TwoLocalCandidates.subgroup i : Set Held.He) =
        Held.TwoLocalCandidates.subgroup i) :
    ∀ M : Subgroup Held.He, IsMaximalTwoLocal M →
      (T : Subgroup Held.He) ≤ M →
      ∃ (i : Fin 3) (g : Held.He),
        M = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom := by
  intro M hM hTM
  exact cover_of_catalogue T hcatalogue hself M hM hTM

/-- Legacy existential reduction from the same impossible catalogue premise.
Use `exists_sylow_two_local_cover_of_maximal_normalizers_exists` for the
adequate input to converse assembly. -/
public theorem exists_sylow_two_local_cover_of_catalogue_exists
    (hcatalogue : ∃ T : Sylow 2 Held.He,
      ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
        ∃ (i : Fin 3) (g : Held.He),
          R.map (T : Subgroup Held.He).subtype =
            (Held.TwoLocalCandidates.subgroup i).map
              (MulAut.conj g).toMonoidHom)
    (hself : ∀ i : Fin 3,
      normalizer (Held.TwoLocalCandidates.subgroup i : Set Held.He) =
        Held.TwoLocalCandidates.subgroup i) :
    ∃ T : Sylow 2 Held.He, ∀ M : Subgroup Held.He, IsMaximalTwoLocal M →
      (T : Subgroup Held.He) ≤ M →
      ∃ (i : Fin 3) (g : Held.He),
        M = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨T, hT⟩ := hcatalogue
  exact ⟨T, exists_sylow_two_local_cover_of_catalogue T hT hself⟩

/-- A catalogue of the actual maximal elementary normalizers gives exhaustive
maximal two-local coverage for the supplied Sylow subgroup.  Maximality is
required only of the normalizer being classified; no candidate normalizer
identity or candidate two-locality hypothesis is needed. -/
public theorem exists_sylow_two_local_cover_of_maximal_normalizers
    (T : Sylow 2 Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R →
      IsMaximalTwoLocal
        (normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He)) →
      ∃ (i : Fin 3) (g : Held.He),
        normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He) =
          (Held.TwoLocalCandidates.subgroup i).map
            (MulAut.conj g).toMonoidHom) :
    ∀ M : Subgroup Held.He, IsMaximalTwoLocal M →
      (T : Subgroup Held.He) ≤ M →
      ∃ (i : Fin 3) (g : Held.He),
        M = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom := by
  intro M hM hTM
  obtain ⟨R, hR, hRn, hRe, hMR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i, g, hN⟩ := hcatalogue R hR hRn hRe (hMR ▸ hM)
  exact ⟨i, g, hMR.trans hN⟩

/-- Existential form of the adequate maximal-normalizer reduction.  The
concrete catalogue is supplied in `exists_sylow_two_local_cover` below. -/
public theorem exists_sylow_two_local_cover_of_maximal_normalizers_exists
    (hcatalogue : ∃ T : Sylow 2 Held.He,
      ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
        IsMaximalTwoLocal
          (normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He)) →
        ∃ (i : Fin 3) (g : Held.He),
          normalizer (R.map (T : Subgroup Held.He).subtype : Set Held.He) =
            (Held.TwoLocalCandidates.subgroup i).map
              (MulAut.conj g).toMonoidHom) :
    ∃ T : Sylow 2 Held.He, ∀ M : Subgroup Held.He, IsMaximalTwoLocal M →
      (T : Subgroup Held.He) ≤ M →
      ∃ (i : Fin 3) (g : Held.He),
        M = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨T, hT⟩ := hcatalogue
  exact ⟨T, exists_sylow_two_local_cover_of_maximal_normalizers T hT⟩

/-- Every maximal two-local containing a suitable Sylow two-subgroup of the
actual degree-2058 Held carrier is a conjugate of one of the literal max3,
max4 or max5 candidates.  The concrete normalizer catalogue supplies all
finite-model premises of the elementary-normalizer reduction. -/
public theorem exists_sylow_two_local_cover :
    ∃ T : Sylow 2 Held.He, ∀ M : Subgroup Held.He, IsMaximalTwoLocal M →
      (T : Subgroup Held.He) ≤ M →
      ∃ (i : Fin 3) (g : Held.He),
        M = (Held.TwoLocalCandidates.subgroup i).map
          (MulAut.conj g).toMonoidHom :=
  exists_sylow_two_local_cover_of_maximal_normalizers_exists
    Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue

end CFSG.Quasithin.MainConverse.SporadicLocal.HeCoverage
