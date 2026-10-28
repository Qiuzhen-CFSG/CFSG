module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Data
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic

/-!
# Local conjugacy reduction for centralizers with central involutions

Conjugating by an element of `localP` transports its literal centralizer
intersection and derived subgroup. The marked eight-group is normalized by
`localP`, so representative derived equalities give the same equality for
every centralizer passing the finite sieve.

The two finite inputs remain explicit here so that the sieve can reuse
centralizer transport without importing its own final assembly.
`LocalCentralizers` discharges them using the checked sieve and representative
calculations and proves `localCentralizerDerivedNormal`. The parent
`DerivedEightConjugacy` owns the transport from an ambient involution
centralizer and the source conjugacy conclusion.

Source motivation: GLS3 Table 5.3r and pp.291–292; Aschbacher–Smith I.2.2(7),
pp.412–413. See `LocalCriterion` for the exact sufficient local statement.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover

namespace LocalCentralizers

/-- Conjugation by a local element preserves the literal centralizer
intersection. This concerns only the fixed local subgroup. -/
public theorem map_centralizerAt (g : Model) (hg : g ∈ localP) (i : Model) :
    (centralizerAt i).map (MulAut.conj g).toMonoidHom =
      centralizerAt (MulAut.conj g i) := by
  let a := MulAut.conj g
  have hP : localP.map a.toMonoidHom = localP :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
  have hC : (centralizer ({i} : Set Model)).map a.toMonoidHom =
      centralizer ({a i} : Set Model) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change a y * a i = a i * a y
      simpa only [map_mul] using
        congrArg a (mem_centralizer_singleton_iff.mp hy)
    · intro hx
      refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply a.injective
      simpa only [map_mul, a.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp hx
  unfold centralizerAt
  rw [map_inf _ _ _ a.injective, hP, hC]

/-- Local conjugacy preserves the order used in the representative input. -/
public theorem card_centralizerAt_conj (g : Model) (hg : g ∈ localP) (i : Model) :
    Nat.card (centralizerAt (MulAut.conj g i)) = Nat.card (centralizerAt i) := by
  rw [← map_centralizerAt g hg i, card_map_of_injective (MulAut.conj g).injective]

/-- Every accepted centralizer has the fixed derived eight-group once the
independent finite sieve and representative calculations have been supplied. -/
public theorem derived_eq_of_certificates
    (hcover : RepresentativeCover) (hderived : RepresentativeDerived)
    (i : Model) (hi : i ∈ localP) (hsq : i ^ 2 = 1)
    (hcard : Nat.card (centralizerAt i) = 256)
    (hcentral : ∀ x ∈ centralizerAt i, x ^ 2 = 1 →
      x ∈ centralizer (centralizerAt i : Set Model)) :
    ⁅centralizerAt i, centralizerAt i⁆ = elementary 2 := by
  obtain ⟨r, g, hg, rfl⟩ := hcover i hi hsq hcard hcentral
  rw [card_centralizerAt_conj g hg] at hcard
  rw [← map_centralizerAt g hg, ← map_commutator, hderived r hcard]
  exact mem_normalizer_iff_map_conj_eq.mp
    (RankOneEightCharacteristic.localP_le_normalizer_elementary_two hg)

end LocalCentralizers

/-- Conditional assembly of the exact requested criterion. The two inputs
are finite calculations on the fixed carrier and must still be discharged. -/
public theorem localCentralizerDerivedNormal_of_certificates
    (hcover : LocalCentralizers.RepresentativeCover)
    (hderived : LocalCentralizers.RepresentativeDerived) :
    LocalCentralizerDerivedNormal := by
  intro i hi hsq
  dsimp only
  intro hcard hcentral
  change localP ≤ normalizer
    ((⁅LocalCentralizers.centralizerAt i, LocalCentralizers.centralizerAt i⁆ :
      Subgroup Model) : Set Model)
  rw [LocalCentralizers.derived_eq_of_certificates hcover hderived i hi hsq hcard hcentral]
  exact RankOneEightCharacteristic.localP_le_normalizer_elementary_two

end Rudvalis.CoveringIncidence.NormalizerGeometry
