module

public import Theory.SpecificGroups.Suzuki.TwoConjugateWitness.Witness
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The original Suzuki branch of E.2.7

For the actual Suzuki carrier, the elementary subgroup in the prescribed
Sylow center constructs an E.2.4 pair. Its conjugator is internal, its Sylow
subgroup is the intersection with the original ambient Sylow, and the core
of the original normalizer intersection is trivial. One isomorphism identifies
the generated subgroup and that same intersection with a Suzuki group and
its Borel. This pair is directly consumable by the E.2.9 quotient-lift API.

No recognition, pair, subfield, or Sylow conclusion remains an input.
Source: Aschbacher--Smith, E.2.7, printed p.218, Bender-group paragraph.
-/

public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.Suzuki

/-- The Suzuki model and Borel marking attached to the original E.2.4 pair. -/
structure SourceWitness {m : ℕ} (S : Sylow 2 (SuzukiMatrixGroup m))
    (V : Subgroup (SuzukiMatrixGroup m)) extends
    QuotientLift.Pair S (normalizer (S : Set (SuzukiMatrixGroup m))) V where
  outside : (conjugator : SuzukiMatrixGroup m) ∉ normalizer (S : Set (SuzukiMatrixGroup m))
  normalizer_eq : (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup =
    normalizer (sylow : Set subgroup)
  core_eq_bot : ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).normalCore = ⊥
  parameter : ℕ
  positive : 0 < parameter
  degree_dvd : 2 * parameter + 1 ∣ 2 * m + 1
  equiv : subgroup ≃* SuzukiMatrixGroup parameter
  borel_eq : ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).map equiv.toMonoidHom =
    normalizer ((sylow : Subgroup subgroup).map equiv.toMonoidHom : Set (SuzukiMatrixGroup parameter))
  borel_conjugate : ∃ c : SuzukiMatrixGroup parameter,
    ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf subgroup).map equiv.toMonoidHom =
      (SuzukiBorelSubgroup parameter).map (MulAut.conj c).toMonoidHom

/-- The E.2.4 pair with its actual Suzuki and Borel models, from the weaker
condition that the elementary subgroup lies in the prescribed Sylow. -/
theorem source_witness_of_le_sylow {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (V : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hrank : 1 < primeRank 2 V) :
    Nonempty (SourceWitness S V) := by
  have hcard : 2 < Nat.card V := by
    by_contra hn
    have hr := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 1) V
      (by simpa only [pow_one] using Nat.le_of_not_gt hn)
    omega
  obtain ⟨w⟩ := suzuki_twoConjugateWitness hm S V hVS hcard
  have hclosed : ∃ P : Sylow 2
      ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf w.subgroup).normalCore,
      (P : Subgroup ((normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf w.subgroup).normalCore).Normal := by
    rw [w.core_eq_bot]
    exact ⟨default, inferInstance⟩
  exact ⟨{
    subgroup := w.subgroup
    le := w.le
    conjugator := w.conjugator
    generate := w.generate
    sylow := w.sylow
    sylow_eq := w.sylow_eq
    core_two_closed := hclosed
    outside := w.outside
    normalizer_eq := w.normalizer_eq
    core_eq_bot := w.core_eq_bot
    parameter := w.parameter
    positive := w.positive
    degree_dvd := w.degree_dvd
    equiv := w.equiv
    borel_eq := w.borel_eq
    borel_conjugate := w.borel_conjugate }⟩

/-- The literal Suzuki model branch used in E.2.7: the original elementary
subgroup lies in the ambient image of the center of the prescribed Sylow,
and has binary rank greater than one. -/
theorem source_witness {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m))
    (V : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 V]
    (hVZ : V ≤ (center S).map (S : Subgroup (SuzukiMatrixGroup m)).subtype)
    (hrank : 1 < primeRank 2 V) : Nonempty (SourceWitness S V) :=
  source_witness_of_le_sylow hm S V (hVZ.trans (map_subtype_le _)) hrank

end CFSG.Quasithin.ChapterE.Witnesses.Suzuki
end
