module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.Lifts
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.SplitSetup
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.RootExtension
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.MatrixFactorization
public import Theory.GroupTheory.PResidual.PrimePowerGeneration
public import Theory.GroupTheory.PResidual.PrimeToSubnormal

/-!
# Reducing the elementary triality index to split D4 geometry

Odd-characteristic interpolation extends centralization of the base-field SL₂
to the full split central factor, including q = 3. The exact fixed-point
calculation for the conjugated three-arm central product then identifies the
complementary image as a pullback from the split centralizer. Normality pulls
back, and its index divides the split relative index.

An alternative reduction needs only coverage of p-elements in the split
centralizer. Transvection generation then identifies the complementary image
with the elementary centralizer's prime-to-p residual, proving both normality
and coprime index. `HighestUnipotentFactorization` is the concrete matrix
obligation supplying that coverage; it remains explicit and unproved here.
The earlier split-normalizer and index reductions are retained. These
conditional reductions do not establish the unconditional elementary index
theorem. `ElementaryIndex/Consumer` applies them to the literal residual,
without adding a coprime-center hypothesis.

Sources: GLS3 §§2.4, 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39, especially (*) and the triality case.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The elementary centralizer embeds into the full split centralizer. -/
def centralizerToSplit (hp : Odd P.prime) :
    elementaryCentralizer D →* splitCentralizer D :=
  ((elementaryInclusion P).comp (elementaryCentralizer D).subtype).codRestrict _ fun x => by
    apply (centralizer_base_eq_split hp D).le
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact congrArg (elementaryInclusion P)
      (Subgroup.mem_centralizer_iff.mp x.property _ ⟨a, rfl⟩)

/-- Exact pullback of the split subsystem, retaining the elementary subgroup. -/
theorem range_elementaryCentralizerHom_eq_comap (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b)) :
    (elementaryCentralizerHom D C hcomm).range =
      ((splitComplementSubgroup D C).subgroupOf (splitCentralizer D)).comap
        (centralizerToSplit D hp) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨PinnedRankOneMaps.armsDiagonal P a, rfl⟩
  · intro x hx
    have hsplit : elementaryInclusion P x.val ∈ (splitComplementHom D C).range :=
      (range_splitComplementHom D C).ge ⟨hx, x.val.val.property⟩
    obtain ⟨a, ha⟩ := hsplit
    exact ⟨a, Subtype.ext (Subtype.ext (Subtype.ext ha))⟩

/-- Split normalization gives normality relative to the elementary centralizer. -/
theorem elementaryCentralizerHom_normal_of_split (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : splitCentralizer D ≤ Subgroup.normalizer (splitComplementSubgroup D C)) :
    (elementaryCentralizerHom D C hcomm).range.Normal := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hnormal
  exact (congrArg (fun H : Subgroup (elementaryCentralizer D) => H.Normal)
    (range_elementaryCentralizerHom_eq_comap D C hp hcomm)).mpr
      (Subgroup.normal_comap (centralizerToSplit D hp))

/-- The elementary index divides the index inside the full split centralizer. -/
theorem elementaryCentralizerHom_index_dvd_split (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : splitCentralizer D ≤ Subgroup.normalizer (splitComplementSubgroup D C)) :
    (elementaryCentralizerHom D C hcomm).range.index ∣
      ((splitComplementSubgroup D C).subgroupOf (splitCentralizer D)).index := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hnormal
  have he := (congrArg Subgroup.index
    (range_elementaryCentralizerHom_eq_comap D C hp hcomm)).trans
      (Subgroup.index_comap _ (centralizerToSplit D hp))
  exact he.symm ▸ Subgroup.relIndex_dvd_index_of_normal _ _

/-- A prime-to-p split relative index gives the required elementary index. -/
theorem elementaryCentralizerHom_coprime_index_of_split (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : splitCentralizer D ≤ Subgroup.normalizer (splitComplementSubgroup D C))
    (hindex : Nat.Coprime P.prime
      ((splitComplementSubgroup D C).subgroupOf (splitCentralizer D)).index) :
    Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index :=
  hindex.coprime_dvd_right (elementaryCentralizerHom_index_dvd_split D C hp hcomm hnormal)

/-- It suffices to control p-elements of the split centralizer. -/
theorem elementary_p_element_mem_of_split
    (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hcover : ∀ (g : splitCentralizer D) (n : ℕ), g ^ (P.prime ^ n) = 1 →
      g.val ∈ splitComplementSubgroup D C)
    (x : elementaryCentralizer D) (n : ℕ) (hx : x ^ (P.prime ^ n) = 1) :
    x ∈ (elementaryCentralizerHom D C hcomm).range := by
  have hg := hcover (centralizerToSplit D hp x) n
    (by simpa only [map_pow, map_one] using congrArg (centralizerToSplit D hp) hx)
  have hf : elementaryInclusion P x.val ∈ (splitComplementHom D C).range :=
    (range_splitComplementHom D C).ge ⟨hg, x.val.val.property⟩
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, Subtype.ext (Subtype.ext (Subtype.ext ha))⟩

/-- P-element coverage identifies the exact elementary prime-to-p residual;
normality and index are conclusions, not inputs. -/
theorem elementaryCentralizerHom_eq_residual_of_split_p_elements
    (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hcover : ∀ (g : splitCentralizer D) (n : ℕ), g ^ (P.prime ^ n) = 1 →
      g.val ∈ splitComplementSubgroup D C) :
    (elementaryCentralizerHom D C hcomm).range =
      Subgroup.primeToResidual P.prime (elementaryCentralizer D) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact Matrix.SL2.map_mem_primeToResidual P.prime _ a
  · have he := Subgroup.primeToResidual_eq_closure_prime_power
      (G := elementaryCentralizer D) P.prime
    have hle : Subgroup.closure {x : elementaryCentralizer D |
        ∃ n : ℕ, x ^ (P.prime ^ n) = 1} ≤
        (elementaryCentralizerHom D C hcomm).range := by
      rw [Subgroup.closure_le]
      rintro x ⟨n, hn⟩
      exact elementary_p_element_mem_of_split D C hp hcomm hcover x n hn
    exact he.le.trans hle

/-- The single concrete matrix factorization suffices for the elementary index. -/
theorem elementaryCentralizerHom_normal_coprime_of_highest_factorization
    (hp : Odd P.prime)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hf : HighestUnipotentFactorization D C) :
    (elementaryCentralizerHom D C hcomm).range.Normal ∧
      Nat.Coprime P.prime (elementaryCentralizerHom D C hcomm).range.index := by
  have he := elementaryCentralizerHom_eq_residual_of_split_p_elements D C hp hcomm
    (split_p_element_mem_of_highest_factorization D C hf)
  exact (congrArg (fun N : Subgroup (elementaryCentralizer D) =>
    N.Normal ∧ Nat.Coprime P.prime N.index) he).mpr
      ⟨inferInstance, Subgroup.primeToResidual_index_coprime P.prime⟩

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
