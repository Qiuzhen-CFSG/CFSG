module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.LinearWitness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.BorelRecognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientAssembly
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.SourceAssembly
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori

/-!
# The odd torus in the projective unitary model

The model calculation used in Lemma 13.2 is the fixed part of the
two-point torus.  The model geometry module gives its exact order as
`(q + 1) / gcd 3 (q + 1)`.  Since the denominator is a divisor of the
prime `3`, this is exactly one of the two orders occurring in the source:
`q + 1` or `(q + 1) / 3`.

The exact order also proves nontriviality, including the endpoint `q = 4`.
The imported `BorelRecognition` and `AmbientTorus` modules identify the literal
`M ∩ Lᵤ` as a Borel and construct the fixed torus `Lᵤ ∩ D ∩ C_G(t)` in the
original ambient group. They prove its cyclicity, exact order, oddness,
nontriviality, pair-stabilizer placement, and normalization of its distinguished
centralizer by u, retaining both actual unitary covers and field orders.

`SourceAssembly` discharges all three geometric premises of `AmbientAssembly`:
the local torus-centralizer identity, the additional linear subgroup, and
the involution-fixed model. Its `secondCentralizerData_of_unitary_centralizers`
proves every clause of Lemma 13.2 from the preceding local centralizer and
shearing inputs and the supplied unitary branch.
`secondCentralizerData_of_minimalCounterexample` applies that construction
at the minimal-counterexample boundary used by the Section 13 consumer.

Source: GLS, Volume 4, Chapter 4, Lemma 3.6(d), used in Chapter 2,
Lemma 13.2.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion

open Subgroup Theory.GroupTheory
open _root_.BenderSuzuki.MatrixGroups
open BenderSuzuki.ZD.RankOneModelGeometry

/-- The uniform unitary alternative supplies the genuine local Borel used
to transport the two-point torus into the original ambient group. -/
public theorem residual_unitary_borel
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {z t u : G} {n : ℕ}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    IsBorelSubgroup (M.comap (centralizerClosure Z u).subtype) :=
  pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2

/-- GLS4, Chapter 2, Lemma 13.2 at the minimal-counterexample boundary.
For every involution of the actual pair stabilizer, construct the cyclic
subgroup and all second-centralizer clauses, with the original exponent `n`.
The earlier local centralizer and shearing results suffice together with
the supplied unitary branch; their producers retain their own source proofs. -/
public theorem secondCentralizerData_of_minimalCounterexample
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    {z t : G} {n : ℕ}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n) :
    ∀ u ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution u →
      Nonempty (SecondCentralizerData Z M z t u n) := by
  intro u huD hu
  exact secondCentralizerData_of_unitary_centralizers h.disconnected r
    hz hzM ht htM hL hlocal hshear hn hcard eL hunitary huD hu

private theorem fixed_torus_order_gt_one {n : ℕ} (hn : 2 ≤ n) :
    1 < (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  by_cases hn2 : n = 2
  · subst n
    decide
  · have hq : 8 ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ n)
    have hd : Nat.gcd 3 (2 ^ n + 1) ≤ 3 :=
      Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
    have hdpos : 0 < Nat.gcd 3 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by decide)
    have htwo : 2 ≤ (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) :=
      (Nat.le_div_iff_mul_le hdpos).mpr (by omega)
    omega

variable {E : Type*} [Field E] [Finite E]
variable (J : HermitianForm 3 E)
variable {n : ℕ} (hn : 2 ≤ n)
variable (hcard : Nat.card E = (2 ^ n) ^ 2)
variable (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

include hn hcard hfixed hJ

/-- The projective unitary fixed torus has one of the two orders used by the
source.  The subgroup itself is the literal intersection of the two Borel
pair torus with the centralizer of the outside involution. -/
public theorem unitary_projective_fixed_torus_order_disjunction
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    IsCyclic (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _) : Subgroup _) ∧
      (Nat.card (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
        centralizer ({t} : Set _) : Subgroup _) = 2 ^ n + 1 ∨
       Nat.card (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
        centralizer ({t} : Set _) : Subgroup _) = (2 ^ n + 1) / 3) := by
  obtain ⟨hcyc, hcardT⟩ := unitary_projective_fixed_torus J hn hcard hfixed hJ P t ht htB
  refine ⟨hcyc, ?_⟩
  have hdvd : Nat.gcd 3 (2 ^ n + 1) ∣ 3 := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with hg | hg
  · left
    simpa [hg] using hcardT
  · right
    simpa [hg] using hcardT

/-- Nontriviality uses the exact gcd formula, including `q = 4`.
The rounded natural-number expression `(q+1)/3` alone would not suffice. -/
public theorem unitary_projective_fixed_torus_nontrivial
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    (twoPoint (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) t ⊓
      centralizer ({t} : Set _) : Subgroup _) ≠ ⊥ := by
  have hc := (unitary_projective_fixed_torus J hn hcard hfixed hJ P t ht htB).2
  intro hb
  rw [hb, Subgroup.card_bot] at hc
  exact (ne_of_gt (fixed_torus_order_gt_one hn)) hc.symm


end BenderSuzuki.ZD.UnitaryExclusion
