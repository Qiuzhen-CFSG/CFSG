module

public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer

/-!
# The Baumann subgroup gives the full residual commutator

Let `P ∈ ℘(S)` be solvable, let `E ≤ P ≤ ES`, and let `Q` be a Sylow
2-subgroup of `E`. Suppose the Baumann subgroup `B(Q)` is normal in `S`
but not normalized by `P`. Then `[O²(P),B(Q)] = O²(P)`.

Lemma (3.4) reduces the proof to excluding `B(Q) ≤ O₂(P)`. In that case
`B(Q) ≤ O₂(P) ∩ E ≤ O₂(E) ≤ Q`. Heredity of the Baumann subgroup identifies
`B(Q)` with `B(O₂(E))`, which `E` normalizes. Together with the given
normality in `S` and `P ≤ ES`, this contradicts the normalizer hypothesis.

This isolates the application of (3.4) in the second paragraph of
Stellmacher (4.6), Journal of Algebra 190 (1997), p. 26, as transcribed in
`refs/latex/stellmacher-n-group.tex`. The caller takes `P=P*`, `Q=O₂(C)`,
and `E=O²(P*)Q`, then uses the commutator equality to put `O²(P*)` in
the normal closure of the Baumann subgroup inside `P*`.
-/

namespace Stellmacher.SectionFour

universe u

private theorem le_normalizer_twoCore
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreAmbient P : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

/-- The Baumann subgroup of the local Sylow gives the full residual commutator. -/
public theorem baumann_partner_full_commutator
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : SectionThree.Hypotheses G S)
    (P Q E B : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hE : E ≤ P) (hPS : P ≤ E ⊔ S)
    (hSyl : IsSylowSubgroupIn Q E)
    (hB : B = Q ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G))
    (hBS : B ≤ S) (hBN : (B.subgroupOf S).Normal)
    (hnot : ¬ P ≤ Subgroup.normalizer (B : Set G)) :
    ⁅twoResidualAmbient P, B⁆ = twoResidualAmbient P := by
  rcases SectionThree.lemma_three_four S h P hP B ⟨hBS, hBN⟩ hsolv with hBcore | hcomm
  · exfalso
    apply hnot
    have hBQ : B ≤ Q := hB ▸ inf_le_left
    obtain ⟨QE, hQE⟩ := hSyl
    have hQleE : Q ≤ E := by
      rw [← hQE]
      exact Subgroup.map_subtype_le _
    have hBleE : B ≤ E := hBQ.trans hQleE
    let K := twoCoreAmbient P ⊓ E
    have hKnormal : (K.subgroupOf E).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      exact (le_inf (hE.trans (le_normalizer_twoCore P)) E.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hKp : IsPGroup 2 K :=
      ((pCore_isPGroup (p := 2) (G := P)).map P.subtype).to_le inf_le_left
    have hKpE : IsPGroup 2 (K.subgroupOf E) :=
      hKp.of_equiv (Subgroup.subgroupOfEquivOfLe (show K ≤ E from inf_le_right)).symm
    have hKcore : K ≤ twoCoreAmbient E := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (show K ≤ E from inf_le_right)]
      exact Subgroup.map_mono (le_sSup ⟨hKnormal, hKpE⟩)
    have hBcoreE : B ≤ twoCoreAmbient E :=
      (le_inf hBcore hBleE).trans hKcore
    have hcoreQ : twoCoreAmbient E ≤ Q := by
      rw [← hQE]
      exact Subgroup.map_mono
        ((pCore_isPGroup (p := 2) (G := E)).le_sylow_of_normal QE)
    have hBeq : twoCoreAmbient E ⊓ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient E)) : Set G) = B := by
      rw [hB]
      exact baumann_eq_of_intermediate Q (twoCoreAmbient E) (hB ▸ hBcoreE) hcoreQ
    have hEnormal : E ≤ Subgroup.normalizer (B : Set G) := by
      rw [← hBeq]
      exact (le_normalizer_twoCore E).trans (normalizer_le_normalizer_baumann _)
    have hSnormal : S ≤ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mp hBN
    exact hPS.trans (sup_le hEnormal hSnormal)
  · exact hcomm

end Stellmacher.SectionFour
