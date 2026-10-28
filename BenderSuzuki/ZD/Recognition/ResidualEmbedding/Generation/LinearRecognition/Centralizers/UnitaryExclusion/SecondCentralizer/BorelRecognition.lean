module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.BorelRecognition

/-!
# The actual local unitary Borel in the Section 13 centralizer

Local strong embedding identifies `M ∩ Lᵤ` as a Borel in either actual
unitary cover. The intrinsic recognition uses the maximal Sylow normalizer
in PSU₃ and its full inverse image in SU₃. Transport through the supplied
multiplicative equivalence therefore preserves the special/projective choice
and the matrix-field and fixed-field orders.

The ambient equality uses the literal inclusion `Lᵤ → G`. The model-valued
export gives a Sylow normalizer under the same unitary witness, ready for the
torus calculation in `SecondCentralizer`. No assertion about the later
second-centralizer intersection or noninner automorphism is assumed here.

Source: GLS, Volume 4, Chapter 2, Lemma 12.4 and the opening of Section 13
before Lemma 13.2; Chapter 4, Lemma 3.2(a–c).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
open _root_.BenderSuzuki.MatrixGroups
open BenderSuzuki.ZD.RankOneModelGeometry

private theorem stronglyEmbedded_map_equiv
    {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]
    {B : Subgroup H} (hB : IsStronglyEmbedded B) (e : H ≃* K) :
    IsStronglyEmbedded (B.map e.toMonoidHom) := by
  rw [map_equiv_eq_comap_symm']
  apply hB.comap_of_injective e.symm.toMonoidHom e.symm.injective
  · intro ht
    apply hB.ne_top
    apply top_unique
    intro x _
    have hx : e x ∈ B.comap e.symm.toMonoidHom := ht ▸ mem_top _
    simpa using hx
  · obtain ⟨x, hx, hi⟩ := hB.exists_involution
    exact ⟨e x, by simpa using hx, IsInvolution.map_of_injective hi e.toMonoidHom e.injective⟩

/-- A strongly embedded subgroup of either genuine unitary cover is a
solvable Sylow two-normalizer. The cover and its field exponent are unchanged. -/
public theorem borel_of_unitaryCentralizerCover
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H)
    (B : Subgroup H) (hB : IsStronglyEmbedded B) : IsBorelSubgroup B := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hcover
  · obtain ⟨e⟩ := he
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv H e.toEquiv
    have hb := unitary_projective_borel_of_stronglyEmbedded J hn hcard hfixed hJ
      (B.map e.toMonoidHom) (stronglyEmbedded_map_equiv hB e)
    have heB : (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
      ext x
      simp
    exact heB ▸ hb.map_mulEquiv e.symm
  · obtain ⟨e⟩ := he
    have hb := unitary_special_borel_of_stronglyEmbedded J hn hcard hfixed hJ
      (B.map e.toMonoidHom) (stronglyEmbedded_map_equiv hB e)
    have heB : (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
      ext x
      simp
    exact heB ▸ hb.map_mulEquiv e.symm

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {t u : G} {n : ℕ}

/-- The literal intersection `M ∩ Lᵤ`, viewed inside `Lᵤ`, is the Borel
needed for the torus construction preceding GLS4, Chapter 2, Lemma 13.2.
Strong embedding is derived in the proper local group, not imposed on `M`. -/
public theorem pair_involution_unitary_borel
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n (centralizerClosure Z u)) :
    IsBorelSubgroup (M.comap (centralizerClosure Z u).subtype) :=
  borel_of_unitaryCentralizerCover hn hcover _
    (pair_involution_centralizerClosure_local h r htM huD hu).2.2

/-- The same Borel identification as an equality of literal ambient
subgroups, using the inclusion of the distinguished centralizer. -/
public theorem pair_involution_unitary_borel_intersection
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n (centralizerClosure Z u)) :
    ∃ P : Sylow 2 (centralizerClosure Z u),
      (normalizer (P : Set (centralizerClosure Z u))).map
        (centralizerClosure Z u).subtype = M ⊓ centralizerClosure Z u := by
  obtain ⟨_, P, hP⟩ := pair_involution_unitary_borel h r htM huD hu hn hcover
  refine ⟨P, ?_⟩
  change (normalizer ((P : Subgroup (centralizerClosure Z u)) :
    Set (centralizerClosure Z u))).map (centralizerClosure Z u).subtype = _
  rw [← hP, map_comap_eq, range_subtype, inf_comm]

/-- Recognition with the actual matrix isomorphism and Sylow subgroup.
Both original cover alternatives, the matrix-field order and fixed-field
order are retained for the ambient torus transport. -/
public theorem pair_involution_unitary_borel_models
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (htM : t ∉ M) (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u) (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n (centralizerClosure Z u)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
      Nat.card E = (2 ^ n) ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      ((∃ e : centralizerClosure Z u ≃* ProjectiveSpecialUnitaryMatrixGroup J,
          ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
          (M.comap (centralizerClosure Z u).subtype).map e.toMonoidHom =
            normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∨
       (∃ e : centralizerClosure Z u ≃* J.specialSubgroup,
          ∃ P : Sylow 2 J.specialSubgroup,
          (M.comap (centralizerClosure Z u).subtype).map e.toMonoidHom =
            normalizer (P : Set J.specialSubgroup))) := by
  have hb := pair_involution_unitary_borel h r htM huD hu hn hcover
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hcover
  · obtain ⟨e⟩ := he
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv (centralizerClosure Z u) e.toEquiv
    exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      Or.inl ⟨e, (hb.map_mulEquiv e).2⟩⟩
  · obtain ⟨e⟩ := he
    exact ⟨E, inferInstance, inferInstance, J, hJ, hcard, hfixed,
      Or.inr ⟨e, (hb.map_mulEquiv e).2⟩⟩

end BenderSuzuki.ZD.UnitaryExclusion
