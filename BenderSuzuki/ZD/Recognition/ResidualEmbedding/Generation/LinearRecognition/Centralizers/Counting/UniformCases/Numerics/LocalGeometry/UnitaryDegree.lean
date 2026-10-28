module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry.Quotient
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.BorelRecognition

/-!
# The degree for either actual unitary cover

Strong embedding identifies the local subgroup as a Sylow normalizer. For
SU₃ its full central kernel lies in this subgroup, and the scalar projection
maps it to the corresponding PSU₃ normalizer. The quotient therefore preserves
the Borel index, giving q³+1 for both covers without discarding the center.

Source: GLS4, Chapter 4, Lemma 3.2(a–c), and Chapter 2, Lemmas 12.3, 12.8.
-/

noncomputable section
namespace BenderSuzuki.ZD.LocalGeometry
open Subgroup Theory.GroupTheory
open _root_.BenderSuzuki.MatrixGroups RankOneModelGeometry
universe u

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The scalar projection preserves the index of an actual SU₃ Borel. -/
public theorem su3_borel_index {E : Type} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hc : Nat.card E = (2 ^ n) ^ 2)
    (hf : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    {B : Subgroup J.specialSubgroup} (hb : IsBorelSubgroup B) :
    B.index = (2 ^ n) ^ 3 + 1 := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨_, P, rfl⟩ := hb
  let f := J.specialToProjective
  have hk : f.ker ≤ normalizer (P : Set J.specialSubgroup) :=
    J.specialToProjective_ker_le_center.trans (center_le_normalizer _)
  calc
    _ = ((normalizer (P : Set J.specialSubgroup)).map f).index :=
      ((normalizer (P : Set J.specialSubgroup)).index_map_eq
        J.specialToProjective_surjective hk).symm
    _ = (normalizer (P.mapSurjective J.specialToProjective_surjective :
        Set (ProjectiveSpecialUnitaryMatrixGroup J))).index :=
      congrArg Subgroup.index (P.normalizer_map_surjective f J.specialToProjective_surjective)
    _ = _ := psu3_borel_index J hn hJ hc hf
      (unitary_projective_borel J hn hc hf hJ
        (P.mapSurjective J.specialToProjective_surjective))

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
    exact ⟨e x, by simpa using hx,
      IsInvolution.map_of_injective hi e.toMonoidHom e.injective⟩

/-- The degree is the same for the projective and special unitary covers. -/
public theorem unitary_cover_index
    {H : Type u} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H)
    {B : Subgroup H} (hs : IsStronglyEmbedded B) : B.index = (2 ^ n) ^ 3 + 1 := by
  obtain ⟨E, _, _, J, hJ, hc, hf, he | he⟩ := hcover
  · obtain ⟨e⟩ := he
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv H e.toEquiv
    have hb := unitary_projective_borel_of_stronglyEmbedded J hn hc hf hJ
      (B.map e.toMonoidHom) (stronglyEmbedded_map_equiv hs e)
    exact (B.index_map_equiv e).symm.trans (psu3_borel_index J hn hJ hc hf hb)
  · obtain ⟨e⟩ := he
    have hb := unitary_special_borel_of_stronglyEmbedded J hn hc hf hJ
      (B.map e.toMonoidHom) (stronglyEmbedded_map_equiv hs e)
    exact (B.index_map_equiv e).symm.trans (su3_borel_index J hn hJ hc hf hb)

end BenderSuzuki.ZD.LocalGeometry
