module

public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Marking
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.FourFusions
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel

/-!
# Large elementary subgroups and intrinsic cores in native M24

The literal standard octad, sextet and trio share the Sylow subgroup constructed
in `Marking`. Its two six-generator candidates are the mapped intrinsic
sextet and trio cores. The checked Sylow coverage proves that these are exactly
its elementary subgroups of order 64. The trio order needed for their
identification is supplied by `TrioAction.Kernel`.

Every elementary subgroup of order at least 32 is first conjugated into the
certified Sylow group. Coverage places it in one of six candidates; the four
additional candidates fuse into the two intrinsic cores by `FourFusions`.
Composing these native conjugators proves ambient fusion with no extra
structural premises. The earlier conditional interfaces remain available.

Source: Aschbacher–Smith, H.14.1(1,5), printed pp.396–397.
-/

public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry

/-- Both intrinsic cores are E64 subgroups of the same geometrically compatible Sylow group. -/
theorem intrinsic_core_placement (hcard : Nat.card trioCore = 64) :
    (IsElementaryAbelian 2 SextetCore.core ∧ Nat.card SextetCore.core = 64 ∧
      SextetCore.core ≤ standardSylow.toSubgroup) ∧
    (IsElementaryAbelian 2 trioCore ∧ Nat.card trioCore = 64 ∧
      trioCore ≤ standardSylow.toSubgroup) := by
  rw [← sextetCandidate_eq_core, ← trioCandidate_eq_core hcard]
  exact ⟨⟨markedCandidate_elementary 1, markedCandidate_card 1, markedCandidate_le_sylow 1⟩,
    ⟨markedCandidate_elementary 0, markedCandidate_card 0, markedCandidate_le_sylow 0⟩⟩

/-- Conjugation by two native elements agrees with conjugation by their product. -/
private theorem conj_comp (g h : M24) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Every explicitly listed additional candidate is fused into a literal source core. -/
theorem smallCandidate_fused_into_core (hcard : Nat.card trioCore = 64) (i : Fin 4) :
    ∃ g : M24,
      (smallCandidate i).map (MulAut.conj g).toMonoidHom ≤ SextetCore.core ∨
      (smallCandidate i).map (MulAut.conj g).toMonoidHom ≤ trioCore := by
  have h := Subgroup.map_mono (f := (MulAut.conj transport).toMonoidHom)
    (smallCandidate_fusion i)
  rw [Subgroup.map_map, conj_comp] at h
  change (smallCandidate i).map (MulAut.conj (transport * fusionElement i)).toMonoidHom ≤
    markedCandidate (fusionTarget i) at h
  refine ⟨transport * fusionElement i, ?_⟩
  by_cases hi : i < 2
  · rw [fusionTarget, if_pos hi, sextetCandidate_eq_core] at h
    exact Or.inl h
  · rw [fusionTarget, if_neg hi, trioCandidate_eq_core hcard] at h
    exact Or.inr h

/-- Any native Sylow subgroup is conjugate to the common geometric marking. -/
theorem exists_conjugate_standardSylow (S : Sylow 2 M24) :
    ∃ g : M24, standardSylow.toSubgroup.map (MulAut.conj g).toMonoidHom = S.toSubgroup := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 standardSylow S
  exact ⟨g, congrArg Sylow.toSubgroup hg⟩

/-- The intrinsic sextet and trio cores are exactly the E64 subgroups of the common Sylow group. -/
theorem elementary_card64_iff_eq_core (A : Subgroup M24) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 64 ∧ A ≤ standardSylow.toSubgroup) ↔
      A = SextetCore.core ∨ A = trioCore := by
  have hKT : Nat.card trioCore = 64 := TrioAction.core_ambient_card
  constructor
  · rintro ⟨hEA, hcard, hA⟩
    let B := A.map (MulAut.conj transport⁻¹).toMonoidHom
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
    have hBcard : Nat.card B = 64 :=
      (Subgroup.card_map_of_injective (MulAut.conj transport⁻¹).injective).trans hcard
    have hB : B ≤ SylowNormalizer.candidate := by
      have h := Subgroup.map_mono (f := (MulAut.conj transport⁻¹).toMonoidHom) hA
      rw [standardSylow_coe, Subgroup.map_map, conj_comp, inv_mul_cancel] at h
      change B ≤ SylowNormalizer.candidate.map (MonoidHom.id _) at h
      simpa only [Subgroup.map_id] using h
    have hback : B.map (MulAut.conj transport).toMonoidHom = A := by
      change (A.map _).map _ = A
      rw [Subgroup.map_map, conj_comp, mul_inv_cancel]
      exact Subgroup.map_id A
    rcases elementary_card64_eq_candidate B hBcard hB with h | h
    · right
      rw [← hback, h]
      exact trioCandidate_eq_core hKT
    · left
      rw [← hback, h]
      exact sextetCandidate_eq_core
  · rintro (rfl | rfl)
    · exact (intrinsic_core_placement hKT).1
    · exact (intrinsic_core_placement hKT).2

/-- Every native elementary subgroup of order at least 32 is conjugate into an intrinsic core. -/
theorem large_elementary_fused_into_core (A : Subgroup M24)
    [IsElementaryAbelian 2 A] (hcard : 32 ≤ Nat.card A) :
    ∃ g : M24, A.map (MulAut.conj g).toMonoidHom ≤ SextetCore.core ∨
      A.map (MulAut.conj g).toMonoidHom ≤ trioCore := by
  have hKT : Nat.card trioCore = 64 := TrioAction.core_ambient_card
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom =
      SylowNormalizer.candidate := congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBcard : 32 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hB : B ≤ SylowNormalizer.candidate := hg' ▸ Subgroup.map_mono hAS
  have hfused : ∃ h : M24, B.map (MulAut.conj h).toMonoidHom ≤ SextetCore.core ∨
      B.map (MulAut.conj h).toMonoidHom ≤ trioCore := by
    rcases large_elementary_le_candidate B hBcard hB with h | h | ⟨i, h⟩
    · refine ⟨transport, Or.inr ?_⟩
      rw [← trioCandidate_eq_core hKT]
      exact Subgroup.map_mono h
    · refine ⟨transport, Or.inl ?_⟩
      rw [← sextetCandidate_eq_core]
      exact Subgroup.map_mono h
    · obtain ⟨k, hk | hk⟩ := smallCandidate_fused_into_core hKT i
      · exact ⟨k, Or.inl ((Subgroup.map_mono h).trans hk)⟩
      · exact ⟨k, Or.inr ((Subgroup.map_mono h).trans hk)⟩
  obtain ⟨h, hh⟩ := hfused
  refine ⟨h * g, ?_⟩
  simpa only [B, Subgroup.map_map, conj_comp] using hh

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
