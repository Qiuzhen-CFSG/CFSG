module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRank.Native
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeTorus

/-!
# Sextet marking and normalization of the code near-offender

Of the two native rank-six elementary cores, the trio core fixes only two
code dimensions. A rank-six near-offender therefore equals the sextet core
in every Sylow group containing it. Applying this to conjugates inside a
two-group proves normalization, retaining the full original actor.
Source: Aschbacher--Smith H.14.1, H.16.5 and 8.2.5, printed pp.396,404,717.
-/
public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.CodeRank

private theorem trio_code_fixed_dimension :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation trioCore) = 2 := by
  have hd := fixedCodim_map_equivariant codeRepresentation cocodeRepresentation.dual
    (MonoidHom.id M24) codeDuality.toLinearEquiv
    (fun g x => LinearMap.congr_fun (codeDuality.isIntertwining' g) x) trioCore
  rw [Subgroup.map_id,fixedCodim_dual_eq_moved_finrank] at hd
  have ht : trioCore =
      (pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype := rfl
  rw [ht,← TrioCalculation.standard_pairSpace_eq_twoCore_commutator,TrioCalculation.finrank_pairSpace] at hd
  rw [← ht] at hd
  have hs := fixedCodim_add_finrank codeRepresentation trioCore
  rw [hd,finrank_code] at hs
  omega

private theorem eq_sextet_in_standardSylow (A : Subgroup M24)
    [IsElementaryAbelian 2 A] (hA : A ≤ standardSylow.toSubgroup)
    (hr : rank A = 6) (hnear : fixedCodim codeRepresentation A ≤ 7) : A = SextetCore.core := by
  have hn : A ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hr; omega
  have hc : Nat.card A = 64 := by
    rw [(show IsElementaryTwo A from ⟨hn,inferInstance⟩).card_eq_two_pow_rank,hr]
    decide
  rcases (elementary_card64_iff_eq_core A).mp ⟨inferInstance,hc,hA⟩ with hs | ht
  · exact hs
  · have hf := fixedCodim_add_finrank codeRepresentation A
    rw [ht,trio_code_fixed_dimension,finrank_code] at hf
    rw [ht] at hnear
    omega

/-- The actual rank-six code near-offender has a native sextet marking. -/
theorem sextet_marking (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hr : rank A = 6) (hnear : fixedCodim codeRepresentation A ≤ 7) :
    ∃ g : M24, A.map (MulAut.conj g).toMonoidHom = SextetCore.core := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S standardSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = standardSylow.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  exact ⟨g,eq_sextet_in_standardSylow (A.map (MulAut.conj g).toMonoidHom)
    (hg' ▸ Subgroup.map_mono hAS) (by rwa [rank_map_conj]) (by rwa [fixedCodim_map_conj])⟩

/-- Every two-group containing the rank-six code near-offender normalizes it. -/
theorem normalized_in_two_group (A P : Subgroup M24) [IsElementaryAbelian 2 A]
    (hP : IsPGroup 2 P) (hAP : A ≤ P)
    (hr : rank A = 6) (hnear : fixedCodim codeRepresentation A ≤ 7) :
    P ≤ normalizer (A : Set M24) := by
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S standardSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = standardSylow.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have he := eq_sextet_in_standardSylow (A.map (MulAut.conj g).toMonoidHom)
    (hg' ▸ Subgroup.map_mono (hAP.trans hPS))
    (by rwa [rank_map_conj]) (by rwa [fixedCodim_map_conj])
  intro p hp
  let : IsElementaryAbelian 2 (A.map (MulAut.conj p).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  change (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom =
    A.map (MulAut.conj g).toMonoidHom
  rw [he]
  apply eq_sextet_in_standardSylow
  · rw [← hg']
    apply Subgroup.map_mono
    rintro _ ⟨x,hx,rfl⟩
    change p * x * p⁻¹ ∈ S.toSubgroup
    exact S.toSubgroup.mul_mem (S.toSubgroup.mul_mem (hPS hp) (hPS (hAP hx)))
      (S.toSubgroup.inv_mem (hPS hp))
  · rwa [rank_map_conj,rank_map_conj]
  · rwa [fixedCodim_map_conj,fixedCodim_map_conj]

end MathieuCode.NormalizedShadowRows.CodeRank
