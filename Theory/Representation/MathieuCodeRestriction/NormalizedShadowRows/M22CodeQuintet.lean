module
public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The quintet marking of a rank-five M22 actor

The intrinsic Sylow catalogue has exactly one elementary subgroup of order
32 in the full native pair stabilizer. Sylow conjugacy therefore identifies
any rank-five actor with the intrinsic quintet core. Applying uniqueness to
its conjugates inside a containing two-group proves normalization.
The original Chapter 12 code pair consumes both statements at rank five.
Source: Aschbacher--Smith H.14.3(1) and 8.2.5, printed pp.397,716--717,
refs/quasithin.pdf.
-/

public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeQuintet
open M22ChapterH

private theorem eq_quintet_in_standardSylow (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hA : A ≤ CompatibleSylow.outer.toSubgroup)
    (hr : rank A = 5) : A = m22OuterQuintetKernel m22SourceSextet := by
  have hn : A ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hr; omega
  have hc : Nat.card A = 32 := by
    rw [(show IsElementaryTwo A from ⟨hn,inferInstance⟩).card_eq_two_pow_rank,hr]
    decide
  exact (intrinsic_sylow_catalogue.2.2 A).mp ⟨inferInstance,hc,hA⟩

/-- A rank-five elementary actor is conjugate to the literal intrinsic quintet core. -/
theorem quintet_marking (A : Subgroup m22PairStabilizer) [IsElementaryAbelian 2 A]
    (hr : rank A = 5) :
    ∃ g : m22PairStabilizer, A.map (MulAut.conj g).toMonoidHom =
      m22OuterQuintetKernel m22SourceSextet := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S CompatibleSylow.outer
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = CompatibleSylow.outer.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  exact ⟨g,eq_quintet_in_standardSylow (A.map (MulAut.conj g).toMonoidHom)
    (hg' ▸ Subgroup.map_mono hAS) (by rwa [rank_map_conj])⟩

/-- Every containing two-group normalizes that same rank-five actor. -/
theorem normalized_in_two_group (A P : Subgroup m22PairStabilizer) [IsElementaryAbelian 2 A]
    (hP : IsPGroup 2 P) (hAP : A ≤ P) (hr : rank A = 5) :
    P ≤ normalizer (A : Set m22PairStabilizer) := by
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S CompatibleSylow.outer
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = CompatibleSylow.outer.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have he := eq_quintet_in_standardSylow (A.map (MulAut.conj g).toMonoidHom)
    (hg' ▸ Subgroup.map_mono (hAP.trans hPS)) (by rwa [rank_map_conj])
  intro p hp
  let : IsElementaryAbelian 2 (A.map (MulAut.conj p).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  change (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj g).toMonoidHom =
    A.map (MulAut.conj g).toMonoidHom
  rw [he]
  apply eq_quintet_in_standardSylow
  · rw [←hg']
    apply Subgroup.map_mono
    rintro _ ⟨x,hx,rfl⟩
    change p*x*p⁻¹ ∈ S.toSubgroup
    exact S.toSubgroup.mul_mem (S.toSubgroup.mul_mem (hPS hp) (hPS (hAP hx)))
      (S.toSubgroup.inv_mem (hPS hp))
  · rwa [rank_map_conj,rank_map_conj]

end MathieuCode.NormalizedShadowRows.M22CodeQuintet
