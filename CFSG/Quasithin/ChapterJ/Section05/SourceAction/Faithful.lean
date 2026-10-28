module
public import CFSG.Quasithin.ChapterJ.Section05.PlusStabilizer

/-!
# Faithfulness of the original J.5 coset action

The kernel intersects the simple derived Tits subgroup trivially, because
that subgroup cannot lie in a distinct conjugate of F. The kernel therefore
centralizes the derived subgroup, whose ambient centralizer is trivial by
the original Q₅ calculation. No ambient simplicity is assumed.

Source: the permutation-action assertion in Aschbacher–Smith J.5.4(3),
printed p.446, with the preceding native J.4/J.5 subgroup constructions.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] (d:LocalSetup G)

theorem source_cosets_faithful (B5:Sylow 5 d.toTypeRuSetup.H) (F:Subgroup G)
    (h5:Q₅ d B5≤F) (hB:B5Image B5≤F) (e:F≃*ReeF4.Model 0)
    {q:G} (hq:q∉F) : FaithfulSMul G (Cosets F) := by
  let N:=F.normalCore
  let D:Subgroup G:=⁅F,F⁆
  have : N.Normal := inferInstance
  have : IsSimpleGroup D := (sourceDerivedEquiv F e).isSimpleGroup
  have hN:N≤F:=F.normalCore_le
  have hi:(N⊓D).subgroupOf D=N.subgroupOf D:=by ext x; simp
  have : ((N⊓D).subgroupOf D).Normal := hi.symm ▸ (inferInstance : (N.subgroupOf D).Normal)
  have hND:N⊓D=⊥ := by
    rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup D)).2
      (N⊓D) inf_le_right inferInstance with hh | hh
    · exact hh
    · have hDN:D≤N:=hh.symm.le.trans inf_le_left
      apply False.elim (source_derived_not_le_conjugate d B5 F h5 hB e hq ?_)
      refine hDN.trans ?_
      dsimp [N]
      rw [normalCore_eq_iInf_map_conj]
      exact iInf_le _ q
  have hcom:⁅N,D⁆=⊥ := by
    apply le_bot_iff.mp
    rw [← hND]
    exact le_inf (commutator_le_left N D)
      (le_normalizer_iff_commutator_le_right.mp
        (hN.trans (normalizer_commutator_ge_left F F)))
  have hbot:N=⊥:=by
    apply le_bot_iff.mp
    rw [← source_derived_centralizer d B5 F h5 hB e]
    exact commutator_eq_bot_iff_le_centralizer.mp hcom
  have hinj:Function.Injective (MulAction.toPermHom G (Cosets F)):=by
    rw [← MonoidHom.ker_eq_bot_iff,← F.normalCore_eq_ker]
    exact hbot
  apply faithfulSMul_iff.mpr
  intro g hg
  apply hinj
  ext x
  simpa using hg x

end CFSG.Quasithin.ChapterJ.Section05
