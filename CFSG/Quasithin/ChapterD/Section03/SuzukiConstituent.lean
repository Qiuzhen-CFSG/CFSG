module
public import CFSG.Quasithin.ChapterD.Section03.ConstituentDrop
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Source
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting

/-!
# The Suzuki lower bound on a faithful constituent

For an irreducible binary action of a normal Suzuki group, adjoining a cubic
elementary actor produces an SQTK extension with two-group quotient. Its
generalized Fitting subgroup is the given Suzuki group. K.3.6 then forces
cubic ratio two whenever the ratio is at most two. Thus every such actor
has ratio at least two, including actors external to the Suzuki group.

Transport through the actual constituent action image combines this endpoint
with strict descent to exclude small cubic actors on a faithful irreducible
Suzuki square. This proves the component-preserving exclusion used in
D.3.7 and the original Chapter 10 seed.
Source: Aschbacher--Smith D.3.7--8, printed pp.198--199, and K.3.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem suzuki_constituent_actor_ratio
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (m : ℕ) (hm : 0 < m) (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hc : IsCubic ρ A) :
    2 ≤ actionRatio ρ A := by
  by_contra! hsmall
  let : Fact (0 < m) := ⟨hm⟩
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp L.subtype) := hi
  let := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  let H := L ⊔ A
  let N := L.subgroupOf H
  let C := A.subgroupOf H
  let eN : N ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv eN.symm
  let τ : Representation (ZMod 2) H V := ρ.comp H.subtype
  have hτ : Function.Injective τ := hf.comp H.subtype_injective
  have hirr : IsIrreducible (τ.comp N.subtype) :=
    (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective (ρ.comp L.subtype)).mpr hi
  have hquot : IsPGroup 2 (H ⧸ N) :=
    quotient_isPGroup_of_sup_eq_top C N
      ((IsElementaryAbelian.isPGroup 2 A).of_injective
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).toMonoidHom
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).injective)
      ((sup_comm C N).trans (codisjoint_subgroupOf_sup L A).eq_top)
  have hcore : pCore 2 H = ⊥ := by
    let : τ.IsIrreducible := irreducible_of_subgroup_restriction τ N hirr
    have hk := normal_p_subgroup_le_ker τ (pCore 2 H) pCore_isPGroup
    exact bot_unique (hk.trans (τ.ker_eq_bot_iff.mpr hτ).le)
  have hN : IsSQTK KnownSimple.IsKnownSimple N := (IsSQTK.equiv eN).mpr hL
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    ChapterB.QuasisimpleSource.IrreducibleBranch.sqtk_of_twoGroup_quotient
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups N hquot hN
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
    intro he
    change A.subgroupOf H = ⊥ at he
    exact hA.1 (by rw [←map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),he,Subgroup.map_bot])
  have hratio : actionRatio τ C = actionRatio ρ A := by
    unfold actionRatio
    rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right),
      rank_subgroupOf (show A ≤ H from le_sup_right)]
  have hbound : cubicRatio τ ≤ actionRatio ρ A := by
    rw [←hratio]
    exact iInf_le_of_le C (iInf_le_of_le ⟨hC,fun a ha b hb c hc' v => hc a ha b hb c hc' v⟩ le_rfl)
  have hs : ChapterK.RankOne.SourceHypotheses τ N :=
    ⟨hH,generalizedFitting_eq_of_quasisimple_two_quotient N hquot hcore,
      inferInstance,hτ,hirr,hbound.trans hsmall.le⟩
  have hZ : center N = ⊥ := by
    let : IsSimpleGroup N := (eN.trans e).isSimpleGroup
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative N (center_eq_top_iff.mp hh))
  let eQ : (N ⧸ center N) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot (G := N)).trans (eN.trans e))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,heq,_⟩ := hs.suzuki_case_of_quotient hm eQ
    (Classical.choice (inferInstance : Nonempty (Sylow 2 H)))
  rw [heq] at hbound
  exact (not_lt_of_ge hbound) hsmall
end CFSG.Quasithin.ChapterD

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The same lower bound on the literal faithful image of a constituent. -/
theorem suzuki_subspace_actor_ratio
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (m : ℕ) (hm : 0 < m) (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (U : Subrepresentation (ρ.comp L.subtype)) (hi : U.toRepresentation.IsIrreducible)
    (hf : Function.Injective U.toRepresentation)
    (C : Subgroup (subspaceActionImage ρ U.toSubmodule))
    (hC : C ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule)) :
    2 ≤ actionRatio (subspaceImageRepresentation ρ U.toSubmodule) C := by
  let f := subgroupActionHom ρ U.toSubmodule L (le_constituent_stabilizer ρ L U)
  have hfi : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg (subspaceImageRepresentation ρ U.toSubmodule) h
  let N := restrictedSubgroup ρ U.toSubmodule L
  let eN : L ≃* N := (MonoidHom.ofInjective hfi).trans
    (MulEquiv.subgroupCongr (subgroupActionHom_range ρ U.toSubmodule L _))
  let : N.Normal := Normal.map inferInstance (subspaceActionHom ρ U.toSubmodule)
    (stabilizerRepresentation ρ U.toSubmodule).asGroupHom.rangeRestrict_surjective
  have hN : IsSQTK KnownSimple.IsKnownSimple N := hL.knownSimple_of_equiv eN
  have hirr : IsIrreducible ((subspaceImageRepresentation ρ U.toSubmodule).comp N.subtype) := by
    apply (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective _).mp
    exact hi
  exact suzuki_constituent_actor_ratio (subspaceImageRepresentation ρ U.toSubmodule)
    (subspaceImageRepresentation_injective ρ U.toSubmodule) N hN hirr m hm
    (eN.symm.trans e) C hC.1 hC.2.1
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
open BenderSuzuki.MatrixGroups

/-- A faithful irreducible Suzuki square has no cubic actor of ratio at most two. -/
theorem suzuki_square_cubicRatio_gt (m : ℕ) (hm : 0 < m)
    (hS : IsSQTK KnownSimple.IsKnownSimple (SuzukiMatrixGroup m))
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) : 2 < cubicRatio ρ := by
  let : Fact (0 < m) := ⟨hm⟩
  let S := SuzukiMatrixGroup m
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  by_contra! hsmall
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hsmall
  obtain ⟨J,hJ,U,hU,_,hC,hd⟩ := square_actor_constituent_drop hZ ρ hi hf A hA
  have hnormal : J.Normal := by
    rcases hJ with rfl | rfl <;> infer_instance
  let := hnormal
  have he : Nonempty (J ≃* S) := by
    rcases hJ with rfl | rfl
    · exact ⟨{
        toFun x := x.val.1
        invFun x := ⟨(x,1),mem_top x,rfl⟩
        left_inv x := Subtype.ext (Prod.ext rfl (mem_bot.mp x.property.2).symm)
        right_inv _ := rfl
        map_mul' _ _ := rfl }⟩
    · exact ⟨{
        toFun x := x.val.2
        invFun x := ⟨(1,x),rfl,mem_top x⟩
        left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
        right_inv _ := rfl
        map_mul' _ _ := rfl }⟩
  let e : J ≃* S := he.some
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hfix : Representation.invariants (ρ.comp J.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi J hJn
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp J.subtype)
    hfix U ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
  have hb := suzuki_subspace_actor_ratio ρ J ((IsSQTK.equiv e).mpr hS)
    m hm e U hU hfaith _ hC
  exact (not_lt_of_ge hb) (hd.trans_le hsmall)
end CFSG.Quasithin.ChapterD
