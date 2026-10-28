module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.LocalCore.Normalization
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.SpecificGroups.SL2.BinaryProjective

/-!
# The intrinsic first two-core, quotient and residual commutator

The inner matching quotient extends across the nonsplit swap: its kernel in
the outer centralizer is the concrete order-64 subgroup. The quotient is S₃,
whose two-core is trivial. The two-residual is inner, so its commutator with
the outer core lies in the quaternion intersection; the marked cubic actor
recovers all four quaternion generators and proves equality.

These are the local core and quotient assertions used in Aschbacher--Smith,
F.1.12(I)(13), printed p.263, and 14.2.21, printed p.988. The only input is
the marked inner-model isomorphism; relative normality, the intrinsic core,
the actual quotient equivalences and the commutator equality are conclusions.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
open Subgroup
open scoped commutatorElement
set_option maxRecDepth 100000
attribute [local irreducible] leftI leftJ rightI rightJ nonsplitSwap cubicActor

/-- Restriction of the marked embedding to the original first parabolic. -/
@[expose] def innerFirstEmbedding (m : InnerModel) : M12SmallPair.firstParabolic →* firstParabolic :=
  (m.embedding.comp M12SmallPair.firstParabolic.subtype).codRestrict firstParabolic
    (fun g => by
      change g.val ∈ firstParabolic.comap m.embedding
      rw [firstParabolic_comap m]
      exact g.property)

private theorem core_preimage (m : InnerModel) (x : M12SmallPair.firstParabolic) :
    m.embedding x.val ∈ outerCore ↔ x.val ∈ M12SmallPair.core := by
  constructor
  · intro hx
    have hq : m.embedding x.val ∈ quaternionCore := by
      rw [← outerCore_inf_inner m]
      exact ⟨hx, m.embedding_range ▸ ⟨x.val,rfl⟩⟩
    rw [quaternionCore_eq_map m] at hq
    obtain ⟨y,hy,he⟩ := hq
    exact m.embedding_injective he ▸ hy
  · intro hx
    apply (show quaternionCore ≤ outerCore from le_sup_left)
    rw [quaternionCore_eq_map m]
    exact ⟨x.val,hx,rfl⟩

/-- The inner matching quotient identifies the quotient of the full outer centralizer. -/
def concreteCoreQuotient (m : InnerModel) :
    letI := outerCore_normal_firstParabolic m
    firstParabolic ⧸ outerCore.subgroupOf firstParabolic ≃* Equiv.Perm (Fin 3) := by
  let := outerCore_normal_firstParabolic m
  let O := outerCore.subgroupOf firstParabolic
  let q := QuotientGroup.mk' O
  let f := q.comp (innerFirstEmbedding m)
  have hk : f.ker = M12SmallPair.core.subgroupOf M12SmallPair.firstParabolic := by
    ext x
    rw [MonoidHom.mem_ker]
    change q (innerFirstEmbedding m x) = 1 ↔ x.val ∈ M12SmallPair.core
    rw [show q (innerFirstEmbedding m x) = 1 ↔ innerFirstEmbedding m x ∈ O from
      QuotientGroup.eq_one_iff _]
    exact core_preimage m x
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective O y
    have hs : q ⟨nonsplitSwap,nonsplitSwap_mem_firstParabolic⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ((show zpowers nonsplitSwap ≤ outerCore from le_sup_right) (mem_zpowers _))
    have hi (x : firstParabolic) (hx : x.val ∈ inner) : ∃ a, f a = q x := by
      have hm : x.val ∈ M12SmallPair.firstParabolic.map m.embedding := by
        rw [firstParabolic_inner_image m]
        exact ⟨hx,x.property⟩
      obtain ⟨a,ha,he⟩ := hm
      exact ⟨⟨a,ha⟩, congrArg q (Subtype.ext he)⟩
    by_cases hg : g.val ∈ inner
    · exact hi g hg
    · let s : firstParabolic := ⟨nonsplitSwap,nonsplitSwap_mem_firstParabolic⟩
      have hx : (g * s⁻¹).val ∈ inner :=
        (inner.mul_mem_iff_of_index_two m.index).mpr (by
          change g.val ∈ inner ↔ nonsplitSwap⁻¹ ∈ inner
          simp only [hg, inner.inv_mem_iff, nonsplitSwap_not_mem_inner])
      obtain ⟨a,ha⟩ := hi (g*s⁻¹) hx
      refine ⟨a,ha.trans ?_⟩
      rw [map_mul, map_inv, hs, inv_one, mul_one]
  exact (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      M12SmallPair.firstParabolicCoreQuotient)

/-- The published order-64 subgroup is the intrinsic two-core of the first parabolic. -/
theorem outerCore_subgroupOf_eq_pCore (m : InnerModel) :
    outerCore.subgroupOf firstParabolic = pCore 2 firstParabolic := by
  let := outerCore_normal_firstParabolic m
  let O := outerCore.subgroupOf firstParabolic
  let f := (concreteCoreQuotient m).toMonoidHom.comp (QuotientGroup.mk' O)
  have hf : Function.Surjective f :=
    (concreteCoreQuotient m).surjective.comp (QuotientGroup.mk'_surjective O)
  have hk : f.ker = O := by
    ext x
    rw [MonoidHom.mem_ker]
    change concreteCoreQuotient m (QuotientGroup.mk' O x) = 1 ↔ x ∈ O
    rw [(concreteCoreQuotient m).map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hOp : IsPGroup 2 O := (outerCore_isPGroup m).of_equiv
    (subgroupOfEquivOfLe (outerCore_le_firstParabolic m)).symm
  have hlo : O ≤ pCore 2 firstParabolic := le_sSup ⟨inferInstance,hOp⟩
  have : ((pCore 2 firstParabolic).map f).Normal := Normal.map inferInstance f hf
  have him : (pCore 2 firstParabolic).map f ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map f⟩
  apply le_antisymm hlo
  intro x hx
  have hh := him (mem_map.mpr ⟨x,hx,rfl⟩)
  rw [M12SmallPair.FirstCore.local_perm_three_core_eq_bot, mem_bot] at hh
  rw [← hk]
  exact MonoidHom.mem_ker.mpr hh

/-- Ambient form of the intrinsic two-core identification. -/
theorem mapped_pCore_eq_outerCore (m : InnerModel) :
    (pCore 2 firstParabolic).map firstParabolic.subtype = outerCore := by
  rw [← outerCore_subgroupOf_eq_pCore m]
  exact map_subgroupOf_eq_of_le (outerCore_le_firstParabolic m)

theorem card_pCore (m : InnerModel) : Nat.card (pCore 2 firstParabolic) = 64 := by
  rw [← outerCore_subgroupOf_eq_pCore m,
    Nat.card_congr (subgroupOfEquivOfLe (outerCore_le_firstParabolic m)).toEquiv]
  exact card_outerCore m

/-- An actual group equivalence, extending the original inner matching action. -/
def firstParabolicPcoreQuotient (m : InnerModel) :
    firstParabolic ⧸ pCore 2 firstParabolic ≃* Equiv.Perm (Fin 3) := by
  letI := outerCore_normal_firstParabolic m
  exact (QuotientGroup.quotientMulEquivOfEq
    (outerCore_subgroupOf_eq_pCore m).symm).trans (concreteCoreQuotient m)

/-- The source notation `L₂(2)` is realized by the actual projective matrix group. -/
def firstParabolicPcoreQuotientPSL (m : InnerModel) :
    firstParabolic ⧸ pCore 2 firstParabolic ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  (firstParabolicPcoreQuotient m).trans
    ((Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm.trans
      Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)

/-- The residual is inner because the inner intersection has two-group quotient. -/
theorem residual_le_inner (m : InnerModel) :
    (pResidual 2 firstParabolic).map firstParabolic.subtype ≤ inner := by
  let I := inner.subgroupOf firstParabolic
  let : I.Normal := normal_of_index_eq_two (inner_firstParabolic_index m)
  have hi : IsPGroup 2 (firstParabolic ⧸ I) :=
    IsPGroup.of_card (n := 1) (inner_firstParabolic_index m)
  have hr : pResidual 2 firstParabolic ≤ I := sInf_le ⟨inferInstance,hi⟩
  rintro _ ⟨x,hx,rfl⟩
  exact hr hx

/-- The marked cubic actor belongs to the actual residual of the outer parabolic. -/
theorem cubicActor_mem_residual_image (m : InnerModel) :
    cubicActor ∈ (pResidual 2 firstParabolic).map firstParabolic.subtype := by
  let c : M12SmallPair.firstParabolic :=
    ⟨M12SmallPair.cubicActor,M12SmallPair.cubicActor_mem⟩
  refine ⟨innerFirstEmbedding m c, map_pResidual_le 2 (innerFirstEmbedding m)
    ⟨c,M12SmallPair.cubicActor_residual,rfl⟩, ?_⟩
  exact map_cubicActor m.embedding m.embedding_originalA m.embedding_originalB

private theorem cubic_commutators (m : InnerModel) :
    leftI = ⁅leftJ,cubicActor⁆⁻¹ ∧ leftJ = ⁅leftJ*leftI,cubicActor⁆ ∧
    rightI = ⁅rightJ,cubicActor⁆⁻¹ ∧ rightJ = ⁅rightJ*rightI,cubicActor⁆ := by
  have h₁ : M12SmallPair.leftI = ⁅M12SmallPair.leftJ,M12SmallPair.cubicActor⁆⁻¹ := by
    decide +kernel
  have h₂ : M12SmallPair.leftJ =
      ⁅M12SmallPair.leftJ*M12SmallPair.leftI,M12SmallPair.cubicActor⁆ := by
    decide +kernel
  have h₃ : M12SmallPair.rightI = ⁅M12SmallPair.rightJ,M12SmallPair.cubicActor⁆⁻¹ := by
    decide +kernel
  have h₄ : M12SmallPair.rightJ =
      ⁅M12SmallPair.rightJ*M12SmallPair.rightI,M12SmallPair.cubicActor⁆ := by
    decide +kernel
  have hm₁ := congrArg m.embedding h₁
  have hm₂ := congrArg m.embedding h₂
  have hm₃ := congrArg m.embedding h₃
  have hm₄ := congrArg m.embedding h₄
  simp only [map_mul, map_inv, map_commutatorElement,
    map_leftI m.embedding m.embedding_originalA m.embedding_originalB,
    map_leftJ m.embedding m.embedding_originalA m.embedding_originalB,
    map_rightI m.embedding m.embedding_originalA m.embedding_originalB,
    map_rightJ m.embedding m.embedding_originalA m.embedding_originalB,
    map_cubicActor m.embedding m.embedding_originalA m.embedding_originalB] at hm₁ hm₂ hm₃ hm₄
  exact ⟨hm₁,hm₂,hm₃,hm₄⟩

/-- The concrete residual commutator is exactly the marked quaternion product. -/
theorem outerCore_commutator_residual (m : InnerModel) :
    ⁅outerCore, (pResidual 2 firstParabolic).map firstParabolic.subtype⁆ =
      quaternionCore := by
  let R := (pResidual 2 firstParabolic).map firstParabolic.subtype
  have hrH : R ≤ firstParabolic := map_subtype_le _
  apply le_antisymm
  · rw [← outerCore_inf_inner m]
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp
        (hrH.trans (firstParabolic_normalizes_outerCore m))
    · let : inner.Normal := normal_of_index_eq_two m.index
      exact (commutator_mono le_rfl (residual_le_inner m)).trans
        (commutator_le_right outerCore inner)
  · have hmarks : leftI ∈ outerCore ∧ leftJ ∈ outerCore ∧
        rightI ∈ outerCore ∧ rightJ ∈ outerCore := by
      have hq : quaternionCore ≤ outerCore := le_sup_left
      rw [quaternionCore_eq_closure] at hq
      exact ⟨hq (subset_closure (by simp)),hq (subset_closure (by simp)),
        hq (subset_closure (by simp)),hq (subset_closure (by simp))⟩
    have hc := cubicActor_mem_residual_image m
    obtain ⟨h₁,h₂,h₃,h₄⟩ := cubic_commutators m
    rw [quaternionCore_eq_closure]
    apply (closure_le _).mpr
    rintro x (rfl | rfl | rfl | rfl)
    · rw [h₁]
      exact inv_mem (commutator_mem_commutator hmarks.2.1 hc)
    · rw [h₂]
      exact commutator_mem_commutator (outerCore.mul_mem hmarks.2.1 hmarks.1) hc
    · rw [h₃]
      exact inv_mem (commutator_mem_commutator hmarks.2.2.2 hc)
    · rw [h₄]
      exact commutator_mem_commutator (outerCore.mul_mem hmarks.2.2.2 hmarks.2.2.1) hc

/-- Source `Q_K = [O₂(H), O²(H)]`, expressed as an equality of ambient subgroups. -/
theorem mapped_pCore_residual_commutator (m : InnerModel) :
    (⁅pCore 2 firstParabolic, pResidual 2 firstParabolic⁆).map
      firstParabolic.subtype = quaternionCore := by
  rw [map_commutator, mapped_pCore_eq_outerCore m]
  exact outerCore_commutator_residual m

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
