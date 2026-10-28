module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Reduction
public import Theory.GroupTheory.PCoreNormalizerAction.Residual
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The literal quotient action in the zero-kernel half-Sylow argument

Put K = <O²(H)^E> and R = N_T(L) ∩ K for the actual source parabolic
and E = <N_G(N_T(L)),H>. The original normalizer preserves R and acts
on K/O₂(K). Its action preserves the image of R; the original full Sylow,
index at most two, lower parabolic-core bound and two-residual all descend
through this same quotient map. Since O₂(K) normalizes O²(H), preservation
of the residual image lifts back to the original residual.

The last two theorems apply this lift to the two parabolics constructed from
the specified exchanger and to the literal half-join. Model-specific image
normalization is still required and stays with qt-d-10-nona5-half-sylow-unique;
these implications do not assert the completed source normalizer theorem.
Only ModuleChoiceAt is external to that owner, with its ultimate discharge
retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.5--6, printed pp.747--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- The original ambient normalizer acts on the actual normal-closure quotient. -/
def quotientAction (T : Sylow 2 G) (L H : Subgroup G) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) →*
      MulAut (XiQuotient (enlargedResidual T L H)) :=
  (pCoreNormalizerAction 2 (enlargedResidual T L H)).comp
    (inclusion (le_sup_left.trans (le_normalizer_conjugateSpanBy _ _)))

/-- The source core bound supplies precisely the kernel-normalization premise. -/
theorem Data.enlargedResidual_core_normalizes_residual (h : Data D H) :
    (enlargedResidual T L H).pCoreIn 2 ≤ normalizer (residual H : Set G) :=
  (h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans h.sylow_le))).trans
      (le_normalizer_embedded_pResidual 2 H)

/-- The quotient action preserves the image of the literal R=T₁∩K. -/
theorem Data.quotientAction_preserves_intersection (h : Data D H)
    (g : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G)) :
    (quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)).map
      (quotientAction T L H g).toMonoidHom =
        quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H) :=
  pCoreNormalizerAction_preserves_image 2 _ _ _
    (h.normalizer_normalizes_intersection g.property)

/-- Every quotient model calculation lifts to the same original X=O²(H). -/
theorem Data.normalizes_residual_of_quotientAction (h : Data D H)
    (hi : ∀ g : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G),
      (quotientImage (enlargedResidual T L H) (residual H)).map
        (quotientAction T L H g).toMonoidHom =
          quotientImage (enlargedResidual T L H) (residual H)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  intro g hg
  exact mem_normalizer_of_pCoreNormalizerAction_preserves_image
    (enlargedResidual T L H) (residual H) h.residual_le_enlargedResidual
    (isPPerfect_embedded_pResidual 2 H) h.enlargedResidual_core_normalizes_residual
    ⟨g,h.normalizer_normalizes_enlargedResidual hg⟩ (hi ⟨g,hg⟩)

/-- The original Sylow intersection descends to a full quotient Sylow. -/
theorem Data.quotient_sylow (h : Data D H) :
    ∃ S : Sylow 2 (XiQuotient (enlargedResidual T L H)),
      (S : Subgroup (XiQuotient (enlargedResidual T L H))) =
        quotientImage (enlargedResidual T L H) (T : Subgroup G) :=
  InvariantThree.component_quotient_sylow
    (SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup
      (h.sylow_le.trans (show H ≤ enlargement T L H from le_sup_right)))
    h.enlargedResidual_le_enlargement h.enlargedResidual_normal

/-- Passing to K/O₂(K) preserves the original index at most two. -/
theorem Data.quotient_intersection_index (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H)).relIndex
      (quotientImage (enlargedResidual T L H) (T : Subgroup G)) ≤ 2 := by
  let K := enlargedResidual T L H
  let R := stabilizerIntersection T L H
  have hQR : pCore 2 K ≤ R.subgroupOf K := by
    intro x hx
    exact h.enlargedResidual_core_le_intersection (mem_map_of_mem K.subtype hx)
  have hQT : pCore 2 K ≤ (T : Subgroup G).subgroupOf K :=
    hQR.trans (subgroupOf_mono K (inf_le_left.trans inf_le_left))
  change ((R.subgroupOf K).map _).relIndex (((T : Subgroup G).subgroupOf K).map _) ≤ 2
  rw [relIndex_map_map,QuotientGroup.ker_mk',sup_of_le_left hQR,sup_of_le_left hQT,
    ← relIndex_map_map_of_injective _ _ K.subtype_injective,
    map_subgroupOf_eq_of_le (show R ≤ K from inf_le_right),subgroupOf_map_subtype]
  simpa only [inf_comm K (T : Subgroup G)] using h.intersection_relIndex_le_two hn

/-- The residual of the source parabolic intersection is the original X. -/
theorem Data.parabolic_intersection_residual (h : Data D H) :
    (pResidual 2 (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H) : Subgroup G)).map
      (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).subtype = residual H :=
  embedded_pResidual_join_pGroup (residual H) ((T : Subgroup G) ⊓ enlargedResidual T L H)
    (isPPerfect_embedded_pResidual 2 H) (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans (h.sylow_le.trans (le_normalizer_embedded_pResidual 2 H)))


/-- The original residual is exactly the two-residual of the quotient parabolic. -/
theorem Data.quotient_parabolic_residual (h : Data D H) :
    (pResidual 2 (quotientImage (enlargedResidual T L H) (residual H) ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G) :
        Subgroup (XiQuotient (enlargedResidual T L H)))).map
        (quotientImage (enlargedResidual T L H) (residual H) ⊔
          quotientImage (enlargedResidual T L H) (T : Subgroup G)).subtype =
      quotientImage (enlargedResidual T L H) (residual H) := by
  let K := enlargedResidual T L H
  let X := (residual H).subgroupOf K
  let S := (T : Subgroup G).subgroupOf K
  have hp : IsPPerfect 2 X := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe h.residual_le_enlargedResidual).symm.toMonoidHom
    (subgroupOfEquivOfLe h.residual_le_enlargedResidual).symm.surjective
  have hn : S ≤ normalizer (X : Set K) := by
    rw [← subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K
      (h.sylow_le.trans (le_normalizer_embedded_pResidual 2 H))
  have he := embedded_pResidual_join_pGroup X S hp T.isPGroup'.comap_subtype hn
  have hm := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
  rw [map_embedded_pResidual,Subgroup.map_sup] at hm
  exact hm

/-- The lower bound in source (*) descends through the actual quotient map. -/
theorem Data.quotient_parabolic_core_le_intersection (h : Data D H) :
    (quotientImage (enlargedResidual T L H) (residual H) ⊔
      quotientImage (enlargedResidual T L H) (T : Subgroup G)).pCoreIn 2 ≤
        quotientImage (enlargedResidual T L H) (stabilizerIntersection T L H) := by
  let K := enlargedResidual T L H
  let B := (residual H).subgroupOf K ⊔ (T : Subgroup G).subgroupOf K
  have hB : B.map K.subtype = residual H ⊔ ((T : Subgroup G) ⊓ K) := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le h.residual_le_enlargedResidual,
      subgroupOf_map_subtype]
  have hc : B.pCoreIn 2 ≤ (stabilizerIntersection T L H).subgroupOf K := by
    apply map_le_iff_le_comap.mp
    rw [map_pCoreIn_of_injective 2 B K.subtype K.subtype_injective,hB]
    exact h.parabolic_intersection_core_le
  have hm := map_mono (f := QuotientGroup.mk' (pCore 2 K)) hc
  rw [map_pCoreIn_of_ker_isPGroup _ (by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hm
  simpa only [B,K,quotientImage,Subgroup.map_sup] using hm

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Apply quotient normalization to the two parabolics constructed from the
original zero-kernel action, retaining the specified exchanger. -/
theorem stabilizer_normalizer_of_binary_three_quotient_actions
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (himage : ∀ H : Subgroup G, Data D H →
      ∀ g : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G),
        (quotientImage (enlargedResidual T L H) (residual H)).map
          (quotientAction T L H g).toMonoidHom =
            quotientImage (enlargedResidual T L H) (residual H)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  obtain ⟨H₁,H₂,h₁,h₂,_,hgen⟩ := exists_pair D hmodel hzero hfull ht htn hcross
  exact normalizer_le_of_normalizes_pair h₁ h₂ hgen
    (h₁.normalizes_residual_of_quotientAction (himage H₁ h₁))
    (h₂.normalizes_residual_of_quotientAction (himage H₂ h₂))

/-- The same actual quotient actions feed the literal half-join consumer;
the containing-component argument is fully discharged by ModuleChoiceAt. -/
theorem halfSylowUnique_of_binary_three_quotient_actions
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (himage : ∀ H : Subgroup G, Data D H →
      ∀ g : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G),
        (quotientImage (enlargedResidual T L H) (residual H)).map
          (quotientAction T L H g).toMonoidHom =
            quotientImage (enlargedResidual T L H) (residual H)) : HalfSylowUnique D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  intro H hH hhalf
  by_contra hne
  obtain ⟨s,K₁,K₂,C⟩ := exists_containingPair D
    (stabilizer_normalizer_of_binary_three_quotient_actions D hmodel hzero hfull ht htn hcross himage)
    hn hH hne hhalf
  exact containingPairExclusionAt_of_moduleChoice hchoice hmany L D hn hna H s K₁ K₂ C

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
