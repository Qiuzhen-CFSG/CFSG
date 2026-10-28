module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuadraticBound
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918

/-!
# A placed faithful quadratic actor in the abelian plane branch

The genuine rank-two source hypotheses supply the F.9.1 setup on the original
plane and outside group. Since the plane is its distinguished seed, the
centralizer alternative in F.9.16 is immediate. The resulting actor lies in
the two-core of the original edge and acts quadratically on the literal span
quotient, with fixed codimension at most twice its binary rank.

F.9.18 makes the same actor faithful on the image of the two-residual in
H/O₂(H). When a normal C-component together with the Sylow subgroup generates
H, its perfectness identifies it with that residual and retains the same
quotient homomorphism in the faithfulness statement.

Source: Aschbacher–Smith, 14.2.13 and 14.6.12(1), printed pp.984,1031;
F.9.16(3) and F.9.18(2), printed pp.324–325.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The original edge contains a quadratic actor faithful on the residual image. -/
theorem source_rankTwo_placed_quadratic_actor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)) :
    let := hU
    ∀ a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T),
    ∃ B : Subgroup H,
      B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
      IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
        2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
        centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  intro _ a
  let := hU
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  let : IsElementaryAbelian 2 (localModule T M) := h.elementary
  have h47 : ∀ x ∈ centralizer (localModule T M : Set G),
      ⁅localModule T M,zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize (localModule T M) x := by
    intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx
  obtain ⟨B,hB,hBA,hq,hr⟩ := OriginalF916.original_witness (SourceF91.ofF91 h)
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hu hmany hcard e hab) h47 a
  exact ⟨B,hB,hBA,hq,hr,source_internal_actor_faithful_on_residual T hH.1.2 B hB⟩


/-- The same placed actor in the ratio convention used for section reductions. -/
theorem source_rankTwo_placed_quadratic_actor_ratio
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)) :
    let := hU
    ∀ a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T),
    ∃ B : Subgroup H,
      B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
      IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      actionRatio a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 ∧
      B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
        centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  intro _ a
  let := hU
  obtain ⟨B,hB,hBA,hq,hr,hf⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hu hmany hcard e hab H hH hU a
  refine ⟨B,hB,hBA,hq,?_,hf⟩
  rw [actionRatio,ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hBA.rank_pos)) (by simp)]
  exact_mod_cast hr

/-- Construct the literal span action and its placed faithful actor from source data. -/
theorem source_rankTwo_bounded_placed_action
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H),
      let := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T),
      ∃ B : Subgroup H,
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
        IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
          2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        actionRatio a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 ∧
        B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
          centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  obtain ⟨hU,a,_⟩ := source_rankTwo_quadratic_bound
    hG T hempty hM hu hmany hcard e hab H hH
  let := hU
  obtain ⟨B,hB,hBA,hq,hr,hf⟩ := source_rankTwo_placed_quadratic_actor
    hG T hempty hM hu hmany hcard e hab H hH hU a
  refine ⟨hU,a,B,hB,hBA,hq,hr,?_,hf⟩
  rw [actionRatio,ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hBA.rank_pos)) (by simp)]
  exact_mod_cast hr

omit hG hempty hM hu hmany hcard e hab in
/-- A normal C-component supplemented by the given Sylow subgroup is the
literal two-residual of the outside group. -/
theorem source_twoResidual_eq_normal_cComponent
    (H : Subgroup G) (_hTH : (T : Subgroup G) ≤ H) (K : Subgroup H)
    (hK : K.IsCComponent) (hn : K.Normal)
    (hgen : K ⊔ (T : Subgroup G).subgroupOf H = ⊤) : pResidual 2 H = K := by
  let := hn
  let := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  exact pResidual_eq_of_isPPerfect_sup K ((T : Subgroup G).subgroupOf H)
    hp T.isPGroup'.comap_subtype hgen

omit hG hempty hM hu hmany hcard e hab in
/-- Faithfulness on a normal selected C-component, using the original actor
placement and the original quotient map. -/
theorem source_placed_actor_faithful_on_normal_cComponent
    {H Y : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (B : Subgroup H)
    (hB : B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H)
    (K : Subgroup H) (hK : K.IsCComponent) (hn : K.Normal)
    (hgen : K ⊔ (T : Subgroup G).subgroupOf H = ⊤) :
    B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
      centralizer (K.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  have hf := source_internal_actor_faithful_on_residual T hTH B hB
  have hr := source_twoResidual_eq_normal_cComponent T H hTH K hK hn hgen
  rw [GenerationOne.residual,hr,actorImage_internal] at hf
  exact hf
end CFSG.Quasithin.Chapter14.Section06
