module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.PointAction
public import Theory.SpecificGroups.PSL3Two.NormalExtension.Parabolic
public import Theory.GroupTheory.PCoreQuotientInnerJoin
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Full quotient recovery for the small and inner linear branches

The actual S₃ point-parabolic rules out the graph extension of a normal
PSL₃(2) component. For an inner action, conjugation identifies I/O₂(I)
with K/O₂(K), compatibly with the literal inclusion. The Sylow supplement
then factors through T intersect K and O₂(I). Consequently the marked
P = L₁(T intersect K) is T-normalized and has the same image as L₁T.

These are quotient and action steps of Aschbacher–Smith 14.7.49 and
14.7.51, printed pp.1064–1065, refs/quasithin.pdf. They do not supply
14.7.11 or the A₆ exclusion. The imported PSL₃(2) model retains its ATLAS
attribution and license, LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal component with intrinsic quotient PSL₃(2), the actual S₃
point parabolic and I = KT determines the full quotient I/O₂(I). -/
theorem linearThree_full_quotient_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hn : (K.subgroupOf I).Normal)
    (hgen : I = K ⊔ (T : Subgroup G))
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL) :
    Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) := by
  let := hn
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  let e := subgroupOfEquivOfLe hKI
  let eN := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK
  let b := subgroupOfEquivOfLe hBI
  let eB := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    (pointQuotientEquiv_at h structural)
  apply Matrix.PSL3Two.quotient_of_normal_component_and_symmetricThree_parabolic
    (K.subgroupOf I) eN (T.subtype (F.sylow_le_of_mem_Hz hI)) ?_ (B.subgroupOf I) ?_ eB
  · rw [Sylow.coe_subtype, ← subgroupOf_sup hKI (F.sylow_le_of_mem_Hz hI), ← hgen,
      subgroupOf_self]
  · exact subgroupOf_mono I (show (T : Subgroup G) ≤ B from le_sup_right)

omit [Finite G] in
/-- In the inner case the component fills the literal full core quotient. -/
theorem inner_full_image
    (K : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    (K.subgroupOf (K ⊔ (T : Subgroup G))).map
      (QuotientGroup.mk' (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G))) = ⊤ :=
  map_subgroupOf_pCoreJoin_eq_top_of_inner K T hn T.isPGroup' hz (fun t => hi t t.property)

/-- The actual Sylow supplement factors through T intersect K and the
ambient two-core, with no splitting assumption. -/
theorem inner_sylow_factor
    (K : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ K) ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  have hST : (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left
  have hh := sup_core_factor_of_inner_action K (T : Subgroup G) hn T.isPGroup' hz S
    hST (fun t => hi t t.property)
  simpa only [hS,subgroupOf_map_subtype,inf_comm] using hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
/-- The full quotient comparison induced by conjugation, with the original
intrinsic quotient on the selected component. -/
def innerQuotientEquiv (I K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    HStar I ≃* (K ⧸ pCore 2 K) := by
  subst I
  exact pCoreJoinQuotientEquivOfInner K T hn T.isPGroup' hz (fun t => hi t t.property)

omit [Finite G] in
/-- The comparison agrees with the literal inclusion and both quotient maps. -/
theorem innerQuotientEquiv_on_component (I K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) (k : K) :
    innerQuotientEquiv I K hn hgen hz hi
      (QuotientGroup.mk' (pCore 2 I) (inclusion (hgen ▸ le_sup_left) k)) =
        QuotientGroup.mk' (pCore 2 K) k := by
  subst I
  exact pCoreJoinQuotientEquivOfInner_on_component K T hn T.isPGroup' hz
    (fun t => hi t t.property) k

/-- In the inner case adjoining the ambient core to the component point
parabolic recovers the original L₁T, not just an abstract S₃ section. -/
theorem point_parabolic_core_factor (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    F.Li L 1 ⊔ (T : Subgroup G) =
      (F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)) ⊔ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  conv_lhs => rw [inner_sylow_factor K hn hz hi]
  exact (sup_assoc _ _ _).symm

/-- The original component point parabolic is Sylow normalized and has
exactly the image of L₁T in the literal ambient two-core quotient. -/
theorem inner_point_parabolic_image_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    let P := F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)
    P ≤ K ∧ (T : Subgroup G) ≤ normalizer (P : Set G) ∧
      (P.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let P := F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)
  have hPK : P ≤ K := sup_le hLK inf_le_right
  have hPI : P ≤ I := hPK.trans (hgen ▸ le_sup_left)
  have hfactor : F.Li L 1 ⊔ (T : Subgroup G) = P ⊔ I.pCoreIn 2 := by
    rw [hgen]
    exact point_parabolic_core_factor K hn hz hi
  have hcore : ((I.pCoreIn 2).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) = ⊥ := by
    change (((pCore 2 I).map I.subtype).comap I.subtype).map _ = ⊥
    rw [comap_map_eq_self_of_injective I.subtype_injective,QuotientGroup.map_mk'_self]
  refine ⟨hPK,?_,?_⟩
  · exact (le_inf (T_normalizes_L₁_at h structural)
      ((le_inf (T : Subgroup G).le_normalizer hn).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · rw [hfactor,subgroupOf_sup hPI (pCoreIn_le 2 I),Subgroup.map_sup,hcore,sup_bot_eq]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
