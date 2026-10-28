module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.SectionCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BlockTransport
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# The outside normal-residual block in 12.1.1

For a normal point residual, the section centralizer Y is normal in the
ambient point centralizer. Characteristic two therefore descends to Y.
The original Q is Sylow in Y, and its characteristic normalizers lie in M;
C.1.29 supplies an outside χ₀ block moved by J(Q). Transport retains
subnormality relative to the point centralizer, not the full ambient group.
Uniqueness for LT also discharges the literal C.5.2 common-normal condition.

The block-type exclusions remain with qt-d-double-natural-centralizers;
qt-d-1222-double-natural owns the final source assembly.
Source: Aschbacher--Smith, 12.1.1, printed pp.788--789, using C.1.29.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Characteristic two descends to the actual normal section centralizer. -/
theorem doubleNatural_normal_sectionCentralizer_characteristic
    {n : ℕ} (B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G))
    (hc : generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w))
    (hn : ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal) :
    generalizedFitting (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) =
      pCore 2 (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)) := by
  let H := B.pointCentralizer w
  let Y := sectionCentralizerIn H (B.pointResidual w)
  have hYH : Y ≤ H := inf_le_left
  have hHY : H ≤ normalizer (Y : Set G) := sectionCentralizerIn_normalized
    ((normal_subgroupOf_iff_le_normalizer ((B.pointResidual_le w).trans inf_le_right)).mp hn)
  let : (Y.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHY
  have hF := generalizedFitting_eq_pCore_of_normalized_by_pCore (Y.subgroupOf H) hc
    le_normalizer_of_normal
  let e := subgroupOfEquivOfLe hYH
  have he := congrArg (map e.toMonoidHom) hF
  rwa [map_generalizedFitting_equiv,pCore_map_iso] at he

/-- Uniqueness for LT rules out every nontrivial common normal subgroup of Q. -/
theorem doubleNatural_outside_no_common_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (K P N : Subgroup G) (hout : ¬ K ≤ normalizer (L : Set G))
    (hN : N ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hn : (N.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ (K ⊔ P))).Normal) : N = ⊥ := by
  by_contra hne
  have hNjoin : N ≤ L ⊔ (T : Subgroup G) := hN.trans (pCoreIn_le _ _)
  have hnorm := (normal_subgroupOf_iff_le_normalizer (hNjoin.trans le_sup_left)).mp hn
  exact hout ((le_sup_left.trans (le_sup_right.trans hnorm)).trans
    (D.normal_subgroup_normalizer_le h.toHypothesis1221 hNjoin hne
      (le_sup_left.trans hnorm)))


/-- An escaping normal-residual centralizer supplies the source χ₀ obstruction,
including Thompson movement and the C.5.2 common-normal exclusion. -/
theorem doubleNatural_adapted_normal_outside_chiZero
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Y := sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)
      ∃ K : Subgroup G, K ≤ Y ∧ IsChiZeroBlockIn (K.subgroupOf Y) ∧
        IsChiZeroBlockIn (K.subgroupOf (B.pointCentralizer w)) ∧
        ¬ K ≤ normalizer (L : Set G) ∧
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ ∧
        ∀ N : Subgroup G, N ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          (N.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ (K ⊔ B.pointSylow w))).Normal → N = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn hout
  let H := B.pointCentralizer w
  let Y := sectionCentralizerIn H (B.pointResidual w)
  let M := (normalizer (L : Set G)).subgroupOf Y
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hYH : Y ≤ H := inf_le_left
  have hHY : H ≤ normalizer (Y : Set G) := sectionCentralizerIn_normalized
    ((normal_subgroupOf_iff_le_normalizer ((B.pointResidual_le w).trans inf_le_right)).mp hn)
  let : (Y.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHY
  have hYout := D.doubleNatural_adapted_normal_sectionCentralizer_outside h B S w hw hn hout
  have hM : M ≠ ⊤ := by
    intro he
    apply hYout
    intro y hy
    exact (show (⟨y,hy⟩ : Y) ∈ M from he.symm ▸ mem_top _)
  have hH : IsSQTK KnownSimple.IsKnownSimple H := h.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (D.doubleNatural_point_orderOf_two h B w hw.nonsingular))
  let j := inclusion hYH
  have hY : IsSQTK KnownSimple.IsKnownSimple Y :=
    ⟨hH.stronglyQuasithin.of_injective j (inclusion_injective hYH),
      hH.isKGroup.of_injective j (inclusion_injective hYH)⟩
  obtain ⟨P,hP⟩ := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  have hQY : Q ≤ Y := by
    calc
      Q = (P : Subgroup Y).map Y.subtype := hP.symm
      _ ≤ Y := map_subtype_le _
  have heP : (P : Subgroup Y) = Q.subgroupOf Y := by
    apply map_injective Y.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hQY]
  have hcontrol : (P : Subgroup Y).characteristicNormalizerClosure ≤ M := by
    rw [heP]
    exact characteristicNormalizerClosure_subgroupOf_le hQY
      (D.doubleNatural_core_characteristicNormalizerClosure h)
  obtain ⟨r,_,F,hF,houtF,hmove,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple hY
      (doubleNatural_normal_sectionCentralizer_characteristic B w hc hn) P M hcontrol
  have hr : r ≠ 0 := by
    intro he
    subst r
    apply hM
    apply top_unique
    intro y _
    obtain ⟨m,b,hmb⟩ := hprod y
    have hy : y = (m : Y) := by simpa only [List.ofFn_zero,List.prod_nil,mul_one] using hmb
    exact hy.symm ▸ m.property
  let i : Fin r := ⟨0,Nat.pos_of_ne_zero hr⟩
  let K := (F i).map Y.subtype
  have hK : K.subgroupOf Y = F i := comap_map_eq_self_of_injective Y.subtype_injective _
  have hJ : j.range.IsSubnormal := by
    rw [inclusion_range]
    exact (inferInstance : (Y.subgroupOf H).Normal).isSubnormal
  have hmap : (F i).map j = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hYH),map_map]
    rfl
  refine ⟨K,map_subtype_le _,hK.symm ▸ hF i,?_,?_,?_,?_⟩
  · rw [←hmap]
    exact Section05.BlockAnalysis.chiZero_map j (inclusion_injective hYH) hJ (hF i)
  · intro hKM
    apply houtF i
    intro k hk
    exact hKM (mem_map_of_mem Y.subtype hk)
  · have hm := congrArg (map Y.subtype) (hmove i)
    rwa [map_commutator,←elementaryAbelianMaxJ_map_injective Y.subtype Y.subtype_injective,hP] at hm

  · intro N hN hnN
    apply D.doubleNatural_outside_no_common_normal h K (B.pointSylow w) N _ hN hnN
    intro hKM
    apply houtF i
    intro k hk
    exact hKM (mem_map_of_mem Y.subtype hk)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
