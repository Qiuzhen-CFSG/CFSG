module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Components
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient
public import Theory.GroupTheory.SylowNormalSupplementIntersection

/-!
# The canonical supplement and the escaping two-core

The commutator claim implies that Y centralizes L_R modulo its own
two-core. That core lies in the fixed Sylow, so it normalizes the perfect
L_R. Recovering L_R as the solvable residual of L_R O₂(Y) proves that Y
normalizes L_R. Relative core monotonicity gives O₂(Y)≤O₂(L_R T)=R.

The literal section-centralizer identity C_T(L_R/O∞(L_R))=R then puts
T∩Y in R. The Sylow intersection theorem in YT proves R is Sylow in YR.
This last step uses the section centralizer, not just O₂(Y)≤R.
Source: Aschbacher--Smith 13.1.9, first paragraph of printed p.870.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The consequences of the commutator claim for the actual canonical
supplement. The displayed canonical geometry is supplied independently
by the original radical Sylow and Frattini argument. -/
theorem normalizes_canonical_and_core_le
    {L H Y C : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hYH : Y ≤ H)
    (hYn : (Y.subgroupOf H).Normal)
    (hAC : canonicalSupplement T L ≤ C) (hCH : C ≤ H)
    (hTA : (T : Subgroup G) ≤ normalizer (canonicalSupplement T L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L)
    (hc : ⁅Y,C⁆ ≤ Y.pCoreIn 2) :
    Y ≤ normalizer (canonicalSupplement T L : Set G) ∧
      Y.pCoreIn 2 ≤ radicalSylowCentralizer T L := by
  let A := canonicalSupplement (T : Subgroup G) L
  let Q := Y.pCoreIn 2
  have hHY : H ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hHQ : H ≤ normalizer (Q : Set G) :=
    hHY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQH : Q ≤ H := (pCoreIn_le 2 Y).trans hYH
  have hQT : Q ≤ (T : Subgroup G) := by
    have hQcore := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQH hHQ
    have ht := pCoreIn_le_sylow H (T.subtype hTH)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at ht
    exact hQcore.trans ht
  have hAH : A ≤ H := hAC.trans hCH
  have hAQ : ⁅A,Y⁆ ≤ Q := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hAC).trans hc
  let : Group.IsPerfect A := canonicalSupplement_perfect _ _
  let : Group.IsPerfect (A.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAH).symm.surjective
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHQ
  have hnQ : Q.subgroupOf H ≤ normalizer (A.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hAH]
    exact comap_mono (hQT.trans hTA)
  have hcH : ⁅A.subgroupOf H,Y.subgroupOf H⁆ ≤ Q.subgroupOf H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hYH,
      map_subgroupOf_eq_of_le hQH]
    exact hAQ
  have hn := normalizes_perfect_of_commutator_le (A.subgroupOf H) (Q.subgroupOf H)
    (Y.subgroupOf H) (isPGroup_pCoreIn 2 Y).comap_subtype hnQ hcH
  have hYA : Y ≤ normalizer (A : Set G) := by
    rw [← subgroupOf_normalizer_eq hAH] at hn
    intro y hy
    exact hn (show (⟨y,hYH hy⟩ : H) ∈ Y.subgroupOf H from hy)
  refine ⟨hYA,?_⟩
  have hJH : A ⊔ (T : Subgroup G) ≤ H := sup_le hAH hTH
  have hQJ : Q ≤ A ⊔ (T : Subgroup G) := hQT.trans le_sup_right
  exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQJ
    (hJH.trans hHQ)).trans_eq hcore

/-- The literal section centralizer supplies the Sylow assertion in YR.
In particular this retains the extra geometry needed in the quasisimple
escaping alternative, whose quotient has even order. -/
theorem sylow_join_of_canonical_centralizer
    {L H Y C : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hYH : Y ≤ H)
    (hYn : (Y.subgroupOf H).Normal)
    (hAC : canonicalSupplement T L ≤ C) (hCH : C ≤ H)
    (hTA : (T : Subgroup G) ≤ normalizer (canonicalSupplement T L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L)
    (hcent : radicalSylowCentralizer T (canonicalSupplement T L) = radicalSylowCentralizer T L)
    (hc : ⁅Y,C⁆ ≤ Y.pCoreIn 2) :
    Y ≤ normalizer (canonicalSupplement T L : Set G) ∧
      Y.pCoreIn 2 ≤ radicalSylowCentralizer T L ∧
      IsSylowIn 2 (radicalSylowCentralizer T L) (Y ⊔ radicalSylowCentralizer T L) := by
  let A := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  have hn := normalizes_canonical_and_core_le hTH hYH hYn hAC hCH hTA hcore hc
  have hHY : H ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hTH.trans hHY
  have hTYR : (T : Subgroup G) ⊓ Y ≤ R := by
    dsimp only [R]
    rw [← hcent]
    apply (le_radicalSylowCentralizer_iff hTA).mpr
    refine ⟨inf_le_left,?_⟩
    have hm : ⁅(T : Subgroup G) ⊓ Y,A⁆ ≤ A.pCoreIn 2 :=
      le_pCoreIn_of_normalizes
        ((isPGroup_pCoreIn 2 Y).to_le ((commutator_mono inf_le_right hAC).trans hc))
        (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hTA))
        (normalizer_commutator_ge_right _ _)
    exact hm.trans (by
      apply map_mono
      let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
      exact le_solvableRadical (pCore 2 A) inferInstance inferInstance)
  have hRT : R ≤ (T : Subgroup G) := radicalSylowCentralizer_le _ _
  let J := Y ⊔ (T : Subgroup G)
  let D := Y ⊔ R
  have hDJ : D ≤ J := sup_le le_sup_left (hRT.trans le_sup_right)
  let : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  have hgen : Y.subgroupOf J ⊔ (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right) : Subgroup J) = ⊤ := by
    rw [Sylow.coe_subtype,← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_map_eq_inf_of_normal_supplement
    (Y.subgroupOf J) (D.subgroupOf J) hgen (comap_mono le_sup_left)
  have hSyl : IsSylowIn 2 ((T : Subgroup G) ⊓ D) D := by
    have hi : IsSylowIn 2
        ((T.subtype (show (T : Subgroup G) ≤ J from le_sup_right) : Subgroup J) ⊓ D.subgroupOf J)
        (D.subgroupOf J) := ⟨P,hP⟩
    have hm := Section02.IndexTwo.isSylowIn_map hi J.subtype
    simpa only [Subgroup.map_inf _ _ J.subtype J.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      map_subgroupOf_eq_of_le hDJ] using hm
  have he : (T : Subgroup G) ⊓ D = R := by
    apply le_antisymm _ (le_inf hRT le_sup_right)
    intro x hx
    have hx' : x ∈ (Y : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hRT.trans hTY)]
      exact hx.2
    obtain ⟨y,hy,r,hr,hyr⟩ := hx'
    have hyT : y ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem hx.1 ((T : Subgroup G).inv_mem (hRT hr))
      rwa [← hyr,mul_inv_cancel_right] at hh
    rw [← hyr]
    exact R.mul_mem (hTYR ⟨hyT,hy⟩) hr
  rw [he] at hSyl
  exact ⟨hn.1,hn.2,hSyl⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
