module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Cubic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The rank-one contradiction on the original local join

The perpendicular four-space is central in Q and is moved by the marked
cubic in J. Relative normality first puts it in J. Since Q is Sylow in JQ
and JQ has characteristic two, this four-space lies in O₂(JQ), hence in
O₂(J). Its cubic commutator then lies in the literal U(J). Restricting the
Sylow of JQ to its normal subgroup J constructs the Sylow required by the
proved L₂(4) endpoint, with the original coordinate and conjugation maps.

Source: Aschbacher--Smith 13.3.12, printed p.890, final paragraph of the
nondegenerate-plane argument. Selection and recognition of J remain earlier
source obligations; no perpendicular placement is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

theorem not_rankOne_of_source_join
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (n : normalizer (V : Set G))
    (hn : f (V.normalizerMonoidHom.rangeRestrict n) = cubic)
    (J Q : Subgroup G) (hJ : ChapterC.IsL2EvenBlock J 2)
    (hnJ : n.val ∈ J) (hQN : Q ≤ normalizer (J : Set G))
    (hQ : Chapter1.IsSylowIn 2 Q (J ⊔ Q))
    (hchar : centralizer (pCore 2 (J ⊔ Q : Subgroup G) : Set (J ⊔ Q : Subgroup G)) ≤
      pCore 2 (J ⊔ Q : Subgroup G))
    (hEQ : perpendicular E ≤ (center Q).map Q.subtype) : False := by
  let D := J ⊔ Q
  have hJD : J ≤ D := le_sup_left
  have hQD : Q ≤ D := le_sup_right
  have hEQ' : perpendicular E ≤ Q := hEQ.trans (map_subtype_le _)
  have hEC : perpendicular E ≤ centralizer (Q : Set G) := by
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hEQ hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y,hy⟩)
  have hm := perpendicular_commutator f E he n hn
  have hEJ : perpendicular E ≤ J := by
    rw [←hm,commutator_comm]
    exact (commutator_mono le_rfl (zpowers_le.mpr hnJ)).trans
      (le_normalizer_iff_commutator_le_right.mp (hEQ'.trans hQN))
  obtain ⟨S,hS⟩ := hQ
  have hcoreQ : D.pCoreIn 2 ≤ Q := hS ▸ pCoreIn_le_sylow D S
  have hEcore : perpendicular E ≤ D.pCoreIn 2 := by
    intro x hx
    refine ⟨⟨x,hQD (hEQ' hx)⟩,hchar ?_,rfl⟩
    intro y hy
    exact Subtype.ext (hEC hx y.val (hcoreQ (mem_map_of_mem D.subtype hy)))
  have hEcoreJ : perpendicular E ≤ J.pCoreIn 2 :=
    (le_inf hEJ hEcore).trans (inf_pCoreIn_le_of_le 2 hJD)
  have hU : (perpendicular E).subgroupOf J ≤ ChapterC.blockU J := by
    have hu : perpendicular E ≤ (ChapterC.blockU J).map J.subtype := by
      rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,
        ←hm,commutator_comm]
      exact commutator_mono hEcoreJ (zpowers_le.mpr hnJ)
    intro x hx
    obtain ⟨y,hy,hyx⟩ := hu hx
    exact (Subtype.ext hyx : y=x) ▸ hy
  let _ : (J.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le J.le_normalizer hQN)
  obtain ⟨P',hP'⟩ := S.exists_subgroupOf_eq_of_normal (J.subgroupOf D)
  let eJ := subgroupOfEquivOfLe hJD
  let P : Sylow 2 J := P'.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hPQ : (P : Subgroup J).map J.subtype ≤ Q := by
    rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
    have hzS : z.val ∈ S := by
      change z ∈ (S : Subgroup D).subgroupOf (J.subgroupOf D)
      rw [←hP']
      exact hz
    exact hS ▸ mem_map_of_mem D.subtype hzS
  exact not_rankOne_of_perpendicular f E he n hn J hJ hEJ hnJ P hU
    (hEC.trans (centralizer_le hPQ))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
