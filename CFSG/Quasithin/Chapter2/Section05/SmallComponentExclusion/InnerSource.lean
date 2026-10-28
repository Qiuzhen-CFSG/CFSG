module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.CrossingObstruction
public import Theory.GroupTheory.InnerCoverCentralizer

/-!
# The inner-action branch of the original small-component exclusion

When S induces only inner automorphisms on K, its elements lie in K C_G(K).
For the local residual R with C_K(R)=⟨z⟩, this makes C_S(R) centralize the
four E. The four centralizer lies in E C_G(K), so it normalizes R whenever
E does. The original crossing, adjusted to centralize R, must then normalize
Q_E=O₂(N_H(E)), contradicting source 2.5.12(4).
The explicit R and crossing hypotheses are the named earlier local-residual
and characteristic-centralizer producers, retained for final assembly.
Source: Aschbacher--Smith 2.5.15(i), printed p.559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L R : Subgroup G}
  {S : Sylow 2 H} {z x : G}

/-- The inner-action alternative is impossible for the actual source crossing. -/
theorem small_component_inner_crossing_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hinner : (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G))
    (hRK : R ≤ K) (hRz : K ⊓ centralizer (R : Set G) = zpowers z)
    (hzR : K ⊓ centralizer ({z} : Set G) ≤ normalizer (R : Set G))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x ∈ centralizer (R : Set G)) : False := by
  obtain ⟨E,hES,hE,hL,hU,hr,hcore,hCE⟩ := largest_pair_four_structure_of_source
    c hG hempty hgen hb hp hUS
  let := hE
  have hEY := hES.trans inf_le_left
  have hEK := hES.trans inf_le_right
  have hzE : z ∈ centralizer (E : Set G) := by
    intro e he
    obtain ⟨a,ha,heq⟩ := c.mem_center
    rw [← heq]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨e,c.sylow_lt.le (hEY he)⟩)
  have hER : E ≤ normalizer (R : Set G) := by
    intro e he
    exact hzR ⟨hEK he,mem_centralizer_singleton_iff.mpr (hzE e he)⟩
  have hQR : (S : Subgroup H).map H.subtype ⊓ centralizer (E : Set G) ≤ normalizer (R : Set G) := by
    have hh := centralizer_inf_le_sup_of_inner_cover K ((S : Subgroup H).map H.subtype) E hEK hinner
    rw [hCE] at hh
    exact hh.trans (sup_le hER ((centralizer_le hRK).trans (Subgroup.centralizer_le_normalizer _)))
  have hCR : (S : Subgroup H).map H.subtype ⊓ centralizer (R : Set G) ≤ centralizer (E : Set G) := by
    have hh := centralizer_inf_le_sup_of_inner_cover K ((S : Subgroup H).map H.subtype) R hRK hinner
    rw [hRz] at hh
    exact hh.trans (sup_le (zpowers_le.mpr hzE) (centralizer_le hEK))
  exact crossing_four_normalizer_core_false c hG hempty hgen hb hp hUS hEY hEK hL hzE
    hQR hCR hxT hxS hxN hxR
end CFSG.Quasithin.Chapter2.Section05
