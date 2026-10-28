module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration

/-!
# Commutator detection from an escaping two-subgroup

A local two-subgroup escaping O₂ detects the full component action on every
normal quotient of O₂ on which O₂ is abelian. Its image in the action kernel
contains the quasisimple component by normal-subgroup generation. This works
with an odd central cover as well as a simple component, and requires no
faithful action of the original quotient.

Source: MS93 (3.6), first paragraph, printed p.870. It supplies the
non-Frattini comparison step while preserving the actual central kernel.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An escaping two-subgroup detects the whole commutator with the component. -/
theorem commutator_le_of_quasisimple_two_escape
    (K R N E : Subgroup G) [K.Normal] [N.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hR : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (hE : IsPGroup 2 E) (hne : ¬ E ≤ pCore 2 G)
    (hQQ : ⁅pCore 2 G,pCore 2 G⁆ ≤ N)
    (hQE : ⁅pCore 2 G,E⁆ ≤ N) : ⁅pCore 2 G,K⁆ ≤ N := by
  let π := QuotientGroup.mk' N
  let C := (centralizer ((pCore 2 G).map π : Set (G ⧸ N))).comap π
  have hc (A : Subgroup G) : A ≤ C ↔ ⁅pCore 2 G,A⁆ ≤ N := by
    change A ≤ (centralizer ((pCore 2 G).map π : Set (G ⧸ N))).comap π ↔ _
    rw [← map_le_iff_le_comap, ← le_centralizer_iff,
      ← commutator_eq_bot_iff_le_centralizer, ← map_commutator,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  let : ((pCore 2 G).map π).Normal :=
    Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hQC : pCore 2 G ≤ C := (hc _).mpr hQQ
  have hEC : E ≤ C := (hc E).mpr hQE
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let B := K.map q
  let D := C.map q
  let : B.Normal := Normal.map inferInstance q hq
  let : D.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (R.map q) (hR.map q) (by
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq])
  obtain ⟨x,hxE,hxQ⟩ := Set.not_subset.mp hne
  have hBD : B ≤ D := quasisimple_le_normal_of_two_escape B D (E.map q)
    hquot (pCore_quotient_pCore_eq_bot 2) (hE.map q) (q x)
    (mem_map_of_mem q hxE) (mem_map_of_mem q (hEC hxE))
    (fun he => hxQ ((QuotientGroup.eq_one_iff x).mp he))
  apply (hc K).mp
  have hh := map_le_iff_le_comap.mp hBD
  simpa only [D,comap_map_eq,q,QuotientGroup.ker_mk',sup_of_le_left hQC] using hh

end Theory.GroupTheory
