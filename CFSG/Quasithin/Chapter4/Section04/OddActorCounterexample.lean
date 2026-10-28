module
public import CFSG.Quasithin.Chapter4.Section01.CoreContainment
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.PResidual.PerfectLift
public import Theory.GroupTheory.SolvableResidual
import Mathlib.Tactic

/-!
# The actual odd-actor residual in a maximal pushing-up counterexample

The original chosen-module and odd-actor hypotheses construct eta and a
maximal counterexample J above LB, with an outside maximal two-local H.
The same chosen V stays in O2(J), whose section-centralizer containment is
proved by4.1.4(1). Residual covering then produces the actual normal
LH=(L intersect H)^infinity, proves L=LH O2(L), and places V=[V,LH] inside LH.
The quasisimple quotient proves that this perfect residual equals O^2(L
intersect H); these residuals are not silently identified.

This is an entry to4.2.12 and the C.4.8 analysis, not a uniqueness theorem.
No equality with the full module [R2(LT),L], exceptional model row, or
rank-three flag alignment is assumed or asserted.
Source: Aschbacher--Smith,4.2.12--13 and4.4.5--6, printed pp.610--612,620.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] : IsPPerfect 2 E := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (E ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (E ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem residual_perfect_of_surjective_twoGroup_kernel
    {E Q : Type*} [Group E] [Finite E] [Group Q] [Finite Q] [Group.IsPerfect Q]
    (f : E →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Group.IsPerfect (pResidual 2 E) := by
  let R := pResidual 2 E
  let g := f.comp R.subtype
  have hg : Function.Surjective g := by
    have hm : R.map f = ⊤ := by
      rw [map_pResidual_of_surjective 2 f hf]
      exact (pResidual_eq_top_iff 2 Q).mpr perfect_twoPerfect
    intro q
    obtain ⟨x,hx,hxq⟩ := show q ∈ R.map f from hm.symm ▸ mem_top q
    exact ⟨⟨x,hx⟩,hxq⟩
  let j : g.ker →* f.ker :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : f.ker => x.val) hab))
  exact (isPPerfect_pResidual (G := E) 2).isPerfect_of_surjective_pGroup_kernel
    g hg (hk.of_injective j hj)

/-- For the original quasisimple quotient, the intersection's two-residual
is its perfect residual. This identifies the literal LH used in4.2.12. -/
theorem chosen_intersection_twoResidual_eq_solvableResidual
    {K : GroupClass} {T : Sylow 2 G} {L J H : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G))
    (hJH : J ≤ H) :
    pResidual 2 (L ⊓ H : Subgroup G) = solvableResidual (L ⊓ H : Subgroup G) := by
  let := h.quasisimple
  let f : (L ⊓ H : Subgroup G) →* L ⧸ pCore 2 L :=
    (QuotientGroup.mk' (pCore 2 L)).comp (inclusion inf_le_left)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    obtain ⟨j,hj,c,hc,he⟩ := hcover l.property
    have hjL : j ∈ L := by
      have hjc : j = l.val * c⁻¹ := by rw [← he]; simp
      rw [hjc]
      exact L.mul_mem l.property (L.inv_mem (pCoreIn_le 2 L hc))
    refine ⟨⟨j,hjL,hJH hj⟩,?_⟩
    apply QuotientGroup.eq.mpr
    obtain ⟨c',hc',hc'eq⟩ := hc
    have hec : (⟨j,hjL⟩ : L)⁻¹ * l = c' := by
      apply Subtype.ext
      change j⁻¹ * l.val = c'.val
      rw [← he, ← hc'eq]
      simp only [Subgroup.subtype_apply]
      group
    change (⟨j,hjL⟩ : L)⁻¹ * l ∈ pCore 2 L
    rwa [hec]
  let j : f.ker →* pCore 2 L :=
    { toFun := fun x => ⟨⟨x.val.val,x.val.property.1⟩,
        (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : pCore 2 L => x.val.val) hab))
  let : Group.IsPerfect (pResidual 2 (L ⊓ H : Subgroup G)) :=
    residual_perfect_of_surjective_twoGroup_kernel f hf (pCore_isPGroup.of_injective j hj)
  apply le_antisymm (le_solvableResidual_of_isPerfect _)
  let : Group.IsNilpotent ((L ⊓ H : Subgroup G) ⧸ pResidual 2 (L ⊓ H : Subgroup G)) :=
    (isPGroup_quotient_pResidual (G := (L ⊓ H : Subgroup G)) 2).isNilpotent
  exact solvableResidual_le_of_solvable_quotient _

/-- Failure of uniqueness for the actual L_B supplies the original maximal
pushing-up pair. The chosen V remains inside its actual two-core. -/
theorem chosen_oddActorResidual_maximal_counterexample
    {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup G) (hBN : B ≤ normalizer (L : Set G))
    (hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L B) (normalizer (L : Set G))) :
    ∃ J H : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L B)) ∧
      PushLE L (oddActorResidual L B) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
      IsSQTK K H ∧ V ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L := by
  obtain ⟨hcover,_,hV,hne⟩ := chosen_oddActorResidual_cover h D B hBN hcomm hodd hBV
  have hI := ((oddActorResidual_le L B).trans inf_le_left).trans L.le_normalizer
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hI hcover.subset hne
  obtain ⟨J,H,hJ,hIJ,hH,hJH,hHM,hSQ⟩ := maximal_counterexample_of_component_cover
    h.simpleQTKE hM.1 L.le_normalizer le_rfl hI hcover.subset hne hnot
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hNL : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  exact ⟨J,H,hJ,hIJ,hH,hJH,hHM,hSQ,hV.trans hIJ.1,
    core_le_sectionCentralizer_of_eta L.le_normalizer hNL perfect_twoPerfect hs.1 hJ.1.1⟩

/-- The same actual counterexample has a normal covering residual in H∩N(L),
and the chosen module lies in that residual and is generated by its action.
This proves the residual/module part of the source setup without identifying
V with the full module [R2(LT),L]. -/
theorem chosen_oddActorResidual_counterexample_residual
    {K : GroupClass} {T : Sylow 2 G} {L V J H : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G))
    (hJH : J ≤ H) (hVJ : V ≤ J.pCoreIn 2) :
    let LH := (pResidual 2 (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
      LH ≤ H ⊓ normalizer (L : Set G) ∧
      (LH.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
      V = ⁅V,LH⁆ ∧ V ≤ LH := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hNL : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  obtain ⟨hc,hLH,hN⟩ := residual_cover_of_containment L.le_normalizer hNL
    perfect_twoPerfect hcover hJH
  have hQLT : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hQV : L.pCoreIn 2 ≤ centralizer (V : Set G) := hQLT.trans D.core_centralizes
  have he := D.eq_commutator.trans
    (commutator_eq_of_product_centralizing_factor hc (le_centralizer_iff.mp hQV))
  have hVH : V ≤ H ⊓ normalizer (L : Set G) :=
    le_inf ((hVJ.trans (pCoreIn_le 2 J)).trans hJH)
      (D.le_component.trans L.le_normalizer)
  have hn := hVH.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hN)
  exact ⟨hc,hLH,hN,he,he ▸ le_normalizer_iff_commutator_le_right.mp hn⟩
/-- The complete verified entry to the unitary source analysis, on the original
odd-actor residual and chosen module. Classification of this actual outside
pair is the remaining4.2.12/C.4.8 obligation. -/
theorem chosen_oddActorResidual_source_counterexample
    {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup G) (hBN : B ≤ normalizer (L : Set G))
    (hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L B) (normalizer (L : Set G))) :
    ∃ J H : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L B)) ∧
      PushLE L (oddActorResidual L B) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧ ¬ H ≤ normalizer (L : Set G) ∧
      IsSQTK K H ∧ V ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      (L : Set G) = (LH : Set G) * (L.pCoreIn 2 : Set G) ∧
        LH ≤ H ⊓ normalizer (L : Set G) ∧
        (LH.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
        V = ⁅V,LH⁆ ∧ V ≤ LH := by
  obtain ⟨J,H,hJ,hIJ,hH,hJH,hHM,hSQ,hVJ,hJC⟩ :=
    chosen_oddActorResidual_maximal_counterexample h D B hBN hcomm hodd hBV hM hnot
  refine ⟨J,H,hJ,hIJ,hH,hJH,hHM,hSQ,hVJ,hJC,?_⟩
  have hr := chosen_intersection_twoResidual_eq_solvableResidual h hJ.1.1.2.2.1 hJH
  simpa only [hr] using
    chosen_oddActorResidual_counterexample_residual h D hJ.1.1.2.2.1 hJH hVJ
end CFSG.Quasithin.Chapter4.Section04
