module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import Theory.GroupTheory.CComponent.OrdinaryProjection
public import Theory.GroupTheory.PerfectNormalizerInner

/-!
# Original A₅-block inputs for ordinary-component placement

Normality of the given block identifies its M-span with itself. The A₅
cohomology splitting of the actual radical gives [R,L] ≤ V, and the block
module has no fixed summand, hence is irreducible in the ambient group.
Genuine Theorems A and C supply solvability of the outer automorphism group
of each original ordinary component, including its central covering kernel.
Source: Aschbacher–Smith C.3.2–3, printed p.149, in the A₅ case of 4.3.2.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

omit [Finite G] in
theorem normalized_span_eq (_h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : M ≤ normalizer (L : Set G)) : conjugateSpanBy L M = L :=
  le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy L M)

theorem normalized_radical_eq_module_sup_centralizer
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : M ≤ normalizer (L : Set G)) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = V) :
    R = V ⊔ (R ⊓ centralizer (L : Set G)) := by
  have he := h.normalized_span_eq hn
  have hLR : L ≤ normalizer (R : Set G) := he ▸ h.span_normalizes_radical
  have hUR : (blockU L).map L.subtype ≤ R := by
    rw [hu]
    exact h.module_le_center_radical.trans (map_subtype_le _)
  have hcomm : ⁅L,R⁆ ≤ L.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      (h.radical_isTwoGroup.to_le (le_normalizer_iff_commutator_le_right.mp hLR))
      (le_normalizer_iff_commutator_le_left.mp (h.radical_le.trans hn))
      (normalizer_commutator_ge_left L R)
  simpa only [hu] using
    hb.two_subgroup_eq_module_sup_centralizer h.radical_isTwoGroup hLR hUR hcomm

theorem normalized_radical_commutator_le_module
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : M ≤ normalizer (L : Set G)) (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = V) : ⁅R,L⁆ ≤ V := by
  have hsplit := h.normalized_radical_eq_module_sup_centralizer hn hb hu
  have hVL : V ≤ L := hu ▸ map_subtype_le _
  have hVC : V ≤ centralizer ((R ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    hVL.trans (le_centralizer_iff.mp inf_le_right)
  have hVR : L ≤ normalizer (V : Set G) := by
    rw [←hu]
    exact L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (blockU L))
  apply commutator_le_of_le_sup_centralizing R L V (R ⊓ centralizer (L : Set G))
  · rw [sup_comm,←hsplit]
  · exact le_centralizer_iff.mp hVC
  · exact inf_le_right
  · exact hVR

omit [Finite G] in
theorem block_module_irreducible_ambient
    (hb : IsAlternatingBlock L 5) (hu : (blockU L).map L.subtype = V)
    (W : Subgroup G) (hWV : W ≤ V) (hLW : L ≤ normalizer (W : Set G)) (hne : W ≠ ⊥) : V ≤ W := by
  have hWL : W ≤ L := hWV.trans (hu ▸ map_subtype_le _)
  have hn : (W.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hLW
  have hfixed : blockU L ⊓ center L = ⊥ := by
    rw [←blockFixed_map,hb.blockFixed_eq_bot,Subgroup.map_bot]
  have hWU : W.subgroupOf L ≤ blockU L := by
    intro w hw
    have hh := hWV hw
    rw [←hu] at hh
    exact (mem_map_iff_mem L.subtype_injective).mp hh
  rcases hb.2.1.irreducible.2 (W.subgroupOf L) hn (hfixed ▸ bot_le) hWU with hz|ht
  · rw [hfixed] at hz
    have hh := congrArg (map L.subtype) hz
    exact (hne (by simpa only [map_subgroupOf_eq_of_le hWL,Subgroup.map_bot] using hh)).elim
  · have hh := congrArg (map L.subtype) ht
    rw [map_subgroupOf_eq_of_le hWL,hu] at hh
    exact hh.symm.le

/-- Genuine A/C discharge the Schreier input on the original ordinary component. -/
theorem component_outer_solvable
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) : Group.IsSolvable (MulAut.Outer K) := by
  let := hK.2
  have he : solvableRadical K = center K := le_antisymm IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center K) inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)))
  have hs := (ChapterA.Section03.SourceComponents.source_model_inputs_on_cComponent_of_theoremC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h.sqtk K hK.isCComponent).1
  let := hs
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    MulAut.isSolvable_outer_of_mulEquiv
      (QuotientGroup.congr (center K) (solvableRadical K) (MulEquiv.refl K)
        (by simpa using he.symm))
  exact Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
end CFSG.Quasithin.ChapterC.HypothesisC28
