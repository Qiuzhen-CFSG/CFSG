module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.ResidualSource
public import Theory.GroupTheory.FourNormalizerTwoCore

/-!
# The two-core of each original component four-normalizer

Every four in S∩K has a symmetric-four normalizer inside K. Its conjugation
action supplies all automorphisms of the four, while the actual source
centralizer lies in S. Thus O₂(N_H(F))=C_S(F), exactly the subgroup Q_E
used in source 2.5.15. No kernel or action-surjectivity premise remains.
Source: Aschbacher--Smith 2.5.8(5), 2.5.12, 2.5.15, pp.556--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentSelection ComponentRefinement
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M F : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem four_normalizer_twoCore_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) [IsKleinFour F]
    (hFS : F ≤ (S : Subgroup H).map H.subtype) (hFK : F ≤ K) :
    twoCore (H ⊓ normalizer (F : Set G)) =
      (S : Subgroup H).map H.subtype ⊓ centralizer (F : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  let N := H ⊓ normalizer (F : Set G)
  let D := K ⊓ normalizer (F : Set G)
  have hFN : F ≤ N := le_inf (hFK.trans c.component_le) F.le_normalizer
  have hFD : F ≤ D := le_inf hFK F.le_normalizer
  have hDN : D ≤ N := inf_le_inf_right _ c.component_le
  let E := F.subgroupOf N
  let B := D.subgroupOf N
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hFN).mpr inf_le_right
  let eE := subgroupOfEquivOfLe hFN
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  have hm := ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  obtain ⟨e⟩ := ComponentSelection.MathieuSourceSetup.four_normalizer c hm F hFK
  have hh : D.subgroupOf K = normalizer (F.subgroupOf K : Set K) := by
    change (K ⊓ normalizer (F : Set G)).subgroupOf K = _
    rw [inf_subgroupOf_left, subgroupOf_normalizer_eq hFK]
  let eD : D ≃* Equiv.Perm (Fin 4) :=
    ((subgroupOfEquivOfLe (show D ≤ K from inf_le_left)).symm.trans
      (MulEquiv.subgroupCongr hh)).trans e
  let eB : B ≃* Equiv.Perm (Fin 4) := (subgroupOfEquivOfLe hDN).trans eD
  have hC := ComponentSelection.MathieuSourceSetup.four_centralizer_le_source_sylow c hm
    (normal_component_centralizer_le_source_sylow c hG hempty hgen) F hFS hFK
  have hCmap : (centralizer (E : Set N)).map N.subtype ≤ Y := by
    rintro _ ⟨x,hx,rfl⟩
    apply hC
    refine ⟨x.property.1,?_⟩
    intro f hf
    exact congrArg Subtype.val (hx (⟨f,hFN hf⟩ : N) hf)
  have hc : IsPGroup 2 (centralizer (E : Set N)) := by
    have hp := (S.isPGroup'.map H.subtype).to_le hCmap
    exact hp.of_equiv ((centralizer (E : Set N)).equivMapOfInjective N.subtype N.subtype_injective).symm
  have hcore := twoCore_eq_centralizer_of_normal_four_symmetric_overgroup E B
    (fun _ hx => hFD hx) eB hc
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    rw [hcore] at hx
    refine ⟨hCmap (mem_map_of_mem N.subtype hx),?_⟩
    intro f hf
    exact congrArg Subtype.val (hx (⟨f,hFN hf⟩ : N) hf)
  · intro x hx
    have hxN : x ∈ N := ⟨map_subtype_le _ hx.1,Subgroup.centralizer_le_normalizer _ hx.2⟩
    refine ⟨⟨x,hxN⟩,?_,rfl⟩
    rw [hcore]
    intro f hf
    exact Subtype.ext (hx.2 f hf)
end CFSG.Quasithin.Chapter2.Section05
