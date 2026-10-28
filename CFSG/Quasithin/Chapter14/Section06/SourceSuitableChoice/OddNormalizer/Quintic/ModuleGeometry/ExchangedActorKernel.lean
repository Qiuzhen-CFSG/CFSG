module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedActorProduct
public import Theory.SpecificGroups.PSL2.SixteenWreathOrder
public import Theory.GroupTheory.SylowSubnormalIntersectionIndex

/-!
# Component normalizers detected by the literal quintic actors

The component normalizer has index two in Mc. An element of H outside it
exchanges the two components, hence also their disjoint nontrivial images
in H/O₂(H). Thus preserving the first actor image is equivalent to
normalizing its actual component. The original two-core acts trivially
in this quotient, so it normalizes both components. Its commutators with
each component intersection lie in that component's Sylow intersection.

The final consumer constructs both normalizer and displacement controls
from Context, using the same actual factors and quotient. These remove
kernel-action premises for the remaining exchanged module comparison;
they do not identify the component actors with the original H₁,H₂ actors.
The support alignment, conjugated point centralizer and p=3 assembly remain
with qt-e-14615-quintic-exclusion. Earlier 14.6.12--14 retain their original
source producers and final suitable-choice discharge. In particular the
factor-join index is the allowed premise owned by qt-e-14612-singleton.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem original_H_le_partner : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

omit [Finite G] in
private theorem actorImage_intersection (K : Subgroup G) :
    actorImage H (K ⊓ H) = actorImage H K := by
  unfold actorImage
  congr 1
  ext x
  exact and_iff_left x.property

omit [Finite G] in
private theorem actorImage_conjugate_any (K : Subgroup G) (h : H) :
    actorImage H (K.map (MulAut.conj (h : G)).toMonoidHom) =
      (actorImage H K).map (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom := by
  have hh := actorImage_conjugate (K ⊓ H) inf_le_right h
  have hH : H.map (MulAut.conj (h : G)).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer h.property)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (h : G)).injective,hH,
    actorImage_intersection,actorImage_intersection] at hh
  exact hh

include s in
theorem source_exchanged_first_actor_normalizer
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) (x : H) :
    (x : G) ∈ normalizer (b.K1 : Set G) ↔
      QuotientGroup.mk' (pCore 2 H) x ∈ normalizer (actorImage H b.K1 : Set (H ⧸ pCore 2 H)) := by
  constructor
  · intro hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : b.K1.map (MulAut.conj (x : G)).toMonoidHom = b.K1 :=
      mem_normalizer_iff_map_conj_eq.mp hx
    exact (actorImage_conjugate_any b.K1 x).symm.trans (congrArg (actorImage H) he)
  · intro hx
    by_contra hn
    obtain ⟨t,ht,htn,he⟩ := b.exchanged
    have hex := map_conj_eq_of_outside_normalizer H Mc
      (Mc ⊓ normalizer (b.K1 : Set G)) b.K1 b.K2 (original_H_le_partner s)
      b.first_le b.first_index inf_le_right t (s.outside.1.2 ht) htn he
      x x.property (fun h => hn h.2)
    have hi := actorImage_conjugate_any (H := H) b.K1 x⁻¹
    have hqi : (actorImage H b.K1).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) x)⁻¹).toMonoidHom = actorImage H b.K1 :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem hx)
    change actorImage H (b.K1.map (MulAut.conj (x : G)⁻¹).toMonoidHom) =
      (actorImage H b.K1).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) x⁻¹)).toMonoidHom at hi
    rw [hex,map_inv,hqi] at hi
    have hd := source_exchanged_actor_disjoint s b
    rw [hi] at hd
    have hb : actorImage H b.K1 = ⊥ := disjoint_self.mp hd
    have hc := source_exchanged_component_actor_card s b b.first_le b.first_component b.first_model
      ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq)
    rw [hb,card_bot] at hc
    omega

include s in
theorem source_exchanged_core_normalizes_first
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    H.pCoreIn 2 ≤ normalizer (b.K1 : Set G) := by
  rintro _ ⟨x,hx,rfl⟩
  apply (source_exchanged_first_actor_normalizer s b x).mpr
  have he : QuotientGroup.mk' (pCore 2 H) x = 1 :=
    (QuotientGroup.eq_one_iff (N := pCore 2 H) x).mpr hx
  rw [he]
  exact one_mem _

include s in
theorem source_exchanged_core_normalizes_factors
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    H.pCoreIn 2 ≤ normalizer (b.K1 : Set G) ∧
      H.pCoreIn 2 ≤ normalizer (b.K2 : Set G) := by
  have hfirst := source_exchanged_core_normalizes_first s b
  refine ⟨hfirst,?_⟩
  obtain ⟨t,ht,_,he⟩ := b.exchanged
  rw [←he,←map_equiv_normalizer_eq b.K1 (MulAut.conj t⁻¹)]
  have hm := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hfirst
  have hQ : (H.pCoreIn 2).map (MulAut.conj t⁻¹).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer_le_normalizer_characteristic_image H (pCore 2 H))
        (H.le_normalizer (H.inv_mem (s.outside.1.2 ht))))
  rwa [hQ] at hm

include s in
theorem source_exchanged_core_borel_commutators
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    ⁅H.pCoreIn 2,b.K1 ⊓ H⁆ ≤ b.K1 ⊓ (T : Subgroup G) ∧
      ⁅H.pCoreIn 2,b.K2 ⊓ H⁆ ≤ b.K2 ⊓ (T : Subgroup G) := by
  have hn := source_exchanged_core_normalizes_factors s b
  have hQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have step (K : Subgroup G) (hKz : K ≤ residualClosure H Mc)
      (hKN : H.pCoreIn 2 ≤ normalizer (K : Set G)) :
      ⁅H.pCoreIn 2,K ⊓ H⁆ ≤ K ⊓ (T : Subgroup G) := by
    rw [←source_exchanged_component_core_intersection s b hKz]
    exact le_inf ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hKN))
      (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hQ))
  exact ⟨step b.K1 ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) hn.1,
    step b.K2 ((le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) hn.2⟩

include s in
theorem source_exchanged_core_borel_control :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      H.pCoreIn 2 ≤ normalizer (b.K1 : Set G) ∧
      H.pCoreIn 2 ≤ normalizer (b.K2 : Set G) ∧
      H.pCoreIn 2 ≤ normalizer ((b.K1 ⊓ (T : Subgroup G) : Subgroup G) : Set G) ∧
      H.pCoreIn 2 ≤ normalizer ((b.K2 ⊓ (T : Subgroup G) : Subgroup G) : Set G) ∧
      ⁅H.pCoreIn 2,b.K1 ⊓ H⁆ ≤ b.K1 ⊓ (T : Subgroup G) ∧
      ⁅H.pCoreIn 2,b.K2 ⊓ H⁆ ≤ b.K2 ⊓ (T : Subgroup G) := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  obtain ⟨h1,h2⟩ := source_exchanged_core_normalizes_factors s b
  exact ⟨b,h1,h2,(le_inf (pCoreIn_le 2 H) h1).trans
    (source_exchanged_component_borel_control s b.first_le b.first_component b.first_model),
    (le_inf (pCoreIn_le 2 H) h2).trans
    (source_exchanged_component_borel_control s b.second_le b.second_component b.second_model),
    source_exchanged_core_borel_commutators s b⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
