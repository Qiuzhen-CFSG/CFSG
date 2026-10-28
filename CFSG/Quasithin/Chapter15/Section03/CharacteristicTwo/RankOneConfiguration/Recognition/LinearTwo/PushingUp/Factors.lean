module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Factors.Transport

/-!
# Recognition of the selected component in the pushing-up product

The C.1.26 product generates O²(I), whose embedded image is the selected
component L. Pairwise commutation makes every factor normal in L. Its image
in the quasisimple quotient L/O₂(L) is central or the whole quotient.
Generation rules out central images for all factors. A factor with full image
has a two-group quotient in L, so two-perfectness makes it equal to L.

The factor's intrinsic quotient and module models transport along the actual
subgroup equivalence. Perfectness excludes A₃, leaving the L₂ and A₅ types.
Subnormality is asserted inside I, the ambient group of the supplied blocks.
This helper assumes the full residual product; constructing that product from
minimal parabolicity and C.1.26 belongs to the parent pushing-up argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–12,
printed pp.123–124; C.1.26, p.132; 15.3.26–30, pp.1130–1132.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

private theorem member_eq_join {H : Type*} [Group H]
    (L : Subgroup H) (F : Set (Subgroup H)) (hgen : sSup F = L)
    (hcomm : F.Pairwise fun K J => ⁅K, J⁆ = ⊥)
    (hp : IsPPerfect 2 L) [IsQuasisimple (L ⧸ pCore 2 L)] : L ∈ F := by
  classical
  let Q := L ⧸ pCore 2 L
  let q : L →* Q := QuotientGroup.mk' (pCore 2 L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hle (K : Subgroup H) (hK : K ∈ F) : K ≤ L := hgen ▸ le_sSup hK
  have hnormal (K : Subgroup H) (hK : K ∈ F) : (K.subgroupOf L).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (hle K hK)).mpr
    rw [← hgen]
    apply sSup_le
    intro J hJ
    by_cases he : K = J
    · subst J; exact K.le_normalizer
    · exact le_normalizer_iff_commutator_le_left.mpr (by
        rw [hcomm hK hJ he]; exact bot_le)
  by_contra hnot
  have hcentral (K : Subgroup H) (hK : K ∈ F) :
      (K.subgroupOf L).map q ≤ center Q := by
    let := hnormal K hK
    let : ((K.subgroupOf L).map q).Normal :=
      (hnormal K hK).map q hq
    rcases IsQuasisimple.normal_le_center_or_eq_top ((K.subgroupOf L).map q) with hc | ht
    · exact hc
    · have hsup : K.subgroupOf L ⊔ pCore 2 L = ⊤ := by
        have he := congrArg (Subgroup.comap q) ht
        have hk : q.ker = pCore 2 L := QuotientGroup.ker_mk' _
        simpa only [comap_map_eq, hk, comap_top] using he
      have he := hp (K.subgroupOf L) (hnormal K hK)
        (isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hsup)
      have hKL : K = L := le_antisymm (hle K hK) (subgroupOf_eq_top.mp he)
      exact (hnot (hKL ▸ hK)).elim
  have hL : L ≤ ((center Q).comap q).map L.subtype := by
    apply hgen.ge.trans
    apply sSup_le
    intro K hK x hx
    exact ⟨⟨x, hle K hK hx⟩,
      hcentral K hK (mem_map_of_mem q (show (⟨x, hle K hK hx⟩ : L) ∈
        K.subgroupOf L from hx)), rfl⟩
  have hz : center Q = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨z, hz, he⟩ := hL x.property
    have he' : z = x := Subtype.ext he
    exact he' ▸ hz
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  exact Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hz)

/-- The component is an actual member of the supplied central product in I. -/
theorem component_mem_factors {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} {c : ComponentWitness d I}
    (h : Earlier d I c) (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (b : ResidualBlockProduct I P) : c.L.subgroupOf I ∈ b.factors := by
  let e : c.L ≃* c.L.subgroupOf I := (subgroupOfEquivOfLe (component_le c)).symm
  let := c.core_quotient_quasisimple
  let : IsQuasisimple ((c.L.subgroupOf I) ⧸ pCore 2 (c.L.subgroupOf I)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  apply member_eq_join _ b.factors _ b.commute
    ((component_twoPerfect d h).of_surjective e.toMonoidHom e.surjective)
  apply map_injective I.subtype_injective
  rw [b.generate, residual_I_eq_component d h hI P hP,
    map_subgroupOf_eq_of_le (component_le c)]

private theorem not_alternating_three {L : Type*} [Group L] [Group.IsPerfect L] :
    ¬ ChapterC.IsAlternatingBlock L 3 := by
  intro h
  obtain ⟨e⟩ := h.2.2.quotient_iso
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Group.IsPerfect (alternatingGroup (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := f)
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact Group.IsPerfect.not_isMulCommutative (alternatingGroup (Fin 3))
    (alternatingGroup.isMulCommutative_of_card_le_three (by simp))

/-- Conditional central-product recognition for 15.3.30. The relative block
assertion and the genuine quotient/module alternatives are both retained. -/
theorem block_recognition {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} {c : ComponentWitness d I}
    (h : Earlier d I c) (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (b : ResidualBlockProduct I P) :
    ChapterC.IsBlock (c.L.subgroupOf I) ∧
      ((∃ m, ChapterC.IsL2EvenBlock c.L m) ∨ ChapterC.IsAlternatingBlock c.L 5) := by
  have hb := b.block _ (component_mem_factors d h hI P hP b)
  let e : c.L.subgroupOf I ≃* c.L := subgroupOfEquivOfLe (component_le c)
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with ⟨m, hm⟩ | hthree | hfive
  · exact Or.inl ⟨m, hm.of_mulEquiv e⟩
  · let := component_isPerfect_of_containment d c h.contains
    exact (not_alternating_three (hthree.of_mulEquiv e)).elim
  · exact Or.inr (hfive.of_mulEquiv e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

end
