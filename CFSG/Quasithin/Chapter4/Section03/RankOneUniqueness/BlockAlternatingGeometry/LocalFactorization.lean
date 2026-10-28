module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalMarking
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension

/-!
# The Sylow factorization in the A₇ branch

The actual KS action has image S₇, and its Sylow image has order sixteen.
The radical maps to the marked transposition group, so |S:R|=8. Meanwhile
LT/O₂(LT) is A₅ or S₅, whose Sylow two-subgroups have order at most eight.
Since R=S∩O₂(LT), the image of S fills the image of T. This proves the
literal factorization T=S O₂(LT).

Source: Aschbacher–Smith, original 4.3.7, printed p.616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem join_sylow (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G),
      (P : Subgroup _) = ((T : Subgroup G) ⊓ c.H).subgroupOf
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)) := by
  let J := c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)
  have hJH : J ≤ c.H := sup_le (map_subtype_le _) inf_le_right
  let f : J →* c.H := inclusion hJH
  obtain ⟨P,hP⟩ := c.sylow
  have hm (x : c.H) : x ∈ (P : Subgroup c.H) ↔ (x : G) ∈ (T : Subgroup G) ⊓ c.H := by
    rw [←hP]
    exact (mem_map_iff_mem c.H.subtype_injective).symm
  have hPr : (P : Subgroup c.H) ≤ f.range := by
    intro x hx
    exact ⟨⟨x,mem_sup_right ((hm x).mp hx)⟩,rfl⟩
  refine ⟨P.comapOfInjective f (inclusion_injective hJH) hPr,?_⟩
  ext x
  exact hm (f x)

/-- The actual R has index eight in the original full Sylow intersection. -/
theorem BlockAlternatingCoordinates.radical_relIndex {c : SourceConfiguration T L}
    (d : BlockAlternatingCoordinates c) :
    (c.I.pCoreIn 2).relIndex ((T : Subgroup G) ⊓ c.H) = 8 := by
  let S := (T : Subgroup G) ⊓ c.H
  let J := c.K.map c.H.subtype ⊔ S
  let f := d.chart.actor
  obtain ⟨e,he⟩ := c.alternating_quotient_of_transposition f d.kernel
    d.chart.component_image d.transposition
  have hf : Function.Surjective f := by
    rw [←he]
    exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := join_sylow c
  have hS : Nat.card ((S.subgroupOf J).map f) = 16 := by
    rw [←hP]
    change Nat.card (P.mapSurjective hf) = 16
    rw [Sylow.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    decide +kernel
  have hR : Nat.card (((c.I.pCoreIn 2).subgroupOf J).map f) = 2 := by
    rw [d.transposition,Nat.card_zpowers]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hkR : f.ker ≤ (c.I.pCoreIn 2).subgroupOf J := by
    intro x hx
    exact c.block_join_core_le (mem_map_of_mem J.subtype (d.kernel ▸ hx))
  have hRS : (c.I.pCoreIn 2).subgroupOf J ≤ S.subgroupOf J :=
    comap_mono (c.core_sylow.le.trans inf_le_left)
  have hm := relIndex_mul_relIndex f.ker ((c.I.pCoreIn 2).subgroupOf J)
    (S.subgroupOf J) hkR hRS
  rw [relIndex_ker,relIndex_ker,hR,hS,relIndex_subgroupOf (show S ≤ J from le_sup_right)] at hm
  change 2 * (c.I.pCoreIn 2).relIndex ((T : Subgroup G) ⊓ c.H) = 16 at hm
  omega

private theorem sylow_card_le_eight {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Equiv.Perm (Fin 5)))
    (P : Sylow 2 Q) : Nat.card P ≤ 8 := by
  rw [Sylow.card_eq_multiplicity]
  rcases hQ with hA | hS
  · obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  · obtain ⟨e⟩ := hS
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide +kernel

/-- The marked Sylow intersection fills the entire quotient T/O₂(LT). -/
theorem BlockAlternatingCoordinates.sylow_factorization {c : SourceConfiguration T L}
    (d : BlockAlternatingCoordinates c) (D : Chapter12.Section02.ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4) :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ c.H) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let A := L ⊔ (T : Subgroup G)
  let S := (T : Subgroup G) ⊓ c.H
  let Q := A.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 A)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hpsl
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) hF
  have hA := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    L (T : Subgroup G) D.sylow_normalizes_component T.isPGroup' (eF.trans e5)
  have hqT : Nat.card (((T : Subgroup G).subgroupOf A).map q) ≤ 8 :=
    sylow_card_le_eight hA ((T.subtype le_sup_right).mapSurjective
      (QuotientGroup.mk'_surjective _))
  have hqS : Nat.card ((S.subgroupOf A).map q) = 8 := by
    rw [←relIndex_ker]
    have hk : q.ker = Q.subgroupOf A := by
      rw [QuotientGroup.ker_mk']
      exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
    rw [hk,relIndex_subgroupOf (inf_le_left.trans le_sup_right),←inf_relIndex_left S Q]
    rw [←c.core_sylow]
    exact d.radical_relIndex
  have he : ((T : Subgroup G).subgroupOf A).map q = (S.subgroupOf A).map q :=
    (eq_of_le_of_card_ge
      (show (S.subgroupOf A).map q ≤ ((T : Subgroup G).subgroupOf A).map q from
        map_mono (comap_mono inf_le_left)) (by rw [hqS]; exact hqT)).symm
  have hc := congrArg (comap q) he
  rw [comap_map_eq,comap_map_eq] at hc
  have hcore : q.ker ≤ (T : Subgroup G).subgroupOf A := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)
  rw [sup_eq_left.mpr hcore] at hc
  have hh := congrArg (map A.subtype) hc
  rw [map_subgroupOf_eq_of_le le_sup_right,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_right),QuotientGroup.ker_mk'] at hh
  exact hh
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
