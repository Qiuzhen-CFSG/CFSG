module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalSource

/-!
# The actual A₅ residual is noncentral in the original component

The perfect A₅ image is unchanged by taking the two-residual of its original
preimage. If that residual were central modulo O₂(L), its image in A₇ would
be central because L maps onto A₇. The latter has trivial center, whereas
the actual image is A₅. This discharges C.1.21's seed noncentrality premise.

Source: Aschbacher–Smith C.1.24, printed p.131, selected X∞ seed.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
local notation "A7" => alternatingGroup (Fin 7)
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := A)]
  exact solvableResidual_le_of_solvable_quotient N

/-- Taking the two-residual preserves the actual A₅ image of the selected group. -/
theorem exceptional_selected_residual_image
    (q : G →* A7) (H : Subgroup G) (B : Subgroup A7)
    (eB : B ≃* alternatingGroup (Fin 5)) (hH : H.map q = B) :
    ((pResidual 2 H).map H.subtype).map q = B := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  let f : H →* B := (q.comp H.subtype).codRestrict B
    (fun h => hH ▸ mem_map_of_mem q h.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨h,hh,hb⟩ := (show (b : A7) ∈ H.map q by rw [hH]; exact b.property)
    exact ⟨⟨h,hh⟩,Subtype.ext hb⟩
  have he : q.comp H.subtype = B.subtype.comp f := rfl
  rw [map_map,he,←map_map,map_pResidual_of_surjective 2 f hf,
    (pResidual_eq_top_iff 2 B).mpr perfect_twoPerfect,
    ←MonoidHom.range_eq_map,range_subtype]

/-- The selected A₅ image rules out centrality in the literal component
quotient, including possible odd central covers of A₇. -/
theorem exceptional_selected_residual_not_central
    (q : G →* A7) (H L : Subgroup G) (B : Subgroup A7)
    (eB : B ≃* alternatingGroup (Fin 5)) (hH : H.map q = B)
    (hL : L.IsSubnormal) (hLq : L.map q = ⊤)
    (hQ : pCore 2 G ≤ q.ker) (hYL : (pResidual 2 H).map H.subtype ≤ L) :
    ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L) := by
  let Y := (pResidual 2 H).map H.subtype
  have hY : Y.map q = B := exceptional_selected_residual_image q H B eB hH
  have hk : pCore 2 L ≤ (q.comp L.subtype).ker := by
    rw [←hL.pCore_subgroupOf 2]
    intro x hx
    exact hQ hx
  let f := QuotientGroup.lift (pCore 2 L) (q.comp L.subtype) hk
  intro hcent
  have hBc : B ≤ center A7 := by
    intro b hb
    obtain ⟨y,hy,hyb⟩ := (show b ∈ Y.map q by rw [hY]; exact hb)
    have hz := hcent (mem_map_of_mem (QuotientGroup.mk' (pCore 2 L))
      (show (⟨y,hYL hy⟩ : L) ∈ Y.subgroupOf L from hy))
    rw [mem_center_iff]
    intro a
    obtain ⟨l,hl,hla⟩ := (show a ∈ L.map q by rw [hLq]; trivial)
    have he := congrArg f (mem_center_iff.mp hz
      (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
    simp only [map_mul] at he
    change q l * q y = q y * q l at he
    rwa [hla,hyb] at he
  have hbot : B = ⊥ := by
    rw [alternatingGroup.center_eq_bot (by simp)] at hBc
    exact bot_unique hBc
  have hc : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hbot,card_bot] at hc
  omega

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
