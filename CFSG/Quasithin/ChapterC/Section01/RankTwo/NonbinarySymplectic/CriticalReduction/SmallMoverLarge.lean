module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductExclusion

/-!
# The large unique maximum in the original small-mover family

The root-product exclusion rules out a single full root as the unique
maximum small mover. Thompson replacement rules out the trivial image.
The remaining arbitrary-degree coordinate alternatives have order at
least q squared: a subgroup of the standard wing, or a finite plane
inside the point wing. All indices are on the original U-layer and the
entire quotient kernel is retained.

This completes the size assertion of MS93 (5.4)(a), printed p.915, and
retains the literal coordinate alternatives needed by (5.5)--(5.6).
The maximizing parabolic and selected-path constructions remain separate
source steps; no fixed parabolic label is imposed without that choice.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_unique_small_mover_large
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (J : Subgroup (FreeAmalgam d.radical))
    (hmax : Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2) = {J}) :
    Nat.card F ^ 2 ≤ (Q d.radical a).relIndex J ∧
      ∃ E : BinaryField, E.degree = n ∧
        ∃ f : stabilizer d.radical a →* Sp E.Carrier,
          Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
          ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
          (Degree.Quotient.coordinates f unipotent.subtype
              (J.subgroupOf (stabilizer d.radical a)) ≤ CentralRootGeometry.wing true ∨
            ∃ l : E.Carrier,
              Degree.Quotient.coordinates f unipotent.subtype
                (J.subgroupOf (stabilizer d.radical a)) = finitePlane l ∧
              Degree.Quotient.coordinates f unipotent.subtype
                ((Q d.radical t).subgroupOf (stabilizer d.radical a)) ≤
                  CentralRootGeometry.wing false) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hKmap : f.ker.map S.subtype = Q d.radical a := hfQ
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hTi : T.map f ≤ (unipotent (F := E.Carrier)).subtype.range := by
    simpa only [range_subtype] using hTf
  have hpre (C : Subgroup (FreeAmalgam d.radical))
      (hC : C ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2)) :
      C.subgroupOf S ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card E.Carrier ^ 2) := by
    apply (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective U₀ f.ker T _ _).mp
    simpa only [hUT,hKmap,hTT,map_subgroupOf_eq_of_le (hC.1.1.trans hTS),hcard] using hC
  have hJ : J ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2) := hmax ▸ Set.mem_singleton J
  have hjoin : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2) = J := by
    simp only [Subgroup.SmallMover.join,hmax,sSup_singleton]
  have hJQ : ¬ J ≤ Q d.radical a := by
    rw [←hjoin]
    exact h.replacement_small_mover_join_not_le_kernel d geometry hb ha hat
  let J₀ := J.subgroupOf S
  let A := Degree.Quotient.coordinates f unipotent.subtype J₀
  have hJS : J ≤ S := hJ.1.1.trans hTS
  have hJm : J₀.map S.subtype = J := map_subgroupOf_eq_of_le hJS
  have hJc := Degree.Quotient.maximal_coordinates U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK hTi hidx (hpre J hJ)
  have hJi : J₀.map f ≤ unipotent.subtype.range := (map_mono (comap_mono hJ.1.1)).trans hTi
  have hcardJ : Nat.card A = (Q d.radical a).relIndex J := by
    have hc := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,hJm] at hc
    rw [hc,relIndex_ker,←Degree.Quotient.coordinates_map f unipotent.subtype J₀ hJi,
      card_map_of_injective Subtype.val_injective]
  have hidxJ : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      movingIndex A := by
    rw [←hJm,←hUT,Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective]
    exact hidx J₀ (comap_mono hJ.1.1)
  rcases Degree.small_classification A hJc.2.1 with hbot | ⟨s,hs⟩ | ⟨hw,hlarge⟩ | ⟨l,hl⟩
  · apply False.elim
    apply hJQ
    have hm : J₀.map f = ⊥ := by
      rw [←Degree.Quotient.coordinates_map f unipotent.subtype J₀ hJi]
      change A.map unipotent.subtype = ⊥
      rw [hbot,Subgroup.map_bot]
    have hle : J₀ ≤ f.ker := ((map_eq_bot_iff J₀).mp hm)
    have hh := map_mono (f := S.subtype) hle
    rwa [hfQ,hJm] at hh
  · have hc : (Q d.radical a).relIndex J = Nat.card F := by
      rw [←hcardJ,hs,card_rootFamily,hcard]
    have hi : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F := by
      rw [hidxJ,hs,movingIndex_rootFamily,hcard]
    apply False.elim
    apply h.replacement_root_product_excluded d geometry hb ha hat J J hJ.1.1 hJ.1.1 hc hc hi hi
    rw [hjoin]
    exact Set.subset_mul_left _ (one_mem _)
  · refine ⟨?_,E,hE,f,hf,hfQ,hTf,Or.inl hw⟩
    rwa [hcard,hcardJ] at hlarge
  · refine ⟨?_,E,hE,f,hf,hfQ,hTf,Or.inr ⟨l,hl,?_⟩⟩
    · rw [←hcardJ,hl,card_finitePlane,hcard]
    · exact Degree.le_point_wing_of_maximal_finitePlane _ l (hl ▸ hJc)

/-- At every actual replacement edge, the entire maximum-small-mover join
has relative order at least q squared. -/
theorem Input.replacement_small_mover_join_index
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    Nat.card F ^ 2 ≤ (Q d.radical a).relIndex
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2)) := by
  rcases h.replacement_small_mover_dichotomy d geometry hb ha hat with
    ⟨J,hmax,hjoin⟩ | ⟨_,hjoin,horder⟩
  · rw [hjoin]
    exact (h.replacement_unique_small_mover_large d geometry hb ha hat J hmax).1
  · rw [hjoin,horder]
    exact Nat.pow_le_pow_right Nat.card_pos (by decide)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
