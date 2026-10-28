module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers
public import Theory.GroupTheory.SmallMoverEqualIndex

/-!
# The unequal-neighbor branches with the whole kernel

Equal neighboring mover orders rule out the full-edge alternative, so each
mover is the unique maximum on its own natural layer. Its exact fixed index
is q squared, and the natural-cover calculation lifts quadraticity to that
whole U-layer. On the other layer its movement is q cubed.

If the neighboring image has order at most q squared, the equal orders and
the original lower bound force both images to have order exactly q squared
and force the entire original Q-kernel into the neighboring mover. This
also bounds their literal intersection modulo Q. UnequalSelectedBranches
carries these conclusions through the actual selected backward-path choice.

Source: MS93 (5.4)--(5.5)(c), printed pp.915--917. The individual generation
alternative, its exceptional nonsplitting clause, and terminal distance
exclusions still require proof; the numerical branch alone is not (5.5).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Unequal neighboring movers each belong to the unique-maximum branch. -/
theorem Input.replacement_unequal_unique_maximal
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) =
        {Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)} := by
  rcases h.replacement_small_mover_dichotomy d geometry hb ha hat with
    ⟨J,hmax,hjoin⟩ | ⟨_,hjoin,_⟩
  · rwa [hjoin]
  · exfalso
    let := finite_stabilizer d.radical t
    let : Finite (Q d.radical t) := Finite.of_injective
      (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
      (inclusion_injective _)
    have hc := small_mover_neighbor_card_eq d.radical hat hct (Nat.card F^2)
    rw [hjoin] at hc
    have he := eq_of_le_of_card_ge (Subgroup.SmallMover.join_le
      (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2)) hc.le
    exact hne (he.trans hjoin.symm)

/-- The original mover has exact square movement and acts quadratically
on the whole original U-layer, including every central attachment. -/
theorem Input.replacement_unequal_original_quadratic
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^2 ∧
      ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hmax := h.replacement_unequal_unique_maximal d geometry hb ha hat hct hne
  have hJ : J ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := hmax ▸ Set.mem_singleton J
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hidx,hquad⟩ :=
    h.replacement_small_mover_quadratic_coordinates d geometry hb ha hat
  let U₀ := (U d.radical a).subgroupOf S
  let J₀ := J.subgroupOf S
  let A := (J₀.map f).subgroupOf unipotent
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := hJT.trans hTS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hAf : J₀.map f ≤ unipotent := (map_mono (comap_mono hJT)).trans hTf
  have hAm : A.map unipotent.subtype = J₀.map f := map_subgroupOf_eq_of_le hAf
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hc : Nat.card A = (Q d.radical a).relIndex J := by
    rw [←card_map_of_injective unipotent.subtype_injective,hAm,←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm
  have hi : movingIndex A = (centralizer (J : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) := by
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ J₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,
      hidx J₀ (comap_mono hJT)] at hh
    exact hh.symm
  have hs : Degree.Small A := by
    rw [Degree.Small,hi,hc,hBF]
    exact hJ.1.2
  have hq : IsQuadratic (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (J₀.map f) := by
    have hh := Degree.small_quadratic A hs
    rwa [hAm] at hh
  have hlarge : Nat.card B.Carrier^2 ≤ Nat.card A := by
    rw [hc,hBF]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hfield : 1 < Nat.card B.Carrier := Finite.one_lt_card
  have hm : movingIndex A = Nat.card B.Carrier^2 := by
    rcases Degree.small_classification A hs with he | ⟨s,he⟩ | ⟨hw,_⟩ | ⟨l,he⟩
    · rw [he,card_bot] at hlarge
      nlinarith
    · rw [he,card_rootFamily] at hlarge
      nlinarith
    · exact movingIndex_eq_field_sq_of_large_wing A hw (by nlinarith)
    · rw [he,Degree.movingIndex_finitePlane]
  refine ⟨by rw [←hi,hm,hBF],?_⟩
  have hh := congrArg (Subgroup.map S.subtype) (hquad J₀ hq)
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hUS,
    map_subgroupOf_eq_of_le hJS,Subgroup.map_bot] at hh
  exact hh

/-- At the smallest possible individual image order, equal neighboring
orders force the whole original vertex kernel into the other mover. This
proves the kernel and intersection clauses in the small-image branch of
MS93 (5.5)(c), without assuming kernel containment in that mover. -/
theorem Input.replacement_unequal_small_image_saturated
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical c)
      (Q d.radical c) (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    Q d.radical a ≤ J ⊓ E ∧
      (Q d.radical a).relIndex J = Nat.card F^2 ∧
      (Q d.radical a).relIndex E = Nat.card F^2 ∧
      (Q d.radical a).relIndex (J ⊓ E) ≤ Nat.card F^2 := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let Q₀ := (Q d.radical a).subgroupOf S
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let := finite_stabilizer d.radical a
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hc : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S.subtype_injective (K := J₀),
      ←card_map_of_injective S.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    exact small_mover_neighbor_card_eq d.radical hat hct _
  have hjidx : Q₀.relIndex J₀ = (Q d.radical a).relIndex J := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm
  have heidx : Q₀.relIndex E₀ = (Q d.radical a).relIndex E := by
    have hh := relIndex_map_map_of_injective Q₀ E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm
  obtain ⟨hk,hj',he'⟩ := Subgroup.SmallMover.kernel_le_of_card_eq_of_relIndex_bounds
    Q₀ J₀ E₀ (comap_mono hQJ) hc (Nat.card F^2)
    (hjidx.symm ▸ h.replacement_small_mover_join_index d geometry hb ha hat)
    (heidx.symm ▸ hsmall)
  have hQE : Q d.radical a ≤ E := by
    have hh := map_mono (f := S.subtype) hk
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    exact hh
  refine ⟨le_inf hQJ hQE,hjidx.symm.trans hj',heidx.symm.trans he',?_⟩
  have hi : Q₀.relIndex (J₀ ⊓ E₀) ≤ Nat.card F^2 :=
    (relIndex_le_of_le_right inf_le_left
      (index_ne_zero_of_finite (H := Q₀.subgroupOf J₀))).trans_eq hj'
  have hh := relIndex_map_map_of_injective Q₀ (J₀ ⊓ E₀) S.subtype_injective
  rw [map_inf _ _ _ S.subtype_injective,map_subgroupOf_eq_of_le hQS,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES] at hh
  exact hh.le.trans hi

/-- Every prescribed unequal neighboring mover has either an image larger
than q squared, or the original full-kernel and intersection conclusions.
Both movers are quadratic on their own whole U-layers, even though the
neighbor has cubic movement on the original one. -/
theorem Input.replacement_unequal_branch_data
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ ∧ ⁅⁅U d.radical c,E⁆,E⁆ = ⊥ ∧
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ((Nat.card F^2 < (Q d.radical a).relIndex E) ∨
        (Q d.radical a ≤ J ⊓ E ∧
          (Q d.radical a).relIndex J = Nat.card F^2 ∧
          (Q d.radical a).relIndex E = Nat.card F^2 ∧
          (Q d.radical a).relIndex (J ⊓ E) ≤ Nat.card F^2)) := by
  dsimp only
  have hc : color d.radical c = false := by
    have hn₁ := adjacent_color_ne d.radical hat
    have hn₂ := adjacent_color_ne d.radical hct
    rw [ha] at hn₁
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  refine ⟨(h.replacement_unequal_original_quadratic d geometry hb ha hat hct hne).2,
    (h.replacement_unequal_original_quadratic d geometry hb hc hct hat hne.symm).2,
    (h.replacement_unequal_individual_edge_fixed d geometry hb ha hat hct hne).1,?_⟩
  by_cases hs : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical c)
      (Q d.radical c) (Q d.radical t) (Nat.card F^2)) ≤ Nat.card F^2
  · exact Or.inr (h.replacement_unequal_small_image_saturated d geometry hb ha hat hct hs)
  · exact Or.inl (lt_of_not_ge hs)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
