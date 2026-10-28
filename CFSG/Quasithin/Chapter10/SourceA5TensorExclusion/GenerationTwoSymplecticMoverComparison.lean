module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSylowMovers
/-!
# Comparing the original movers across a common edge

Every original vertex kernel has the order of O₂(M), and every canonical
edge mover has sixty-four times that order. Consequently the neighboring
mover has at least sixty-four images modulo the starting kernel, with equality
exactly when it contains that full kernel. Uniqueness of the maximum small
mover now makes equality across the edge equivalent to cross moving index
at most sixteen. Unequal movers have larger cross action.

This is the original-kernel comparison needed by the unequal case of MS93
(5.5), pp.915--917. Its quadratic and backward-path applications are in
GenerationTwoSymplecticUnequalMovers; no selected generator is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The literal vertex kernel has the order of the original two-core. -/
theorem original_kernel_card_eq :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a : Vertex R}, color R a = false → Nat.card (Q R a) = Nat.card (pCore 2 c.M) := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,hi,_,_,_,hiQ⟩ := vertex_coordinates_with_kernel R hodd.isPGroup hodd.twoCore_le ha
  rw [←hiQ,card_map_of_injective hi]

/-- The full original mover has sixty-four times the original kernel order. -/
theorem original_small_mover_card
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      Nat.card (LocalPackage.J R a t) = Nat.card (pCore 2 c.M) * 64 := by
  intro R a t ha hat
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have h := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) (Q R a)
    (LocalPackage.J R a t) bot_le (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat)
  rw [relIndex_bot_left,relIndex_bot_left,
    (c.original_small_mover_join_indices eK ha hat).2.1,c.original_kernel_card_eq ha] at h
  exact h.symm

/-- A neighboring mover has at least sixty-four images modulo the starting kernel. -/
theorem original_neighbor_mover_cross_index_ge_64
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      64 ≤ (Q R a).relIndex (LocalPackage.J R d t) := by
  intro R a d t ha hat hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
  have hcard := c.original_small_mover_card eK hd hdt
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (LocalPackage.J R d t ⊓ Q R a) (LocalPackage.J R d t) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hcard] at hm
  have hc := card_le_of_le (show LocalPackage.J R d t ⊓ Q R a ≤ Q R a from inf_le_right)
  rw [c.original_kernel_card_eq ha] at hc
  have hp : 0 < Nat.card (pCore 2 c.M) := Nat.card_pos
  nlinarith

/-- The two original movers coincide exactly when the cross action is small. -/
theorem original_neighbor_mover_eq_iff_small_cross_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (LocalPackage.J R d t = LocalPackage.J R a t ↔
        (centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16) := by
  intro R a d t ha hat hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hmax,_,hindex⟩ := c.original_small_mover_join_indices eK ha hat
  constructor
  · intro he
    rw [he,hindex]
  · intro hsmall
    have hJa : LocalPackage.J R a t ∈ LocalPackage.MaximalMovers R a t := by
      rw [hmax]
      exact Set.mem_singleton _
    have hJd : LocalPackage.J R d t ∈ LocalPackage.MaximalMovers R a t := by
      refine ⟨⟨LocalPackage.J_le_radical R d t,
        hsmall.trans ((by decide : 16 ≤ 64).trans
          (c.original_neighbor_mover_cross_index_ge_64 eK ha hat hdt)),hsmall⟩,?_⟩
      intro E hE
      have hc := hJa.2 E hE
      rwa [c.original_small_mover_card eK ha hat,←c.original_small_mover_card eK hd hdt] at hc
    rw [hmax] at hJd
    exact Set.mem_singleton_iff.mp hJd

/-- The minimal cross index occurs exactly when the whole starting kernel is retained. -/
theorem original_neighbor_mover_cross_index_eq_64_iff
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      ((Q R a).relIndex (LocalPackage.J R d t) = 64 ↔ Q R a ≤ LocalPackage.J R d t) := by
  intro R a d t ha hat hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (LocalPackage.J R d t ⊓ Q R a) (LocalPackage.J R d t) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,
    c.original_small_mover_card eK hd hdt,←c.original_kernel_card_eq ha] at hm
  change Nat.card (LocalPackage.J R d t ⊓ Q R a : Subgroup (FreeAmalgam R)) *
    (Q R a).relIndex (LocalPackage.J R d t) = Nat.card (Q R a) * 64 at hm
  constructor
  · intro hi
    rw [hi] at hm
    have he : LocalPackage.J R d t ⊓ Q R a = Q R a :=
      eq_of_le_of_card_ge inf_le_right (by omega)
    exact he ▸ inf_le_left
  · intro hQ
    rw [inf_eq_right.mpr hQ] at hm
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hm

/-- Unequal original movers have cross moving index greater than sixteen. -/
theorem original_unequal_mover_cross_action_gt_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
        16 < (centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))).relIndex (U R a) := by
  intro R a d t ha hat hdt hne
  exact Nat.lt_of_not_ge (fun h => hne
    ((c.original_neighbor_mover_eq_iff_small_cross_action eK ha hat hdt).mpr h))
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
