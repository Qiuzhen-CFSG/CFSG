module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMovers
public import Glauberman.ThompsonPair
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverKernels
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.QuadraticIndex

/-!
# The original root-product obstruction on the characteristic replacement

MS3 forces the ordinary all-abelian Thompson subgroup outside the actual
replacement core. Thompson replacement supplies an actual maximum abelian
actor outside Q, quadratic on the full U-layer. The exact natural-cover
index bound makes it a small mover, proving that the full small-mover join
also escapes Q.

If that join lay in a product of two source roots, mapping the literal
product through the whole vertex quotient bounds its order by q². This
excludes the multiple-maximum branch, whose join has relative order q³.
Any failed exclusion therefore has a unique maximum of relative order at
most q²; that same subgroup normalizes the two full fixed seeds.

This proves MS93 (5.1), pp.912--913, in the multiple-maximum branch and
constructs actual inputs to the remaining unique-maximum pushing-up
argument. It does not prove that argument, the special parabolic generator
choices, or the final critical-distance bound. The original field degree,
replacement radical and full quotient kernel are retained throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
private theorem join_not_le_of_admissible
    {G : Type*} [Group G] [Finite G] (V Q T A : Subgroup G) [Q.Normal]
    (k : ℕ) (hk : 1 ≤ k) (hQT : Q ≤ T) (hVQ : V ≤ centralizer (Q : Set G))
    (hA : Subgroup.SmallMover.Admissible V Q T k A) (hAQ : ¬ A ≤ Q) :
    ¬ Subgroup.SmallMover.join V Q T k ≤ Q := by
  obtain ⟨E,hE⟩ := Subgroup.SmallMover.maximal_nonempty V Q T k hk
  have hQE := Subgroup.SmallMover.maximal_contains_kernel V Q T k hQT hVQ hE
  intro hJQ
  have he : E = Q := le_antisymm ((le_sSup hE).trans hJQ) hQE
  have hb := hE.2 (Q ⊔ A) (Subgroup.SmallMover.admissible_sup V Q T A k hQT hVQ hA)
  rw [he] at hb
  have hsup : Q = Q ⊔ A := eq_of_le_of_card_ge le_sup_left hb
  exact hAQ (le_sup_right.trans_eq hsup.symm)

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- The ordinary all-abelian Thompson subgroup of the actual replacement
is outside its own two-core. This is the initial MS93 (5.1) assertion. -/
theorem Input.replacement_all_abelian_thompson_not_le :
    ¬ thompsonSubgroup d.radical ≤ pCore 2 d.overgroup := by
  apply Glauberman.allAbelianThompson_not_le_normal d.radical (pCore 2 d.overgroup)
    (h.replacement_core_le d) (h.replacement_radical_ne_bot d)
  intro A hA hn
  let := hA
  exact (h.replacement_characteristic d).eq_bot_of_normal A hn

omit [Finite F] [CharP F 2] in
/-- An actual maximum-order abelian subgroup of each replacement edge,
selected outside Q, acts quadratically on the full moving layer and
satisfies the source offender inequality there. -/
theorem Input.replacement_quadratic_maximum_abelian
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ A : Subgroup (FreeAmalgam d.radical),
      A ∈ thompsonAbelianSubgroups (Q d.radical t) ∧
      ¬ A ≤ Q d.radical a ∧
      ⁅⁅U d.radical a,A⁆,A⁆ = ⊥ ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤
        (Q d.radical a).relIndex A := by
  let V := Sp4Four.LocalPackage.initialLayer d.radical
  have hVZ : V ≤ omegaOrbit d.radical := commutator_le_left _ _
  have hVQ : V ≤ pCore 2 d.overgroup := hVZ.trans
    ((omegaOrbit_le_centralOmega d.radical (h.replacement_core_le d)
      (h.replacement_core_selfCentralizing d)).trans (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1))
  have hVS := hVQ.trans (h.replacement_core_le d)
  let : IsElementaryAbelian 2 (omegaOrbit d.radical) := omegaOrbit_elementary d.radical
    (h.replacement_core_le d) (h.replacement_core_selfCentralizing d)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVZ
  have hcentral : V ≤ centralizer (pCore 2 d.overgroup : Set d.overgroup) :=
    Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)
  have hnorm : d.radical ≤ normalizer (V : Set d.overgroup) := by
    have : V.Normal := inferInstance
    rw [normalizer_eq_top]
    exact le_top
  obtain ⟨A,hA,hAQ,hmax,hquad⟩ := Glauberman.exists_quadratic_maximum_abelian_outside
    d.radical (pCore 2 d.overgroup) V (h.replacement_two_group d) hVS inferInstance
    hnorm hcentral (h.replacement_all_abelian_thompson_not_le d)
  have hindex := Glauberman.maximum_abelian_offender_bound hA hVS hVQ inferInstance hcentral
  rw [inf_relIndex_left] at hindex
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  refine ⟨A.map j,?_,?_,?_,?_⟩
  · rw [←hjR]
    exact Glauberman.maximum_abelian_map_of_injective j hj hA
  · rw [←hjQ,map_le_map_iff_of_injective hj]
    exact hAQ
  · rw [←hjU,←map_commutator,←map_commutator,hquad,Subgroup.map_bot]
  · rw [←hjU,←hjQ,Subgroup.SmallMover.centralizer_index_map j hj,
      relIndex_map_map_of_injective _ _ hj]
    exact hindex

/-- Thompson replacement supplies a genuine nontrivial small mover on
the literal edge, at every original field degree. -/
theorem Input.replacement_exists_quadratic_small_mover
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ A : Subgroup (FreeAmalgam d.radical),
      A ∈ thompsonAbelianSubgroups (Q d.radical t) ∧
      ¬ A ≤ Q d.radical a ∧
      ⁅⁅U d.radical a,A⁆,A⁆ = ⊥ ∧
      Subgroup.SmallMover.Admissible (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) A := by
  obtain ⟨A,hA,hAQ,hquad,hindex⟩ := h.replacement_quadratic_maximum_abelian d ha hat
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ stabilizer d.radical a := by
    rw [←hjr,←hjR]
    exact map_le_range j _
  exact ⟨A,hA,hAQ,hquad,hA.1,hindex,
    h.replacement_quadratic_moving_index_le_square d geometry hb ha A (hA.1.trans hTS) hquad⟩

/-- The literal small-mover join escapes Q. This supplies the nonzero
image premise in the unique-maximum branch of MS93 (5.4). -/
theorem Input.replacement_small_mover_join_not_le_kernel
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ¬ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2) ≤ Q d.radical a := by
  obtain ⟨A,hA,hAQ,hquad,hsmall⟩ := h.replacement_exists_quadratic_small_mover d geometry hb ha hat
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hAi : A ≤ j.range := hA.1.trans (hjR ▸ map_le_range j d.radical)
  have hAm : (A.comap j).map j = A := map_comap_eq_self hAi
  have hsmall' : Subgroup.SmallMover.Admissible (Sp4Four.LocalPackage.initialLayer d.radical)
      (pCore 2 d.overgroup) d.radical (Nat.card F ^ 2) (A.comap j) := by
    apply (Subgroup.SmallMover.admissible_map_iff j hj _ _ _ _ _).mp
    rwa [hjU,hjQ,hjR,hAm]
  have hn : ¬ A.comap j ≤ pCore 2 d.overgroup := by
    intro hh
    have hm := map_mono (f := j) hh
    rw [hAm,hjQ] at hm
    exact hAQ hm
  have hescape := join_not_le_of_admissible (Sp4Four.LocalPackage.initialLayer d.radical)
    (pCore 2 d.overgroup) d.radical (A.comap j) (Nat.card F ^ 2)
    (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)) hsmall' hn
  intro hJ
  apply hescape
  apply (map_le_map_iff_of_injective hj).mp
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit

private theorem image_card_le_mul_of_subset_mul
    {G D : Type*} [Group G] [Group D] [Finite D]
    (J A B : Subgroup G) (f : G →* D)
    (hprod : (J : Set G) ⊆ (A : Set G) * (B : Set G)) :
    Nat.card (J.map f) ≤ Nat.card (A.map f) * Nat.card (B.map f) := by
  have hp : (J.map f : Set D) ⊆ (A.map f : Set D) * (B.map f : Set D) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨a,ha,b,hb,rfl⟩ := hprod hx
    exact ⟨f a,mem_map_of_mem f ha,f b,mem_map_of_mem f hb,(map_mul f a b).symm⟩
  exact (Nat.card_le_card_of_injective (Set.inclusion hp) (Set.inclusion_injective hp)).trans
    Set.natCard_mul_le

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A failure of source (5.1) has a unique maximum small mover. Its full
quotient has order at most q², and it normalizes both full fixed seeds.
This is a consequence of a failed exclusion, not an exclusion theorem. -/
theorem Input.replacement_root_product_unique_maximum
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hprod : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical))) :
    ∃ J : Subgroup (FreeAmalgam d.radical),
      Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2) = {J} ∧
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2) = J ∧
      (Q d.radical a).relIndex J ≤ Nat.card F ^ 2 ∧
      J ≤ normalizer ((Z d.radical a ⊓ centralizer (E₁ : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical a ⊓ centralizer (E₂ : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  let S := stabilizer d.radical a
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hQS]
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hES₁ := hE₁.trans hTS
  have hES₂ := hE₂.trans hTS
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hcard (B : Subgroup (FreeAmalgam d.radical)) (hBS : B ≤ S) :
      Nat.card ((B.subgroupOf S).map f) = (Q d.radical a).relIndex B := by
    rw [←relIndex_ker,hQeq,relIndex_subgroupOf hBS]
  have hp : (J.subgroupOf S : Set S) ⊆ (E₁.subgroupOf S : Set S) * (E₂.subgroupOf S : Set S) := by
    intro x hx
    obtain ⟨y,hy,z,hz,he⟩ := hprod hx
    exact ⟨⟨y,hES₁ hy⟩,hy,⟨z,hES₂ hz⟩,hz,Subtype.ext he⟩
  have hbound := image_card_le_mul_of_subset_mul (J.subgroupOf S)
    (E₁.subgroupOf S) (E₂.subgroupOf S) f hp
  rw [hcard J hJS,hcard E₁ hES₁,hcard E₂ hES₂,hc₁,hc₂,←pow_two] at hbound
  have hn₁ := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb
    ha hat E₁ hE₁ hi₁.le
  have hn₂ := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb
    ha hat E₂ hE₂ hi₂.le
  rcases h.replacement_small_mover_dichotomy d geometry hb ha hat with ⟨A,hA,hJA⟩ | ⟨_,hJT,hcube⟩
  · exact ⟨A,hA,hJA,hJA ▸ hbound,hJA ▸ hn₁,hJA ▸ hn₂⟩
  · change (Q d.radical a).relIndex J ≤ Nat.card F ^ 2 at hbound
    change J = Q d.radical t at hJT
    rw [hJT,hcube] at hbound
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact False.elim ((pow_lt_pow_right₀ hq (by decide : 2 < 3)).not_ge hbound)

/-- Source (5.1) holds on the entire multiple-maximum branch of the
actual replacement. The remaining pushing-up argument is the unique branch. -/
theorem Input.replacement_root_product_excluded_of_multiple_movers
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    {A B : Subgroup (FreeAmalgam d.radical)}
    (hA : A ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2))
    (hB : B ∈ Subgroup.SmallMover.Maximal (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)) (hne : A ≠ B)
    (E₁ E₂ : Subgroup (FreeAmalgam d.radical))
    (hE₁ : E₁ ≤ Q d.radical t) (hE₂ : E₂ ≤ Q d.radical t)
    (hc₁ : (Q d.radical a).relIndex E₁ = Nat.card F)
    (hc₂ : (Q d.radical a).relIndex E₂ = Nat.card F)
    (hi₁ : (centralizer (E₁ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F)
    (hi₂ : (centralizer (E₂ : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) = Nat.card F) :
    ¬ (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F ^ 2) : Set (FreeAmalgam d.radical)) ⊆
      (E₁ : Set (FreeAmalgam d.radical)) * (E₂ : Set (FreeAmalgam d.radical)) := by
  intro hp
  obtain ⟨J,hJ,_⟩ := h.replacement_root_product_unique_maximum d geometry hb ha hat
    E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hp
  have hAJ : A = J := Set.mem_singleton_iff.mp (hJ ▸ hA)
  have hBJ : B = J := Set.mem_singleton_iff.mp (hJ ▸ hB)
  exact hne (hAJ.trans hBJ.symm)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
