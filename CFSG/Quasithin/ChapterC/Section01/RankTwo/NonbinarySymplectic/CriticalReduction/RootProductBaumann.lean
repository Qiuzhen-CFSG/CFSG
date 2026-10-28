module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProduct
public import Glauberman.SymplecticSmallMoverThompson
public import Glauberman.SmallMoverBaumann

/-!
# The actual Thompson and Baumann subgroups in the root-product branch

The q² bound from a putative product of two roots places every maximum
abelian subgroup of the replacement edge in its unique maximum small mover.
The fixed-centralizer argument then places the entire Baumann subgroup
there as well. MS3 makes this Baumann subgroup escape the actual Q-kernel,
and it normalizes both full root-fixed seeds.

These are the original-group inputs to the rank-one pushing-up construction
in MS93 (5.1), printed p.913. The construction of F₀, the pushing-up
conclusion, special parabolic generators and terminal exclusions remain
separate proof obligations. No distance-two assertion is made here, and
the original field degree and all central attachments are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Under the source q² bound, both the ordinary Thompson subgroup and
the Baumann subgroup of the actual edge lie in its maximum-small-mover join. -/
theorem Input.replacement_thompson_baumann_le_small_mover_join
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (hbound : (Q d.radical a).relIndex
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t)
        (Nat.card F ^ 2)) ≤ Nat.card F ^ 2) :
    thompsonSubgroup (Q d.radical t) ≤
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ∧
    Glauberman.baumannSubgroup (Q d.radical t) ≤
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier ^ 2)
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
  have hUQ : U d.radical a ≤ Q d.radical a := (U_le_Z a).trans
    (Z_le_Q_of_dist_lt d.radical a (geometry.exists_critical a ha) (by
      rw [SimpleGraph.dist_self,geometry.distance_constant a ha]
      change 0 < geometry.b d.radical
      omega))
  have hUk : U₀ ≤ f.ker := by rw [hQeq]; exact comap_mono hUQ
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (U_le_Z a)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUS
  have hUT : U₀.map S.subtype = U d.radical a := map_subgroupOf_eq_of_le hUS
  have hTT : T.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hUT,hfQ,hTT,hcard]
  have hbound' : f.ker.relIndex J ≤ Nat.card E.Carrier ^ 2 := by
    rw [←relIndex_map_map_of_injective f.ker J S.subtype_injective,hfQ,hjoin,hcard]
    exact hbound
  have hq : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hTh : thompsonSubgroup T ≤ J := Degree.Quotient.thompson_le_smallMover_join
    U₀ T f unipotent.subtype Subtype.val_injective hkT hUK
    (by simpa only [range_subtype] using hTf) hidx hq hUk hbound'
  have hJmax : J ∈ Subgroup.SmallMover.Maximal U₀ f.ker T (Nat.card E.Carrier ^ 2) := by
    rcases h.replacement_small_mover_dichotomy d geometry hb ha hat with ⟨A,hA,hJA⟩ | ⟨_,hJT,hcube⟩
    · apply (Subgroup.SmallMover.maximal_map_iff S.subtype S.subtype_injective _ _ _ _ _).mp
      rw [hUT,hfQ,hTT,hcard,hjoin,hJA,hA]
      exact Set.mem_singleton A
    · rw [hJT,hcube] at hbound
      have hqF : 1 < Nat.card F := Finite.one_lt_card
      exact False.elim ((pow_lt_pow_right₀ hqF (by decide : 2<3)).not_ge hbound)
  have hB := Glauberman.baumann_le_maximum_smallMover U₀ f.ker T J _ (hUk.trans hkT) hTh hJmax
  have hThmap := map_mono (f := S.subtype) hTh
  have hBmap := map_mono (f := S.subtype) hB
  rw [Glauberman.thompson_map_injective T S.subtype S.subtype_injective,hTT,hjoin] at hThmap
  rw [Glauberman.baumann_map_injective T S.subtype S.subtype_injective,hTT,hjoin] at hBmap
  exact ⟨hThmap,hBmap⟩

omit [Finite F] [CharP F 2] in
/-- The actual Baumann subgroup escapes Q by MS3 and the ordinary
Thompson subgroup, before making any source root-product assumption. -/
theorem Input.replacement_baumann_not_le_kernel
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ¬ Glauberman.baumannSubgroup (Q d.radical t) ≤ Q d.radical a := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  intro hB
  apply h.replacement_all_abelian_thompson_not_le d
  apply (map_le_map_iff_of_injective hj).mp
  rw [Glauberman.thompson_map_injective _ j hj,hjR,hjQ]
  exact (Glauberman.thompson_le_baumann _).trans hB

/-- The actual root-product premise of (5.1) places the original Baumann
subgroup in the unique maximum mover, retaining the full Q-kernel. -/
theorem Input.replacement_root_product_baumann_control
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
      thompsonSubgroup (Q d.radical t) ≤ J ∧
      Glauberman.baumannSubgroup (Q d.radical t) ≤ J ∧
      ¬ Glauberman.baumannSubgroup (Q d.radical t) ≤ Q d.radical a ∧
      Glauberman.baumannSubgroup (Q d.radical t) ≤
        normalizer ((Z d.radical a ⊓ centralizer (E₁ : Set (FreeAmalgam d.radical)) :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      Glauberman.baumannSubgroup (Q d.radical t) ≤
        normalizer ((Z d.radical a ⊓ centralizer (E₂ : Set (FreeAmalgam d.radical)) :
          Subgroup (FreeAmalgam d.radical)) : Set _) := by
  obtain ⟨J,hJ,hjoin,hbound,hn₁,hn₂⟩ := h.replacement_root_product_unique_maximum d geometry hb
    ha hat E₁ E₂ hE₁ hE₂ hc₁ hc₂ hi₁ hi₂ hprod
  have hh := h.replacement_thompson_baumann_le_small_mover_join d geometry hb ha hat
    (by rwa [hjoin])
  rw [hjoin] at hh
  exact ⟨J,hJ,hjoin,hh.1,hh.2,h.replacement_baumann_not_le_kernel d ha hat,
    hh.2.trans hn₁,hh.2.trans hn₂⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
