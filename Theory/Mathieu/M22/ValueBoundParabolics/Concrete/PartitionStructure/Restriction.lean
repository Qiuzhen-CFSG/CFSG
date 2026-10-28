module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupTheory.SymmetricThreeTwoCore
/-!
# Restricting the marked M₂₂ partition to its hexad

The partition stabilizer lies in the genuine hexad stabilizer. Restriction
identifies it, and its intersection with the marked-pair stabilizer, with
preimages of explicit subgroups of the alternating group on the six hexad
points. The restriction kernel has order sixteen by the hexad extension.
The standard odd design involution preserves both configurations, giving an
index-two passage to the corresponding full design stabilizers.

These are the geometric reductions for Aschbacher–Smith E.4.3(2), printed
pp. 241–242. The finite image calculations are supplied separately.
-/

@[expose] public section
open scoped Pointwise
open Subgroup
namespace Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure

def onFinset {G A : Type*} [Group G] [MulAction G A] [DecidableEq A]
    (s : Finset A) : MulAction.stabilizer G s →* Equiv.Perm s where
  toFun g := (MulAction.toPerm g.val).subtypePerm
    (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; exact one_smul G a.val
  map_mul' g h := by ext a; exact mul_smul g.val h.val a.val

def smallGroup : Subgroup (Equiv.Perm m22Hexad123) :=
  ((MulAction.stabilizer (Equiv.Perm (Fin 22)) hexadPartition).comap
    Equiv.Perm.ofSubtype) ⊓ alternatingGroup m22Hexad123

instance : DecidablePred (· ∈ smallGroup) := fun g =>
  inferInstanceAs (Decidable ((Equiv.Perm.ofSubtype g • hexadPartition = hexadPartition) ∧ Equiv.Perm.sign g = 1))

def smallAction : smallGroup →* Equiv.Perm hexadPartition :=
  (onFinset hexadPartition).comp
    (Equiv.Perm.ofSubtype.restrict (fun _ h => h.1))


def smallMarked : Subgroup (Equiv.Perm m22Hexad123) :=
  smallGroup ⊓ ((MulAction.stabilizer (Equiv.Perm (Fin 22)) m22Pair12).comap
    Equiv.Perm.ofSubtype)
instance : DecidablePred (· ∈ smallMarked) := fun g =>
  inferInstanceAs (Decidable (g ∈ smallGroup ∧ Equiv.Perm.ofSubtype g • m22Pair12 = m22Pair12))

theorem card_comap_of_le_range {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (K : Subgroup H) (hK : K ≤ f.range) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have hc := (K.comap f).card_mul_index
  have hr := f.ker.card_mul_index
  have hk := (K.subgroupOf f.range).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at hk
  rw [Subgroup.index_comap] at hc
  rw [Subgroup.index_ker] at hr
  have hn : K.relIndex f.range ≠ 0 := by
    rw [← Subgroup.index_comap]
    exact Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn)
  calc
    Nat.card (K.comap f) * K.relIndex f.range = Nat.card G := hc
    _ = Nat.card f.ker * Nat.card f.range := hr.symm
    _ = (Nat.card f.ker * Nat.card K) * K.relIndex f.range := by
      rw [← hk]; exact (Nat.mul_assoc _ _ _).symm

theorem second_le_hexad : second ≤ (MulAction.stabilizer M22 m22Hexad123) := by
  intro g hg
  change g • m22Hexad123 = m22Hexad123
  rw [← hexadPartition_union]
  have h : g • hexadPartition.biUnion id = (g • hexadPartition).biUnion id := by
    simp only [Finset.smul_finset_def, Finset.image_biUnion, Finset.biUnion_image]
    rfl
  rw [h, MulAction.mem_stabilizer_iff.mp hg]

theorem subset_hexad_of_mem {s : Finset (Fin 22)} (hs : s ∈ hexadPartition) :
    s ⊆ m22Hexad123 := by
  rw [← hexadPartition_union]
  exact Finset.subset_biUnion_of_mem id hs

theorem restriction_agrees (g : (MulAction.stabilizer M22 m22Hexad123)) {s : Finset (Fin 22)}
    (hs : s ⊆ m22Hexad123) :
    Equiv.Perm.ofSubtype (m22SetAction m22Hexad123 g) • s = (g : M22) • s := by
  simp only [Finset.smul_finset_def]
  apply Finset.image_congr
  intro a ha
  exact Equiv.Perm.ofSubtype_apply_of_mem _ (hs ha)

theorem restriction_partition (g : (MulAction.stabilizer M22 m22Hexad123)) :
    Equiv.Perm.ofSubtype (m22SetAction m22Hexad123 g) • hexadPartition =
      (g : M22) • hexadPartition := by
  rw [Finset.smul_finset_def, Finset.smul_finset_def]
  apply Finset.image_congr
  intro s hs
  exact restriction_agrees g (subset_hexad_of_mem hs)

theorem restriction_range :
    (m22SetAction m22Hexad123).range = alternatingGroup m22Hexad123 := by
  have hr : Nat.card (m22SetAction m22Hexad123).range = 360 := by
    have h := (m22SetAction m22Hexad123).ker.card_mul_index
    rw [Subgroup.index_ker, m22HexadKernel_card m22Hexad123_mem,
      m22Hexad_stabilizer_card m22Hexad123_mem] at h
    omega
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h := (m22SetAction m22Hexad123).range.card_mul_index
  rw [hr] at h
  have hp : Nat.card (Equiv.Perm m22Hexad123) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide +kernel
  rw [hp] at h
  omega

theorem restriction_mem_alternating (g : (MulAction.stabilizer M22 m22Hexad123)) :
    m22SetAction m22Hexad123 g ∈ alternatingGroup m22Hexad123 := by
  rw [← restriction_range]
  exact ⟨g, rfl⟩

theorem second_preimage : smallGroup.comap (m22SetAction m22Hexad123) =
    second.subgroupOf (MulAction.stabilizer M22 m22Hexad123) := by
  ext g
  change (_ • hexadPartition = hexadPartition ∧ _ ∈ alternatingGroup _) ↔
    (g : M22) • hexadPartition = hexadPartition
  rw [restriction_partition, and_iff_left (restriction_mem_alternating g)]

theorem intersection_preimage : smallMarked.comap (m22SetAction m22Hexad123) =
    (first ⊓ second).subgroupOf (MulAction.stabilizer M22 m22Hexad123) := by
  ext g
  change ((_ • hexadPartition = hexadPartition ∧ _ ∈ alternatingGroup _) ∧
      _ • m22Pair12 = m22Pair12) ↔
    (g : M22) • m22Pair12 = m22Pair12 ∧ (g : M22) • hexadPartition = hexadPartition
  rw [restriction_partition,
    restriction_agrees g (subset_hexad_of_mem pair_mem_hexadPartition),
    and_iff_left (restriction_mem_alternating g), and_comm]

noncomputable def oddElement : m22DesignAut :=
  ⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩

theorem oddElement_mem : oddElement ∈ outerFirst ⊓ outerSecond := by
  constructor
  · change m22OddPairSwap • m22Pair12 = m22Pair12
    decide +kernel
  · change m22OddPairSwap • hexadPartition = hexadPartition
    decide +kernel

theorem inner_index : inner.index = 2 := by
  have hi : Nat.card inner = Nat.card M22 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe M22_le_m22DesignAut).toEquiv
  have hc := inner.card_mul_index
  rw [hi, m22_order, m22DesignAut_order] at hc
  omega

theorem outer_card_double (H : Subgroup m22DesignAut) (ho : oddElement ∈ H) :
    Nat.card H = Nat.card (H.comap inclusion) * 2 := by
  have hd : (inner.subgroupOf H).index ∣ 2 := by
    change inner.relIndex H ∣ 2
    rw [← inner_index]
    exact Subgroup.relIndex_dvd_index_of_normal inner H
  have hn : (inner.subgroupOf H).index ≠ 1 := by
    intro h
    have ht := Subgroup.index_eq_one.mp h
    have hm : (⟨oddElement, ho⟩ : H) ∈ inner.subgroupOf H := ht ▸ Subgroup.mem_top _
    exact m22OddPairSwap_not_mem_M22 hm
  have hi : (inner.subgroupOf H).index = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  have he : Nat.card (inner.subgroupOf H) = Nat.card (inner ⊓ H : Subgroup m22DesignAut) := by
    rw [← Subgroup.inf_subgroupOf_right inner H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hmap : (H.comap inclusion).map inclusion = inner ⊓ H := by
    rw [Subgroup.map_comap_eq, inclusion_range]
  have hm : Nat.card (inner ⊓ H : Subgroup m22DesignAut) = Nat.card (H.comap inclusion) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective inclusion_injective
  have hc := (inner.subgroupOf H).card_mul_index
  rw [hi, he, hm] at hc
  exact hc.symm

end Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
