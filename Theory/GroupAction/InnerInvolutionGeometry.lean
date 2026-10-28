module

public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.IsPerfect

/-!
# Inner involutions, Sylow centers, and embedded fixed residuals

In a centerless group, an inner involutory automorphism has a unique
conjugating element of order two. If it fixes a Sylow two-subgroup pointwise,
that element normalizes the Sylow subgroup and lies in its center: a
p-element in a Sylow normalizer belongs to the Sylow subgroup.

Containment of the full fixed subgroup in a local overgroup identifies the
residuals after both are embedded in the ambient group. The element version
uses the actual centralizer inside the overgroup, without asserting ambient
normality. These are elementary transport steps for Aschbacher–Smith,
16.1.4(1) and 16.1.6, printed pp.1171–1172 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace MulAut
variable {G : Type*} [Group G]

def embeddedFixedResidual (p : ℕ) (a : MulAut G) : Subgroup G :=
  (pResidual p a.fixedSubgroup).map a.fixedSubgroup.subtype

theorem embeddedFixedResidual_eq_local (p : ℕ) (a : MulAut G) (P : Subgroup G)
    (h : a.fixedSubgroup ≤ P) :
    embeddedFixedResidual p a =
      ((pResidual p (a.fixedSubgroup.subgroupOf P)).map
        (a.fixedSubgroup.subgroupOf P).subtype).map P.subtype := by
  have he := map_pResidual p (subgroupOfEquivOfLe h)
  have hm := congrArg (fun K : Subgroup a.fixedSubgroup =>
    K.map a.fixedSubgroup.subtype) he
  rw [map_map] at hm
  change _ = (pResidual p a.fixedSubgroup).map a.fixedSubgroup.subtype at hm
  rw [embeddedFixedResidual, ← hm, map_map]
  rfl

theorem conj_orderOf_of_center_eq_bot (hc : center G = ⊥) (x : G) :
    orderOf (conj x) = orderOf x :=
  orderOf_injective (conj : G →* MulAut G) (conj_injective_of_center_eq_bot hc) x

theorem inner_involution_representative (hc : center G = ⊥) (a : MulAut G)
    (ha : orderOf a = 2) (hi : ∃ x : G, a = conj x) :
    ∃ x : G, orderOf x = 2 ∧ a = conj x ∧ a.fixedSubgroup = centralizer {x} := by
  obtain ⟨x, rfl⟩ := hi
  exact ⟨x, (conj_orderOf_of_center_eq_bot hc x).symm.trans ha, rfl, fixedSubgroup_conj x⟩


theorem involution_mem_sylow_of_centralizes (S : Sylow 2 G) (x : G)
    (hx : x ^ 2 = 1) (hfix : ∀ y ∈ S, conj x y = y) :
    x ∈ S ∧ ∀ y ∈ S, Commute x y := by
  have hc : x ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (mul_inv_eq_iff_eq_mul.mp (hfix y hy)).symm
  have hn : x ∈ normalizer (S : Set G) := centralizer_le_normalizer _ hc
  have hp := (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx).isPGroup 2 _
  have hxI : x ∈ zpowers x ⊓ normalizer (S : Set G) := ⟨mem_zpowers x, hn⟩
  rw [hp.inf_normalizer_sylow S] at hxI
  exact ⟨hxI.2, fun y hy => (mem_centralizer_iff.mp hc y hy).symm⟩

theorem inner_involution_fixing_sylow (hc : center G = ⊥) (S : Sylow 2 G)
    (a : MulAut G) (ha : orderOf a = 2) (hi : ∃ x : G, a = conj x)
    (hfix : ∀ y ∈ S, a y = y) :
    ∃ x : G, orderOf x = 2 ∧ a = conj x ∧ x ∈ S ∧
      ∀ y ∈ S, Commute x y := by
  obtain ⟨x, hx, he, _⟩ := inner_involution_representative hc a ha hi
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨hS, hcomm⟩ := involution_mem_sylow_of_centralizes S x hx2 (he ▸ hfix)
  exact ⟨x, hx, he, hS, hcomm⟩

end MulAut

namespace Subgroup
variable {G : Type*} [Group G] [IsSimpleGroup G] [Group.IsPerfect G]
theorem center_eq_bot_of_simple_perfect : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative G (center_eq_top_iff.mp h)).elim
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G]

theorem centralizer_subgroupOf_singleton (P : Subgroup G) (x : P) :
    (centralizer ({(x : G)} : Set G)).subgroupOf P = centralizer ({x} : Set P) := by
  ext y
  simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem embedded_centralizer_residual_eq_local (p : ℕ) (P : Subgroup G) (x : P)
    (hc : centralizer ({(x : G)} : Set G) ≤ P) :
    (pResidual p (centralizer ({(x : G)} : Set G))).map
        (centralizer ({(x : G)} : Set G)).subtype =
      ((pResidual p (centralizer ({x} : Set P))).map
        (centralizer ({x} : Set P)).subtype).map P.subtype := by
  have h := MulAut.embeddedFixedResidual_eq_local p (MulAut.conj (x : G)) P
    (by rwa [MulAut.fixedSubgroup_conj])
  unfold MulAut.embeddedFixedResidual at h
  rw [MulAut.fixedSubgroup_conj] at h
  rw [centralizer_subgroupOf_singleton] at h
  exact h
end Subgroup

namespace MulAut
variable {G : Type*} [Group G]
theorem inner_involution_fixing_sylow_center (hc : center G = ⊥) (S : Sylow 2 G)
    (a : MulAut G) (ha : orderOf a = 2) (hi : ∃ x : G, a = conj x)
    (hfix : ∀ y ∈ S, a y = y) :
    ∃ x : (S : Subgroup G), x ∈ center (S : Subgroup G) ∧ orderOf (x : G) = 2 ∧ a = conj (x : G) := by
  obtain ⟨x, hx, he, hS, hcomm⟩ := inner_involution_fixing_sylow hc S a ha hi hfix
  refine ⟨⟨x, hS⟩, ?_, hx, he⟩
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (hcomm y y.property).eq.symm
end MulAut

end
