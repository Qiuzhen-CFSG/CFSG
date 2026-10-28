module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

/-!
# A central commutator row and its actual image bound

If [t,G] is central, x↦[t,x] is a homomorphism with kernel C_G(t)
and image [⟨t⟩,G]. Every action kernel centralizing t therefore bounds
the order of this image by the actual action image. The ambient-subgroup
version needs only finiteness of the acting subgroup.
Source: Aschbacher–Smith, D.1.4, printed p.176, the single-vector bound.
-/

@[expose] public section
namespace Subgroup.CentralRow
open scoped commutatorElement
variable {G : Type*} [Group G]
def commutatorHom (t : G) (hc : ⁅zpowers t,(⊤ : Subgroup G)⁆ ≤ center G) : G →* G where
  toFun x := ⁅t, x⁆
  map_one' := by simp
  map_mul' x y := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hcent := mem_center_iff.mp
      (hc (commutator_mem_commutator (mem_zpowers t) (mem_top y))) x
    calc
      _ = ⁅t,x⁆ * (x * ⁅t,y⁆) * x⁻¹ := by group
      _ = ⁅t,x⁆ * ⁅t,y⁆ := by rw [hcent]; group

theorem commutatorHom_ker (t : G) (hc : ⁅zpowers t,(⊤ : Subgroup G)⁆ ≤ center G) :
    (commutatorHom t hc).ker = centralizer ({t} : Set G) := by
  ext x
  change ⁅t,x⁆ = 1 ↔ _
  rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff, eq_comm]

theorem commutatorHom_range (t : G) (hc : ⁅zpowers t,(⊤ : Subgroup G)⁆ ≤ center G) :
    (commutatorHom t hc).range = ⁅zpowers t, (⊤ : Subgroup G)⁆ := by
  let f := commutatorHom t hc
  have hcentral : f.range ≤ center G := by
    rintro _ ⟨x, rfl⟩
    exact hc (commutator_mem_commutator (mem_zpowers t) (mem_top x))
  let : f.range.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hcentral hx) g, mul_inv_cancel_right]
    exact hx⟩
  let π := QuotientGroup.mk' f.range
  have ht (x : G) : Commute (π t) (π x) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact commutator_mem_commutator (mem_zpowers t) (mem_top x)
  · apply commutator_le.mpr
    intro y hy x _
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅t ^ n, x⁆ = 1
    rw [map_commutatorElement, map_zpow]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((ht x).zpow_left n).eq

theorem card_commutator_le_range [Finite G] {A : Type*} [Group A]
    (t : G) (hc : ⁅zpowers t,(⊤ : Subgroup G)⁆ ≤ center G)
    (f : G →* A) (hf : f.ker ≤ centralizer ({t} : Set G)) :
    Nat.card (⁅zpowers t,(⊤ : Subgroup G)⁆ : Subgroup G) ≤ Nat.card f.range := by
  rw [← commutatorHom_range t hc, ← index_ker, ← index_ker]
  exact index_antitone ((commutatorHom_ker t hc).symm ▸ hf)
end Subgroup.CentralRow

namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]
theorem card_central_commutator_le_range {A : Type*} [Group A]
    (Q : Subgroup G) [Finite Q] {v : G} (hv : v ∈ Q)
    (hc : ⁅zpowers v,Q⁆ ≤ centralizer (Q : Set G))
    (f : Q →* A) (hf : ∀ q ∈ f.ker, Commute v (q : G)) :
    Nat.card (⁅zpowers v,Q⁆ : Subgroup G) ≤ Nat.card f.range := by
  let t : Q := ⟨v,hv⟩
  have hm : (⁅zpowers t,(⊤ : Subgroup Q)⁆ : Subgroup Q).map Q.subtype = ⁅zpowers v,Q⁆ := by
    rw [map_commutator, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hcent : ⁅zpowers t,(⊤ : Subgroup Q)⁆ ≤ center Q := by
    intro x hx
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact hc (hm ▸ mem_map_of_mem Q.subtype hx) q q.property
  have hk : f.ker ≤ centralizer ({t} : Set Q) := by
    intro q hq
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (hf q hq).eq.symm
  rw [← hm, card_map_of_injective Q.subtype_injective]
  exact CentralRow.card_commutator_le_range t hcent f hk
end Subgroup

