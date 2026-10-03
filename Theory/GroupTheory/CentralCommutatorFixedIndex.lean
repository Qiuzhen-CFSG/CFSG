module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Fixed subgroups for commutators in a central involution

If [A,G] is contained in the center of order two, every element that does
not centralize A has a fixed subgroup of index two in A. The central
commutator map a ↦ [x,a] is a homomorphism onto the center, with kernel
C_A(x). This supplies the fixed-hyperplane calculation in Parrott's
characterization of the Tits group (1972), p.673, property (a).
-/

open scoped commutatorElement
namespace Subgroup

/-- A nontrivial action with commutators in a central group of order two
has fixed subgroup of index two. -/
public theorem centralizer_relIndex_eq_two_of_commutator_le_center
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hcomm : ⁅A, ⊤⁆ ≤ center G)
    (hcenter : Nat.card (center G) = 2)
    (x : G) (hx : x ∉ centralizer (A : Set G)) :
    (centralizer ({x} : Set G)).relIndex A = 2 := by
  classical
  have hvalue (a : A) : ⁅x, (a : G)⁆ ∈ center G := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top x) a.property
  let f : A →* center G := {
    toFun := fun a => ⟨⁅x, (a : G)⁆, hvalue a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅x, (a : G) * (b : G)⁆ = ⁅x, (a : G)⁆ * ⁅x, (b : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := mem_center_iff.mp (hvalue b) (a : G)
      calc
        _ = ⁅x, (a : G)⁆ * ((a : G) * ⁅x, (b : G)⁆) * (a : G)⁻¹ := by group
        _ = _ := by rw [hc]; group }
  have hker : f.ker = (centralizer ({x} : Set G)).subgroupOf A := by
    ext a
    change (⟨⁅x, (a : G)⁆, hvalue a⟩ : center G) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅x, (a : G)⁆ = 1 ↔ (a : G) ∈ centralizer ({x} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
    exact eq_comm
  have hne : f.range ≠ ⊥ := by
    intro hbot
    apply hx
    intro a ha
    have hh : f ⟨a, ha⟩ = 1 := by
      have hm : f ⟨a, ha⟩ ∈ f.range := ⟨⟨a, ha⟩, rfl⟩
      simpa only [hbot, mem_bot] using hm
    have hz : ⁅x, a⁆ = 1 := congrArg Subtype.val hh
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  have hcard : Nat.card f.range = 2 := by
    have hdvd := f.range.card_subgroup_dvd_card
    rw [hcenter] at hdvd
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with hone | htwo
    · exact (hne (card_eq_one.mp hone)).elim
    · exact htwo
  change ((centralizer ({x} : Set G)).subgroupOf A).index = 2
  rw [← hker, index_ker]
  exact hcard

end Subgroup
