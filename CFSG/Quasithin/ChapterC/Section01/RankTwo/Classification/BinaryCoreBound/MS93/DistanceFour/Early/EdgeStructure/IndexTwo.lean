module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Displacement from a fixed subgroup of index two

For an abelian subgroup U normalized by P, suppose every displacement is
fixed by P and the common fixed subgroup has index two in U. Evaluation at
any point outside that fixed subgroup defines a homomorphism on P. Its
kernel is C_P(U), and its image is the entire commutator [U,P]. This proves
the equality of their orders using the actual ambient commutator.

The lemma needs no finite ambient group. It supplies the binary edge-index
calculation in Meierfrankenfeld--Stellmacher (1993), the first (4.6.6), p.903.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early

/-- Evaluation outside the fixed subgroup identifies the faithful actor quotient
with the displacement group. -/
theorem actor_index_eq_displacement_card_of_fixed_index_two
    {G : Type*} [Group G] (U P : Subgroup G) [IsMulCommutative U]
    (hn : P ≤ normalizer (U : Set G))
    (hc : ⁅U, P⁆ ≤ centralizer (P : Set G))
    (hi : (U ⊓ centralizer (P : Set G)).relIndex U = 2) :
    (centralizer (U : Set G)).relIndex P = Nat.card (⁅U, P⁆ : Subgroup G) := by
  let C := U ⊓ centralizer (P : Set G)
  let F := C.subgroupOf U
  obtain ⟨u, hu, _⟩ := (F.index_eq_two_iff_exists_notMem_and).mp hi
  have hKU : ⁅U, P⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hn
  have hmem (p : P) : ⁅(p : G), (u : G)⁆ ∈ ⁅U, P⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator p.property u.property
  have hformula (p : P) (v : G) (hv : v ∈ U) :
      ⁅(p : G), v⁆ = 1 ∨ ⁅(p : G), v⁆ = ⁅(p : G), (u : G)⁆ := by
    by_cases hvC : v ∈ C
    · exact Or.inl (commutatorElement_eq_one_iff_mul_comm.mpr (hvC.2 p p.property))
    · right
      have hd : v * (u : G)⁻¹ ∈ C := by
        have hd' : (⟨v, hv⟩ : U) * u⁻¹ ∈ F := by
          rw [mul_mem_iff_of_index_two hi]
          change (v ∈ C ↔ (u : G)⁻¹ ∈ C)
          simp only [inv_mem_iff, hvC, show (u : G) ∉ C from hu]
        exact hd'
      calc
        ⁅(p : G), v⁆ = ⁅(p : G), (v * (u : G)⁻¹) * (u : G)⁆ := by
          rw [inv_mul_cancel_right]
        _ = ⁅(p : G), (u : G)⁆ := by
          rw [commutatorElement_mul_right_eq_mul_conj,
            commutatorElement_eq_one_iff_mul_comm.mpr (hd.2 p p.property), one_mul,
            setLike_mul_comm hd.1 (hKU (hmem p)), mul_inv_cancel_right]
  let f : P →* G := {
    toFun := fun p => ⁅(p : G), (u : G)⁆
    map_one' := commutatorElement_one_left _
    map_mul' := by
      intro p q
      change ⁅(p : G) * (q : G), (u : G)⁆ =
        ⁅(p : G), (u : G)⁆ * ⁅(q : G), (u : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        (hc (hmem q)) p p.property, mul_inv_cancel_right,
        setLike_mul_comm (hKU (hmem q)) (hKU (hmem p))] }
  have hrange : f.range = ⁅U, P⁆ := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact hmem p
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro p hp v hv
      rcases hformula ⟨p, hp⟩ v hv with h | h
      · rw [h]
        exact f.range.one_mem
      · exact ⟨⟨p, hp⟩, h.symm⟩
  have hker : f.ker = (centralizer (U : Set G)).subgroupOf P := by
    ext p
    change ⁅(p : G), (u : G)⁆ = 1 ↔ (p : G) ∈ centralizer (U : Set G)
    constructor
    · intro hp v hv
      have hh : ⁅(p : G), v⁆ = 1 := (hformula p v hv).elim id (fun h => h.trans hp)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    · intro hp
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hp u u.property).symm
  change ((centralizer (U : Set G)).subgroupOf P).index = _
  rw [← hker, index_ker, hrange]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
