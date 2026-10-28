module

public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.ThreeSubgroups

/-!
# Triviality of an action through an irreducible quotient by a line

Let Z have order two, with Z≤V and |V|>4. Suppose R acts irreducibly on
V/Z. If P fixes Z, displaces V into Z and commutes with R on V, then P
centralizes V. For p∈P, orbit counting gives |C_V(p)|>2. The three-subgroups
lemma makes this centralizer R-invariant, so irreducibility forces C_V(p)=V.
This does not require selecting a particular coprime-order actor.

Source application: the final action step of Aschbacher--Smith 12.9.9(1),
printed p.863 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- If R is irreducible on V/Z with |Z|=2 and |V|>4, an actor P
centralizing Z, acting trivially on V/Z and commuting with R on V
centralizes V. -/
theorem centralizes_of_irreducible_fixed_line
    (R P V Z : Subgroup G) (hZV : Z ≤ V) (hZ : Nat.card Z = 2)
    (hV : 4 < Nat.card V) (hRV : R ≤ normalizer (V : Set G))
    (hPZ : P ≤ centralizer (Z : Set G)) (hPV : ⁅P,V⁆ ≤ Z)
    (hRP : ⁅R,P⁆ ≤ centralizer (V : Set G))
    (hirr : ∀ B : Subgroup G, Z ≤ B → B ≤ V →
      R ≤ normalizer (B : Set G) → B = Z ∨ B = V) :
    P ≤ centralizer (V : Set G) := by
  intro p hp
  let B := V ⊓ centralizer ({p} : Set G)
  have hBZ : Z ≤ B := le_inf hZV (by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (hPZ hp z hz))
  have hBp : ⁅B,zpowers p⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [zpowers_eq_closure, centralizer_closure]
    exact inf_le_right
  have hprB : ⁅⁅zpowers p,R⁆,B⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm (zpowers p) R]
    exact ((commutator_mono le_rfl (zpowers_le.mpr hp)).trans hRP).trans
      (centralizer_le (show B ≤ V from inf_le_left))
  have hRBp : ⁅⁅R,B⁆,zpowers p⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rw [hBp, commutator_bot_left]) hprB
  have hRB : R ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply le_inf
    · exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp hRV)
    · have hh := commutator_eq_bot_iff_le_centralizer.mp hRBp
      rwa [zpowers_eq_closure, centralizer_closure] at hh
  have hcard : 2 < Nat.card B := by
    have hc := card_le_commutator_card_mul_centralizer V p
    have hcom : ⁅V,zpowers p⁆ ≤ Z := by
      rw [commutator_comm]
      exact (commutator_mono (zpowers_le.mpr hp) le_rfl).trans hPV
    have hsmall : Nat.card (⁅V,zpowers p⁆ : Subgroup G) ≤ 2 := by
      rw [← hZ]
      exact Nat.card_le_card_of_injective (inclusion hcom) (inclusion_injective _)
    have hsub : (centralizer ({p} : Set G)).subgroupOf V = B.subgroupOf V := by
      ext v
      change _ ↔ (v : G) ∈ V ∧ _
      exact ⟨fun hv => ⟨v.property,hv⟩,fun hv => hv.2⟩
    rw [hsub,Nat.card_congr (subgroupOfEquivOfLe (show B ≤ V from inf_le_left)).toEquiv] at hc
    have hbound := hc.trans (Nat.mul_le_mul_right (Nat.card B) hsmall)
    omega
  rcases hirr B hBZ inf_le_left hRB with hb | hb
  · rw [hb,hZ] at hcard
    omega
  · have hVC : V ≤ centralizer ({p} : Set G) := hb ▸ (show B ≤ centralizer ({p} : Set G) from inf_le_right)
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hVC hv)

end Subgroup
