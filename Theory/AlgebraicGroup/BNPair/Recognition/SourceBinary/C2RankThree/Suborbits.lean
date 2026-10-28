module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.DoubleCosets
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.CosetAction
public import Mathlib.Tactic.Group

/-!
# Rank and subdegrees of the original C₂ coset action

Inversion takes the source right coset P₂x to the left coset x⁻¹P₂.
A fiber count therefore converts the actual parabolic double-coset counts
into subdegrees q(q+1) and q³. The opposite orbit is exactly the complement
of the fixed point and neighboring orbit. The chosen simple lift exchanges
the first two points because its square is in the full Borel; no involutory
lift or additional representative choice is assumed. These proofs include q=2.

The internal `import all CosetAction` is confined to this extension of the
same family: it unfolds the private body of the existing source-coset
convention in proofs. Public names and re-exports remain unchanged.

Source: Fong–Seitz I (1I), pp.5–6, and II (7C), p.193.
The kernel-root fixation and projective coordinatization are subsequent
obligations, not conclusions of the orbit count.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree

private theorem right_coset_mem_orbit {G : Type*} [Group G] (H : Subgroup G) (n x : G) :
    (QuotientGroup.mk x⁻¹ : G ⧸ H) ∈ orbit H (QuotientGroup.mk n⁻¹ : G ⧸ H) ↔
      x ∈ DoubleCoset.doubleCoset n H H := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨⟨h,hh⟩,he⟩
    have hc : n*h⁻¹*x⁻¹ ∈ H := by
      have he' := QuotientGroup.eq.mp he
      change (h*n⁻¹)⁻¹*x⁻¹ ∈ H at he'
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using he'
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨(n*h⁻¹*x⁻¹)⁻¹,H.inv_mem hc,h⁻¹,H.inv_mem hh,by group⟩
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    refine ⟨⟨b⁻¹,H.inv_mem hb⟩,?_⟩
    apply QuotientGroup.eq.mpr
    change (b⁻¹*n⁻¹)⁻¹*(a*n*b)⁻¹ ∈ H
    simpa only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,
      mul_one] using H.inv_mem ha

private theorem right_coset_preimage_card {G : Type*} [Group G] (H : Subgroup G)
    (C : Set (G ⧸ H)) :
    Nat.card {x : G // (QuotientGroup.mk x⁻¹ : G ⧸ H) ∈ C} = Nat.card C * Nat.card H := by
  let e : G ≃ (G ⧸ H) × H := (Equiv.inv G).trans groupEquivQuotientProdSubgroup
  have he (x : G) : (e x).1 = (QuotientGroup.mk x⁻¹ : G ⧸ H) := by rfl
  let f : {x : G // (QuotientGroup.mk x⁻¹ : G ⧸ H) ∈ C} ≃
      {z : (G ⧸ H) × H // z.1 ∈ C} :=
    e.subtypeEquiv (fun x => by rw [he])
  exact (Nat.card_congr (f.trans Equiv.prodSubtypeFstEquivSubtypeProd)).trans (Nat.card_prod _ _)

/-- Right cosets are left cosets after inversion; every orbit fiber has size |H|. -/
theorem right_coset_orbit_card_mul {G : Type*} [Group G] (H : Subgroup G) (n : G) :
    Nat.card (orbit H (QuotientGroup.mk n⁻¹ : G ⧸ H)) * Nat.card H =
      Nat.card (DoubleCoset.doubleCoset n H H) := by
  rw [← right_coset_preimage_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (right_coset_mem_orbit H n))

open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P)

/-- The stabilizer is the literal second marked parabolic. -/
theorem base_stabilizer : stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1) =
    Q.tits.standardParabolic {Q.simple 1} := by
  unfold rightCosetPoint
  change stabilizer (X ⧸ Q.D) (QuotientGroup.mk (1 : X ⧸ Q.D)⁻¹ : Points Q 1) = _
  rw [inv_one,stabilizer_quotient]

/-- The representative of the neighboring suborbit in the source convention. -/
@[expose] def neighborPoint : Points Q 1 :=
  rightCosetPoint Q 1 (representative (Q.simple 0))

/-- The representative of the opposite suborbit in the source convention. -/
@[expose] def oppositePoint : Points Q 1 :=
  rightCosetPoint Q 1 (representative (longest Q))

/-- Membership in a source suborbit is membership in its original right double coset. -/
theorem source_orbit_mem (n x : X ⧸ Q.D) :
    rightCosetPoint Q 1 x ∈
      orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (rightCosetPoint Q 1 n) ↔
        x ∈ DoubleCoset.doubleCoset n (Q.tits.standardParabolic {Q.simple 1})
          (Q.tits.standardParabolic {Q.simple 1}) := by
  rw [base_stabilizer]
  unfold rightCosetPoint
  exact right_coset_mem_orbit _ n x

/-- The opposite suborbit is precisely the complement of the fixed point
and the neighboring suborbit: the original action has rank three. -/
theorem opposite_orbit_eq_compl (hm : rotationOrder Q = 4) :
    orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (oppositePoint Q) =
      (insert (rightCosetPoint Q 1 1)
        (orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)))ᶜ := by
  ext x
  have hx : ∃ y, x = rightCosetPoint Q 1 y := by
    induction x using QuotientGroup.induction_on with | H x =>
      refine ⟨x⁻¹,?_⟩
      simp [rightCosetPoint]
  obtain ⟨x,rfl⟩ := hx
  rw [Set.mem_compl_iff,Set.mem_insert_iff]
  change (rightCosetPoint Q 1 x ∈ orbit _ (rightCosetPoint Q 1 _)) ↔ _
  rw [source_orbit_mem,opposite_doubleCoset_eq_compl Q hm,Set.mem_compl_iff,Set.mem_union]
  rw [rightCosetPoint_eq_iff]
  change ¬(x ∈ _ ∨ x ∈ _) ↔ ¬(x*1⁻¹ ∈ _ ∨ rightCosetPoint Q 1 x ∈
      orbit _ (rightCosetPoint Q 1 _))
  rw [source_orbit_mem,inv_one,mul_one]
  rfl

/-- The two distinct original simple reflections give distinct cosets. -/
theorem base_ne_neighbor : rightCosetPoint Q 1 1 ≠ neighborPoint Q := by
  intro he
  have hn : (representative (Q.simple 0) : X ⧸ Q.D) ∈
      Q.tits.standardParabolic {Q.simple 1} := by
    apply (Q.tits.standardParabolic {Q.simple 1}).inv_mem_iff.mp
    simpa only [one_mul] using (rightCosetPoint_eq_iff Q 1 1 _).mp he
  change (representative (Q.simple 0) : X ⧸ Q.D) ∈ (Q.tits.standardParabolic {Q.simple 1} : Set (X ⧸ Q.D)) at hn
  rw [show (Q.tits.standardParabolic {Q.simple 1} : Set (X ⧸ Q.D)) =
    (Q.tits.B : Set (X ⧸ Q.D)) ∪ Q.tits.bruhatCell (Q.simple 1) from
      singleton_parabolic_cells (Q.simple_mem 1)] at hn
  have hs := Q.tits.representative_mem_bruhatCell (Q.simple 0)
    (representative _) (representative_spec _)
  rcases hn with hn | hn
  · have h1 : (representative (Q.simple 0) : X ⧸ Q.D) ∈ Q.tits.bruhatCell 1 := by
      rwa [Q.tits.bruhatCell_one]
    exact (Q.tits.involutions _ (Q.simple_mem 0)).1 (Q.tits.doubleCoset_index_unique hs h1)
  · exact (by decide : (0 : Fin 2) ≠ 1) (Q.simple_injective (Q.tits.doubleCoset_index_unique hs hn))

/-- The chosen lift acts on right source cosets by its inverse. -/
theorem neighbor_swap_base :
    (representative (Q.simple 0) : X ⧸ Q.D)⁻¹ • rightCosetPoint Q 1 1 = neighborPoint Q := by
  unfold neighborPoint rightCosetPoint
  change QuotientGroup.mk ((representative (Q.simple 0) : X ⧸ Q.D)⁻¹*1⁻¹) = _
  simp only [inv_one,mul_one]

/-- The lift need not itself be involutory: its square lies in the full Borel,
which is enough to exchange the two source cosets. -/
theorem neighbor_swap_neighbor :
    (representative (Q.simple 0) : X ⧸ Q.D)⁻¹ • neighborPoint Q = rightCosetPoint Q 1 1 := by
  unfold neighborPoint rightCosetPoint
  apply QuotientGroup.eq.mpr
  change ((representative (Q.simple 0) : X ⧸ Q.D)⁻¹ *
    (representative (Q.simple 0) : X ⧸ Q.D)⁻¹)⁻¹*1⁻¹ ∈ _
  simp only [mul_inv_rev,inv_inv,inv_one,mul_one]
  apply Q.tits.B_le_standardParabolic _
  have hh := (Q.tits.representative_sq_mem_intersection (Q.simple_mem 0)
    (representative (Q.simple 0)) (representative_spec _)).1
  change (representative (Q.simple 0) : X ⧸ Q.D)^2 ∈ Q.tits.B at hh
  simpa only [pow_two] using hh

private theorem parabolic_card (split : SplitData Q.tits) {q : ℕ}
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (Q.tits.standardParabolic {Q.simple 1}) = Nat.card Q.tits.B*(q+1) := by
  have hi := singleton_parabolic_root_index Q split 1
  rw [hq1] at hi
  have h := (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple 1})).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (Q.tits.B_le_standardParabolic _)).toEquiv,hi] at h
  simpa only [Nat.add_comm] using h.symm

/-- The original neighboring subdegree q(q+1), derived from its four cells. -/
theorem neighbor_orbit_card (split : SplitData Q.tits) {q : ℕ}
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)) = q*(q+1) := by
  rw [base_stabilizer]
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q.tits.standardParabolic {Q.simple 1}))
  unfold neighborPoint rightCosetPoint
  rw [right_coset_orbit_card_mul,neighbor_doubleCoset_card Q split hm hq0 hq1,
    parabolic_card Q split hq1]
  ring

/-- The original opposite subdegree q³, derived from its two cells. -/
theorem opposite_orbit_card (split : SplitData Q.tits) {q : ℕ}
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q) :
    Nat.card (orbit (stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (oppositePoint Q)) = q^3 := by
  rw [base_stabilizer]
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q.tits.standardParabolic {Q.simple 1}))
  unfold oppositePoint rightCosetPoint
  rw [right_coset_orbit_card_mul,opposite_doubleCoset_card Q split hm hq0 hq1,
    parabolic_card Q split hq1]
  ring

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
