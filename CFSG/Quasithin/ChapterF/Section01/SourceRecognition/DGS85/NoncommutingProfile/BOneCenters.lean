module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneSylow
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalFixedLine
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The center and Sylow order dichotomy for b=1

The two full actor centers intersect trivially: their intersection is
normalized by the full Borel and centralized by both local actors, hence
is normal in the faithful completion. Each center embeds into the other
natural core quotient, inside its Sylow fixed line. Borel maximality
supplies every Sylow-normalizer actor on that line. Its transitivity on
nonzero vectors forces the embedded center to have order one or q.
Reciprocal core indices give equal center orders at both endpoints.

Thus the actual common Sylow product has order q³ with trivial actor
centers, or q⁴ with centers of order q. The corresponding vertex cores
have orders q² or q³. Both centers and the Sylow product remain literal
subgroups of the same source completion.

Source: DGS, *Groups and Graphs* (1985), the proof of 10.5(c), p.156.
The earlier Chapter 6 normalization of the actors by the Borel remains
explicit, as do the marked Chapter 7 natural actions. This proves the
order dichotomy, not the remaining r,s and path-stabilizer clauses.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)

/-- The full local actor center lies in both adjacent vertex cores. -/
theorem actor_center_le_cores (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v) :
    centerIn c.actor ≤ Q (family P) v ⊓ Q (family P) w := by
  have hC := (naturalCoreSection c h hcore).kernel_le
  refine le_inf hC ?_
  intro x hx
  have hxZ : x ∈ Z (family P) v := hcore ▸ hC hx
  have hZw : Z (family P) w ≤ c.actor := by
    intro z hz
    exact c.neighbor_core_le
      (((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hz)).1)
  have hxc := (centralizer_le hZw) hx.2
  exact (show x ∈ Z (family P) v ⊓ Q (family P) w from
    c.centralizer_intersection ▸
      (show x ∈ Z (family P) v ⊓ centralizer (Z (family P) w : Set G) from ⟨hxZ,hxc⟩)).2

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)

include h

/-- Faithfulness kills the common part of the two full local centers. -/
theorem paired_actor_centers_disjoint
    (hn₀ : B ≤ normalizer (c₀.actor : Set G))
    (hn₁ : B ≤ normalizer (c₁.actor : Set G)) :
    Disjoint (centerIn c₀.actor) (centerIn c₁.actor) := by
  let N := centerIn c₀.actor ⊓ centerIn c₁.actor
  have hNB : N ≤ B := by
    have hh : N ≤ stabilizer (family P) (base (family P) false) ⊓
        stabilizer (family P) (base (family P) true) :=
      inf_le_inf (inf_le_left.trans c₀.actor_le) (inf_le_left.trans c₁.actor_le)
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,family,h.intersection] using hh
  have hBN : B ≤ normalizer (N : Set G) :=
    (le_inf (normalizes_centerIn hn₀) (normalizes_centerIn hn₁)).trans
      inf_normalizer_le_normalizer_inf
  have hnL₀ : c₀.actor ≤ normalizer (N : Set G) :=
    ((le_centralizer_iff.mpr (show N ≤ centralizer (c₀.actor : Set G) from
      inf_le_left.trans inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hnL₁ : c₁.actor ≤ normalizer (N : Set G) :=
    ((le_centralizer_iff.mpr (show N ≤ centralizer (c₁.actor : Set G) from
      inf_le_right.trans inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hs₀ : c₀.actor ⊔ B = P 0 := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,family,h.intersection]
      using c₀.supplement
  have hs₁ : c₁.actor ⊔ B = P 1 := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,family,
      inf_comm (P 1) (P 0),h.intersection] using c₁.supplement
  have hn : N.Normal := normalizer_eq_top_iff.mp (top_unique (h.generate ▸
    sup_le (hs₀ ▸ sup_le hnL₀ hBN) (hs₁ ▸ sup_le hnL₁ hBN)))
  exact disjoint_iff.mpr (h.faithful N hn hNB)

local instance bOneCenterFieldAlgebra {k : Type*} [Field k] [CharP k 2] : Algebra (ZMod 2) k := ZMod.algebra k 2

omit c₀ c₁ in
/-- A central subgroup disjoint from the section kernel has order one or q. -/
theorem central_subgroup_card_of_normalizer_lifts
    {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)
    (hcore : Q (family P) v = Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (C A : Subgroup G)
    (hC : C ≤ Q (family P) v)
    (hcentral : C ≤ centralizer (Z (family P) w : Set G))
    (hdisjoint : Disjoint (centerIn c.actor) C)
    (hn : A ≤ normalizer (C : Set G))
    (hlift : ∀ g ∈ normalizer (c.imageSylow : Set SL(2,k)),
      ∃ a : c.actor, (a : G) ∈ A ∧ c.quotient a = g) :
    Nat.card C = 1 ∨ Nat.card C = Nat.card k := by
  let : Finite W := Finite.of_equiv (Fin 2 → k) E.toEquiv.symm
  let d := naturalCoreSection c h hcore
  let I := d.imageSpace C
  have hI : I ≤ fixedSpace c.representation c.imageSylow := by
    intro x hx s
    have hs : s.val ∈ ((Z (family P) w).subgroupOf c.actor).map c.quotient :=
      c.neighbor_image.symm ▸ s.property
    obtain ⟨a,ha,he⟩ := hs
    change c.representation s.val x = x
    rw [←he]
    have hcomm : ⁅Z (family P) w,C⁆ ≤ centerIn c.actor := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hcentral]
      exact bot_le
    exact d.fixed_on_imageSpace_of_commutator_le (Z (family P) w) C hcomm a ha x hx
  have hstable : ∀ g ∈ normalizer (c.imageSylow : Set SL(2,k)), ∀ x ∈ I,
      c.representation g x ∈ I := by
    intro g hg x hx
    obtain ⟨a,ha,rfl⟩ := hlift g hg
    exact d.imageSpace_apply_mem C a (hn ha) x hx
  have hcard : Nat.card I = Nat.card C := by
    rw [d.imageSpace_card_eq_relIndex C hC,←inf_relIndex_left C (centerIn c.actor),
      inf_comm C (centerIn c.actor),hdisjoint.eq_bot,relIndex_bot_left]
  obtain ⟨E',he⟩ := exists_natural_coordinates c E
  rcases invariant_subspace_of_natural_fixed c.representation c.imageSylow
      c.quadratic c.generated c.fixed_bot E' he I hI hstable with hb | hf
  · left
    rw [←hcard,hb]
    exact Nat.card_unique
  · right
    rw [←hcard,hf]
    exact (sl2_natural_fixed_spaces c.representation c.imageSylow c.quadratic
      c.generated c.fixed_bot E).1

/-- Embed the first center into the opposite natural fixed line. -/
theorem first_actor_center_card_alternatives
    (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hn₀ : B ≤ normalizer (c₀.actor : Set G))
    (hn₁ : B ≤ normalizer (c₁.actor : Set G))
    (hlift : ∀ g ∈ normalizer (c₁.imageSylow : Set SL(2,k₁)),
      ∃ a : c₁.actor, (a : G) ∈ B ∧ c₁.quotient a = g) :
    Nat.card (centerIn c₀.actor) = 1 ∨ Nat.card (centerIn c₀.actor) = Nat.card k₁ := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hC := (actor_center_le_cores c₀ h h₀).trans inf_le_right
  have hcent : centerIn c₀.actor ≤ centralizer (Z (family P) (base (family P) false) : Set G) := by
    rw [←h₀]
    exact inf_le_right.trans (centralizer_le c₀.core_le)
  exact central_subgroup_card_of_normalizer_lifts h c₁ h₁ E₁ (centerIn c₀.actor) B hC hcent
    (paired_actor_centers_disjoint h c₀ c₁ hn₀ hn₁).symm
    (normalizes_centerIn hn₀) hlift

/-- Reciprocal core indices identify the orders of the two full centers. -/
theorem paired_actor_center_orders_eq
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁)) :
    Nat.card (centerIn c₀.actor) = Nat.card (centerIn c₁.actor) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hf := paired_field_orders_eq h c₀ c₁ E₀
  have hi₀ := neighbor_center_index c₀ h
  have hi₁ := neighbor_center_index c₁ h
  rw [←h₁] at hi₀
  rw [←h₀] at hi₁
  have count (A D : Subgroup G) :
      Nat.card (A ⊓ D : Subgroup G) * A.relIndex D = Nat.card D := by
    simpa only [relIndex_bot_left,inf_relIndex_right] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ D) D bot_le inf_le_right
  have hc₀ := count (Q (family P) (base (family P) true))
    (Q (family P) (base (family P) false))
  have hc₁ := count (Q (family P) (base (family P) false))
    (Q (family P) (base (family P) true))
  rw [hi₁,inf_comm] at hc₀
  rw [hi₀,hf] at hc₁
  have hc := hc₀.symm.trans hc₁
  rw [core_card_of_natural c₀ h h₀ E₀,core_card_of_natural c₁ h h₁ E₁,hf] at hc
  exact Nat.mul_left_cancel (pow_pos (Nat.card_pos : 0 < Nat.card k₁) 2) hc

/-- Both centers are trivial, or both have their respective field orders. -/
theorem paired_center_order_dichotomy
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hn₀ : B ≤ normalizer (c₀.actor : Set G))
    (hn₁ : B ≤ normalizer (c₁.actor : Set G)) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥) ∨
      (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
        Nat.card (centerIn c₁.actor) = Nat.card k₁) := by
  have hf := paired_field_orders_eq h c₀ c₁ E₀
  have he := paired_actor_center_orders_eq h c₀ c₁ E₀ E₁
  have h₀ := (paired_cores_eq_centers_of_actions h c₀ c₁).1
  have hlift := base_borel_lifts_sylow_normalizer h true c₁ h₀ hn₁
  rcases first_actor_center_card_alternatives h c₀ c₁ E₁ hn₀ hn₁ hlift with hb | hq
  · left
    exact ⟨card_eq_one.mp hb,card_eq_one.mp (he.symm.trans hb)⟩
  · exact Or.inr ⟨hq.trans hf.symm,he.symm.trans hq⟩

include c₀ c₁ in
/-- The literal product is a common Sylow in both full vertex stabilizers. -/
theorem paired_core_product_sylow :
    Stellmacher.IsSylowSubgroupIn
        (Q (family P) (base (family P) false) ⊔ Q (family P) (base (family P) true)) (P 0) ∧
      Stellmacher.IsSylowSubgroupIn
        (Q (family P) (base (family P) false) ⊔ Q (family P) (base (family P) true)) (P 1) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  constructor
  · simpa only [sup_comm,stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using
      core_product_sylow c₀ h h₁
  · simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,family] using
      core_product_sylow c₁ h h₀

/-- The actual core and common Sylow orders in the two center branches. -/
theorem paired_core_product_order_dichotomy
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hn₀ : B ≤ normalizer (c₀.actor : Set G))
    (hn₁ : B ≤ normalizer (c₁.actor : Set G)) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      Nat.card (Q (family P) (base (family P) false)) = Nat.card k₀ ^ 2 ∧
      Nat.card (Q (family P) (base (family P) true)) = Nat.card k₁ ^ 2 ∧
      Nat.card (Q (family P) (base (family P) false) ⊔
        Q (family P) (base (family P) true) : Subgroup G) = Nat.card k₀ ^ 3) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧
      Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      Nat.card (Q (family P) (base (family P) false)) = Nat.card k₀ ^ 3 ∧
      Nat.card (Q (family P) (base (family P) true)) = Nat.card k₁ ^ 3 ∧
      Nat.card (Q (family P) (base (family P) false) ⊔
        Q (family P) (base (family P) true) : Subgroup G) = Nat.card k₀ ^ 4) := by
  obtain ⟨h₀,h₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  have hf := paired_field_orders_eq h c₀ c₁ E₀
  have hc₀ := core_card_of_natural c₀ h h₀ E₀
  have hc₁ := core_card_of_natural c₁ h h₁ E₁
  have hS := core_product_card c₁ h h₁ E₁
  rcases paired_center_order_dichotomy h c₀ c₁ E₀ E₁ hn₀ hn₁ with ⟨hb₀,hb₁⟩ | ⟨hb₀,hb₁⟩
  · rw [card_eq_one.mpr hb₀,mul_one] at hc₀
    rw [card_eq_one.mpr hb₁,mul_one] at hc₁
    left
    refine ⟨hb₀,hb₁,hc₀,hc₁,?_⟩
    rw [hS,hc₀,←hf]
    ring
  · have hq₀ : Nat.card (Q (family P) (base (family P) false)) = Nat.card k₀ ^ 3 := by
      rw [hc₀,hb₀]
      ring
    have hq₁ : Nat.card (Q (family P) (base (family P) true)) = Nat.card k₁ ^ 3 := by
      rw [hc₁,hb₁]
      ring
    right
    refine ⟨hb₀,hb₁,hq₀,hq₁,?_⟩
    rw [hS,hq₀,←hf]
    ring

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
