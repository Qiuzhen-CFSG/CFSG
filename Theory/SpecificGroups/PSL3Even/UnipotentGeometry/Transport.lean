module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic

/-!
# Root-plane maximality and marked transport

The two concrete planes are exactly the maximal elementary abelian subgroups.
An actual equivalence from UT₃(F) onto an ambient subgroup transports the center,
orders, exponent and containment statements. All centers and centralizers are
relative to that subgroup; no ambient normality or fusion is assumed.

Source: Aschbacher--Smith §5.3.5--5.3.7, printed p. 660 (PDF p. 677).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F]

theorem plane₁_not_le_plane₂ : ¬ V₁ F ≤ V₂ F := by
  intro h
  have := h ((mem_V₁ F (⟨1,0,0⟩ : U F)).mpr rfl)
  simp at this

theorem plane₂_not_le_plane₁ : ¬ V₂ F ≤ V₁ F := by
  intro h
  have := h ((mem_V₂ F (⟨0,1,0⟩ : U F)).mpr rfl)
  simp at this

section Even
variable [CharP F 2]

theorem plane₁_maximal (B : Subgroup (U F)) [IsElementaryAbelian 2 B]
    (h : V₁ F ≤ B) : B = V₁ F := by
  rcases elementary_le_plane F B with hB | hB
  · exact le_antisymm hB h
  · exact (plane₁_not_le_plane₂ F (h.trans hB)).elim

theorem plane₂_maximal (B : Subgroup (U F)) [IsElementaryAbelian 2 B]
    (h : V₂ F ≤ B) : B = V₂ F := by
  rcases elementary_le_plane F B with hB | hB
  · exact (plane₂_not_le_plane₁ F (h.trans hB)).elim
  · exact le_antisymm hB h

/-- Exact maximal elementary abelian classification, without a maximality record. -/
theorem maximal_elementary_iff (A : Subgroup (U F)) [IsElementaryAbelian 2 A] :
    (∀ B : Subgroup (U F), IsElementaryAbelian 2 B → A ≤ B → B = A) ↔
      A = V₁ F ∨ A = V₂ F := by
  constructor
  · intro h
    rcases elementary_le_plane F A with hA | hA
    · exact Or.inl (h _ inferInstance hA).symm
    · exact Or.inr (h _ inferInstance hA).symm
  · rintro (rfl | rfl) B hB h
    · exact plane₁_maximal F B h
    · exact plane₂_maximal F B h

end Even

section Marked
variable {G : Type*} [Group G] (S : Subgroup G) (e : U F ≃* S)

/-- The center of the local overgroup, expressed inside the ambient group. -/
theorem marked_center :
    (Subgroup.center S).map S.subtype = (Z F).map (markedHom F S e) := by
  have hc : (Z F).map e.toMonoidHom = Subgroup.center S := by
    ext s
    rw [Subgroup.mem_map_equiv, Z_eq_center, Subgroup.mem_center_iff,
      Subgroup.mem_center_iff]
    constructor
    · intro h t
      apply e.symm.injective
      simpa only [map_mul] using h (e.symm t)
    · intro h a
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using h (e a)
  rw [← hc, Subgroup.map_map]
  rfl

include e in
theorem marked_quotient_commutative : IsMulCommutative (S ⧸ Subgroup.center S) := by
  have hc : (Z F).map e.toMonoidHom = Subgroup.center S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_map]
    exact (marked_center F S e).symm
  let q := QuotientGroup.congr (Z F) (Subgroup.center S) e hc
  refine ⟨⟨fun a b => q.symm.injective ?_⟩⟩
  simp only [map_mul, mul_comm']

/-- The transported highest-root subgroup centralizes the specified S. -/
theorem marked_center_le_centralizer :
    (Z F).map (markedHom F S e) ≤ Subgroup.centralizer (S : Set G) := by
  rw [← marked_center F S e]
  rintro x ⟨z,hz,rfl⟩ y hy
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y,hy⟩)

theorem marked_card_plane₁ :
    Nat.card ((V₁ F).map (markedHom F S e)) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr ((V₁ F).equivMapOfInjective _ (markedHom_injective F S e)).toEquiv]
  exact card_V₁ F

theorem marked_card_plane₂ :
    Nat.card ((V₂ F).map (markedHom F S e)) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr ((V₂ F).equivMapOfInjective _ (markedHom_injective F S e)).toEquiv]
  exact card_V₂ F

theorem marked_card_center :
    Nat.card ((Z F).map (markedHom F S e)) = Nat.card F := by
  rw [← Nat.card_congr ((Z F).equivMapOfInjective _ (markedHom_injective F S e)).toEquiv]
  exact card_Z F

variable [CharP F 2]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem marked_plane₁_elementary : IsElementaryAbelian 2 ((V₁ F).map (markedHom F S e)) :=
  IsElementaryAbelian.map (markedHom F S e)

theorem marked_plane₂_elementary : IsElementaryAbelian 2 ((V₂ F).map (markedHom F S e)) :=
  IsElementaryAbelian.map (markedHom F S e)

theorem marked_center_exponent (x : G) (hx : x ∈ (Z F).map (markedHom F S e)) :
    x ^ 2 = 1 := by
  obtain ⟨a,ha,rfl⟩ := hx
  rw [← map_pow, Z_exponent_two F a ha, map_one]

theorem marked_elementary_le_plane (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) :
    A ≤ (V₁ F).map (markedHom F S e) ∨ A ≤ (V₂ F).map (markedHom F S e) := by
  let f := markedHom F S e
  have hp : ∀ a ∈ A.comap f, a ^ 2 = 1 := by
    intro a ha
    apply markedHom_injective F S e
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (f a) ha
  have hle (V : Subgroup (U F)) (hV : A.comap f ≤ V) : A ≤ V.map f := by
    intro x hx
    have hxS := hAS hx
    rw [← range_markedHom F S e] at hxS
    obtain ⟨a,rfl⟩ := hxS
    exact ⟨a,hV hx,rfl⟩
  exact (le_plane_of_exponent_two F _ hp).imp (hle _) (hle _)

end Marked
end Matrix.PSL3Even.UnipotentGeometry
