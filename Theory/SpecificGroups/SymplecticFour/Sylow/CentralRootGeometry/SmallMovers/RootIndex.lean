module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Classification
/-!
# Exact movement of the transvection roots

A literal three-parameter fixed hyperplane gives fixed dimension at least
three for each full root. Faithfulness and the root order show that the
moving index is exactly the field order. Two distinct roots generate an
order-q-squared subgroup of the standard plane radical with that moving index.

Thus the source (5.1) exclusion of two order-q, index-q subgroups implies the
root-product exclusion used by the unique-maximum branch of MS93 (5.4).
No scalar-linearity is imposed on other small movers.
-/

@[expose] public section
open Subgroup Representation
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def rootFixedVector (s : Option F) (a : F × F × F) : Vector (F := F) :=
  match s with
  | none => Sum.elim ![a.1,a.2.1] ![0,a.2.2]
  | some s => Sum.elim ![a.1,a.2.1] ![a.2.2,s*a.2.2]

private theorem rootFixedVector_mem (s : Option F) (a : F × F × F) :
    rootFixedVector s a ∈ fixed (rootFamily s) := by
  apply (mem_fixed_iff _ _).mpr
  intro b u w v hg
  cases s with
  | none =>
    obtain ⟨rfl,rfl,rfl⟩ := (element_mem_root b u w v).mp hg
    simp [rootFixedVector]
  | some s =>
    obtain ⟨rfl,rfl,rfl⟩ := (element_mem_finiteRoot s b u w v).mp hg
    simp [rootFixedVector]
    constructor
    · ring_nf
      simp [CharTwo.two_eq_zero]
    · ring_nf
      simp [CharTwo.two_eq_zero]

theorem finrank_fixed_rootFamily_ge_three (s : Option F) :
    3 ≤ Module.finrank F (fixed (rootFamily s)) := by
  let p : (F × F × F) →ₗ[F] fixed (rootFamily s) :=
    { toFun := fun a => ⟨rootFixedVector s a,rootFixedVector_mem s a⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext i
        cases s <;> rcases i with i | i <;> fin_cases i <;> simp [rootFixedVector,mul_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext i
        cases s <;> rcases i with i | i <;> fin_cases i <;> simp [rootFixedVector,mul_left_comm] }
  have hp : Function.Injective p := by
    intro x y he
    have hv := congrArg (fun z : fixed (rootFamily s) => z.val) he
    have h1 : x.1=y.1 := by
      have hh := congrFun hv (.inl 0)
      cases s <;> exact hh
    have h2 : x.2.1=y.2.1 := by
      have hh := congrFun hv (.inl 1)
      cases s <;> exact hh
    have h3 : x.2.2=y.2.2 := by
      cases s with
      | none => exact congrFun hv (.inr 1)
      | some s => exact congrFun hv (.inr 0)
    exact Prod.ext h1 (Prod.ext h2 h3)
  simpa using LinearMap.finrank_le_finrank_of_injective hp

theorem movingIndex_rootFamily (s : Option F) :
    movingIndex (rootFamily s)=Nat.card F := by
  have hne : rootFamily s ≠ ⊥ := by
    intro hb
    have hc := card_rootFamily s
    rw [hb,card_bot] at hc
    have hp : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hpos := field_le_movingIndex_of_ne_bot (rootFamily s) hne
  have hdim : Module.finrank F (Vector (F := F))=4 := by simp [Vector]
  have hh := (fixed (rootFamily s)).finrank_quotient_add_finrank
  have h3 := finrank_fixed_rootFamily_ge_three s
  have hquot : Module.finrank F (Vector (F := F) ⧸ fixed (rootFamily s)) ≤ 1 := by
    rw [hdim] at hh
    omega
  apply le_antisymm _ hpos
  exact (Nat.pow_le_pow_right (Nat.card_pos (α := F)) hquot).trans_eq (pow_one _)

theorem movingIndex_rootFamily_four (hF : Nat.card F=4) (s : Option F) :
    movingIndex (rootFamily s)=4 := by rw [movingIndex_rootFamily,hF]

theorem movingIndex_rootFamily_sup (hF : Nat.card F=4) {s t : Option F} (hne : s ≠ t) :
    movingIndex (rootFamily s ⊔ rootFamily t)=16 := by
  have hh := movingIndex_eq_field_sq_of_large_wing (rootFamily s ⊔ rootFamily t)
    (sup_le (rootFamily_le_wing s) (rootFamily_le_wing t)) (by
      rw [rootFamily_sup_card hne,hF]
      norm_num)
  norm_num [hF] at hh
  exact hh
open scoped Pointwise in
theorem rootExclusion_of_source (hF : Nat.card F=4)
    (T : Subgroup (unipotent (F := F)))
    (hsource : ∀ E A : Subgroup (unipotent (F := F)), E≤T → A≤T →
      Nat.card E=4 → movingIndex E=4 → Nat.card A=4 → movingIndex A=4 →
      ¬ (join T : Set (unipotent (F := F))) ⊆ (E:Set _) * (A:Set _)) :
    RootExclusion T := by
  intro s t hs ht
  exact hsource (rootFamily s) (rootFamily t) hs ht
    ((card_rootFamily s).trans hF) (movingIndex_rootFamily_four hF s)
    ((card_rootFamily t).trans hF) (movingIndex_rootFamily_four hF t)

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
