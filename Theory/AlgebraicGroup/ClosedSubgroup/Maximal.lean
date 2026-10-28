module

public import Theory.AlgebraicGroup.Dimension.Chain

universe u

/-! Maximal elements in nonempty families of connected closed subgroups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Any nonempty family of connected closed subgroups has an
inclusion-maximal member. -/
public theorem exists_maximal_connected_closedSubgroup
    (G : Variety k) [AlgebraicGroup G]
    (P : ClosedSubgroup G → Prop) (hP : ∃ T, P T)
    (hconnected : ∀ T, P T →
      _root_.IsConnected (T : Set (Variety.Point G))) :
    ∃ T, P T ∧ ∀ S, P S → T ≤ S → S = T := by
  let : PartialOrder (ClosedSubgroup G) :=
    { le := fun A B ↦ (A : Set (Variety.Point G)) ⊆ B
      le_refl := fun _ ↦ Set.Subset.rfl
      le_trans := fun _ _ _ ↦ Set.Subset.trans
      le_antisymm := fun _ _ hAB hBA ↦
        SetLike.coe_injective (Set.Subset.antisymm hAB hBA) }
  let C := {T : ClosedSubgroup G // P T}
  have hwf : WellFounded ((· > ·) : C → C → Prop) := by
    rw [wellFounded_iff_isEmpty_descending_chain]
    refine ⟨?_⟩
    rintro ⟨f, hf⟩
    let H : ℕ → ClosedSubgroup G := fun n ↦ (f n).1
    have hstep : ∀ n, H n < H (n + 1) := fun n ↦ hf n
    have hmono : Monotone H :=
      monotone_nat_of_le_succ fun n ↦ (hstep n).le
    obtain ⟨n, hn⟩ := ascending_connectedClosedSubgroups_eventually_constant G H
      (fun {_ _} h ↦ hmono h)
      (fun n ↦ hconnected (H n) (f n).2)
    exact (hstep n).ne (hn (n + 1) (Nat.le_succ n)).symm
  let : WellFoundedGT C := ⟨hwf⟩
  obtain ⟨T₀, hT₀⟩ := hP
  obtain ⟨T, hTmax⟩ :=
    exists_maximal_of_wellFoundedGT (fun _ : C ↦ True)
      ⟨⟨T₀, hT₀⟩, trivial⟩
  refine ⟨T.1, T.2, ?_⟩
  intro S hS hTS
  let S' : C := ⟨S, hS⟩
  have hle : T ≤ S' := hTS
  have heq : T = S' := hTmax.eq_of_le trivial hle
  exact congrArg Subtype.val heq |>.symm

end Theory.AlgebraicGroup
