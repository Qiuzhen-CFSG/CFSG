module

public import Theory.Representation.PSL3Two.ParabolicFixedFree

/-!
# Small invariant subgroups for the point parabolic

Outside its fixed axis the point parabolic has an orbit of length six on the
natural module. A subgroup of order at most four invariant under that parabolic
therefore lies on the axis and is fixed pointwise. Applying this fact to both
projections proves the doubled version, without presupposing a summand for the
four-group. This orients the source line marking in 13.6.22.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, p.932.
-/

@[expose] public section
open Matrix Representation Subgroup BinaryLinearThree
open Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
private abbrev Outside := {x : Vector // ¬ (x 1 = 0 ∧ x 2 = 0)}
private theorem card_outside : Nat.card Outside = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide
private theorem outside_orbit : ∀ x y : Outside,
    ∃ g : pointParabolicSL, W g x.val = y.val := by
  decide +kernel
private theorem fixes_axis : ∀ g : pointParabolicSL, ∀ x : Vector,
    x 1 = 0 → x 2 = 0 → W g x = x := by
  decide +kernel

/-- Small invariant natural subgroups are fixed by the point parabolic. -/
theorem point_invariant_small_fixed (H : Subgroup (Multiplicative Vector))
    (hcard : Nat.card H ≤ 4)
    (hinv : ∀ g : pointParabolicSL, ∀ x : H,
      Multiplicative.ofAdd (W g (Multiplicative.toAdd (x : Multiplicative Vector))) ∈ H)
    (g : pointParabolicSL) (x : H) :
    W g (Multiplicative.toAdd (x : Multiplicative Vector)) =
      Multiplicative.toAdd (x : Multiplicative Vector) := by
  have hx : (Multiplicative.toAdd (x : Multiplicative Vector)) 1 = 0 ∧
      (Multiplicative.toAdd (x : Multiplicative Vector)) 2 = 0 := by
    by_contra hn
    let p : Outside := ⟨Multiplicative.toAdd (x : Multiplicative Vector), hn⟩
    have hy (y : Outside) : Multiplicative.ofAdd y.val ∈ H := by
      obtain ⟨a, ha⟩ := outside_orbit p y
      rw [← ha]
      exact hinv a x
    let f : Outside → H := fun y => ⟨Multiplicative.ofAdd y.val, hy y⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun c : H => Multiplicative.toAdd (c : Multiplicative Vector)) hab
    have hc := Nat.card_le_card_of_injective f hf
    rw [card_outside] at hc
    omega
  exact fixes_axis g _ hx.1 hx.2
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
private def first : Multiplicative (Vector × Vector) →* Multiplicative Vector :=
  { toFun := fun x => Multiplicative.ofAdd x.toAdd.1
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
private def second : Multiplicative (Vector × Vector) →* Multiplicative Vector :=
  { toFun := fun x => Multiplicative.ofAdd x.toAdd.2
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
private theorem image_card_le {A B : Type*} [_root_.Group A] [_root_.Group B] [Finite A]
    (H : Subgroup A) (f : A →* B) : Nat.card (H.map f) ≤ Nat.card H := by
  apply Nat.card_le_card_of_surjective
    (fun x : H => (⟨f x, mem_map_of_mem f x.property⟩ : H.map f))
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The same result on two summands with a common actor. -/
theorem point_invariant_small_doubled_fixed
    (H : Subgroup (Multiplicative (Vector × Vector))) (hcard : Nat.card H ≤ 4)
    (hinv : ∀ g : pointParabolicSL, ∀ x : H,
      Multiplicative.ofAdd ((W.prod W) g (Multiplicative.toAdd (x : Multiplicative (Vector × Vector)))) ∈ H)
    (g : pointParabolicSL) (x : H) :
    (W.prod W) g (Multiplicative.toAdd (x : Multiplicative (Vector × Vector))) =
      Multiplicative.toAdd (x : Multiplicative (Vector × Vector)) := by
  apply Prod.ext
  · apply point_invariant_small_fixed (H.map first) ((image_card_le H first).trans hcard)
      (fun a y => ?_) g ⟨first x, mem_map_of_mem first x.property⟩
    obtain ⟨y, hy, he⟩ := y.property
    rw [← he]
    exact mem_map_of_mem first (hinv a ⟨y, hy⟩)
  · apply point_invariant_small_fixed (H.map second) ((image_card_le H second).trans hcard)
      (fun a y => ?_) g ⟨second x, mem_map_of_mem second x.property⟩
    obtain ⟨y, hy, he⟩ := y.property
    rw [← he]
    exact mem_map_of_mem second (hinv a ⟨y, hy⟩)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
