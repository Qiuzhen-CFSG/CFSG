module

public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Common fixed subgroups and actor normalizers

The normalizer of an acting subgroup preserves its common fixed subgroup.
The statements use the original homomorphism to automorphisms, including
when its source action has a kernel.
-/

@[expose] public section
namespace MonoidHom
open Subgroup
variable {A W : Type*} [Group A] [Group W]

/-- The literal subgroup fixed by every element of the indicated actor. -/
def commonFixed (ρ : A →* MulAut W) (L : Subgroup A) : Subgroup W :=
  ⨅ a : L, MulAut.fixedSubgroup (ρ a)

@[simp] theorem mem_commonFixed (ρ : A →* MulAut W) (L : Subgroup A) (w : W) :
    w ∈ ρ.commonFixed L ↔ ∀ a ∈ L, ρ a w = w := by
  simp only [commonFixed, mem_iInf, MulAut.mem_fixedSubgroup]
  exact Subtype.forall

private theorem commonFixed_preserved (ρ : A →* MulAut W) (L : Subgroup A)
    (a : A) (ha : a ∈ normalizer (L : Set A))
    {w : W} (hw : w ∈ ρ.commonFixed L) : ρ a w ∈ ρ.commonFixed L := by
  rw [mem_commonFixed] at hw ⊢
  intro b hb
  have hconj : a⁻¹ * b * a ∈ L := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (L : Set A)).inv_mem ha) b).mp hb
  have he := congrArg (ρ a) (hw _ hconj)
  have hgroup : a * (a⁻¹ * b * a) = b * a := by simp [← mul_assoc]
  calc
    ρ b (ρ a w) = ρ (b * a) w := by rw [map_mul]; rfl
    _ = ρ (a * (a⁻¹ * b * a)) w := by rw [hgroup]
    _ = ρ a w := by rw [map_mul]; exact he

/-- Actor normalization preserves the actual common fixed subgroup. -/
theorem commonFixed_map_of_normalizes (ρ : A →* MulAut W) (L : Subgroup A)
    (a : A) (ha : a ∈ normalizer (L : Set A)) :
    (ρ.commonFixed L).map (ρ a).toMonoidHom = ρ.commonFixed L := by
  apply le_antisymm
  · rintro w ⟨x, hx, rfl⟩
    exact commonFixed_preserved ρ L a ha hx
  · intro w hw
    refine ⟨ρ a⁻¹ w,
      commonFixed_preserved ρ L a⁻¹ ((normalizer (L : Set A)).inv_mem ha) hw, ?_⟩
    change ρ a (ρ a⁻¹ w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end MonoidHom
