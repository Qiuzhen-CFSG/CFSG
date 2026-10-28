module

public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Centerlessness of the genuine binary triality carrier

The existing elementary-group center theorem and the bijective map to its
own central quotient give centerlessness of Standard.BinaryCarrier. A generic
transport helper avoids unfolding the concrete matrix carrier in the proof.
No independent simplicity or perfectness assertion is used.

Source: the standard graph-field construction in GLS3, §§2.3–2.4, and the
proved ElementaryCentralKernel comparison for binary parameters.
-/

public section
open Subgroup
namespace Triality.Standard

private theorem center_eq_bot_of_bijective
    {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hi : Function.Injective f) (hs : Function.Surjective f)
    (hz : center X = ⊥) : center Y = ⊥ := by
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨x, rfl⟩ := hs y
  have hx : x ∈ center X := by
    rw [mem_center_iff]
    intro z
    apply hi
    simpa only [map_mul] using (mem_center_iff.mp hy) (f z)
  have hxone : x = 1 := by simpa only [hz, mem_bot] using hx
  exact mem_bot.mpr (hxone ▸ f.map_one)

theorem binaryCarrier_center_eq_bot (n : ℕ) (hn : 0 < n) :
    center (BinaryCarrier n hn) = ⊥ :=
  center_eq_bot_of_bijective (toCarrier (binaryParameters n hn))
    (ElementaryCentralKernel.toCarrier_injective _ rfl)
    (toCarrier_surjective _) (ElementaryCentralKernel.center_eq_bot _ rfl)

end Triality.Standard
