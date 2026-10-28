module

public import Theory.Representation.BinaryPrimeDegree
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M24.Properties.Order

/-!
# The prime-divisor degree inputs for the simple Mathieu branches of G.7

The orders of the concrete groups contain 11 for M₁₂ and M₂₂, and 23 for
M₂₃ and M₂₄. Their multiplicative orders over the binary field give lower
bounds ten and eleven. The bounds apply to every faithful representation,
without irreducibility, and transport through actual group isomorphisms.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.1(1)
and the proof of G.7.3(2), printed pp.347--348. These bounds do not prove
the James classification of the representations attaining small degree.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.MathieuRecognition
open Sporadic.Mathieu Representation.BinaryPrimeDegree

variable {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) L V) (hρ : Function.Injective ρ)

include ρ hρ

theorem ten_le_finrank_of_m12 (e : L ≃* M12) :
    10 ≤ Module.finrank (ZMod 2) V := by
  have hd : 11 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, m12_order]
    norm_num
  simpa only [orderOf_two_mod_eleven] using
    orderOf_le_finrank ρ hρ (by decide : Nat.Prime 11) (by decide) hd

theorem ten_le_finrank_of_m22 (e : L ≃* M22) :
    10 ≤ Module.finrank (ZMod 2) V := by
  have hd : 11 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, m22_order]
    norm_num
  simpa only [orderOf_two_mod_eleven] using
    orderOf_le_finrank ρ hρ (by decide : Nat.Prime 11) (by decide) hd

theorem eleven_le_finrank_of_m23 (e : L ≃* M23) :
    11 ≤ Module.finrank (ZMod 2) V := by
  have hd : 23 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, m23_order]
    norm_num
  simpa only [orderOf_two_mod_twentyThree] using
    orderOf_le_finrank ρ hρ (by decide : Nat.Prime 23) (by decide) hd

theorem eleven_le_finrank_of_m24 (e : L ≃* M24) :
    11 ≤ Module.finrank (ZMod 2) V := by
  have hd : 23 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv, m24_order]
    norm_num
  simpa only [orderOf_two_mod_twentyThree] using
    orderOf_le_finrank ρ hρ (by decide : Nat.Prime 23) (by decide) hd

/-- The M₁₂ small-degree branch has degree exactly ten; recognition is still separate. -/
theorem finrank_eq_ten_of_m12 (e : L ≃* M12)
    (hd : Module.finrank (ZMod 2) V ≤ 10) : Module.finrank (ZMod 2) V = 10 :=
  Nat.le_antisymm hd (ten_le_finrank_of_m12 ρ hρ e)

/-- No faithful binary action of M₂₃ has dimension at most ten. -/
theorem not_m23_of_finrank_le_ten (hd : Module.finrank (ZMod 2) V ≤ 10) :
    ¬ Nonempty (L ≃* M23) := by
  rintro ⟨e⟩
  have := eleven_le_finrank_of_m23 ρ hρ e
  omega

end CFSG.Quasithin.ChapterG.Section07.MathieuRecognition
