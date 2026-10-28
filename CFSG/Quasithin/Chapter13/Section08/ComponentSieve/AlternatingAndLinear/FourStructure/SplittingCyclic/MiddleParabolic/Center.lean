module

public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# The center in the middle binary parabolic

For an incident line--plane--hyperplane flag, the center of the full flag
stabilizer lies in both end-node radicals. The line--hyperplane stabilizer
fixes the binary line pointwise and acts trivially on the one-dimensional
quotient by the hyperplane, so it centralizes their common radical.

This proves the centralization step used in Aschbacher--Smith 13.8.25,
combined manuscript of 1 March 2004, printed p.962 (PDF p.979).
-/

@[expose] public section

namespace BinaryLinear.MiddleParabolic
open Subgroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem nonzero_eq_of_finrank_one (hd : Module.finrank (ZMod 2) V = 1)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) : v = w := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hv w
  have hc0 : c ≠ 0 := by
    intro h
    exact hw (by simpa [h] using hc.symm)
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc

private theorem fixes_line {L : Submodule (ZMod 2) V}
    (hL : Module.finrank (ZMod 2) L = 1) {g : GL V}
    (hg : g ∈ parabolic L) {v : V} (hv : v ∈ L) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  exact congrArg Subtype.val (nonzero_eq_of_finrank_one hL
    (v := (⟨g v, (hg v).mpr hv⟩ : L)) (w := (⟨v, hv⟩ : L))
    (by intro h; exact hv0 (g.map_eq_zero_iff.mp (congrArg Subtype.val h)))
    (by intro h; exact hv0 (congrArg Subtype.val h)))

private theorem displacement_mem_hyperplane [FiniteDimensional (ZMod 2) V]
    {F : Submodule (ZMod 2) V}
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) V)
    {g : GL V} (hg : g ∈ parabolic F) (v : V) : g v - v ∈ F := by
  by_cases hv : v ∈ F
  · exact F.sub_mem ((hg v).mpr hv) hv
  have hd : Module.finrank (ZMod 2) (V ⧸ F) = 1 := by
    have := F.finrank_quotient_add_finrank
    omega
  apply (Submodule.Quotient.eq F).mp
  apply nonzero_eq_of_finrank_one hd
  · intro h
    exact hv ((hg v).mp ((Submodule.Quotient.mk_eq_zero F).mp h))
  · exact fun h => hv ((Submodule.Quotient.mk_eq_zero F).mp h)

/-- The middle minimal parabolic: the stabilizer of a line inside a hyperplane. -/
def middle (L F : Submodule (ZMod 2) V) : Subgroup (GL V) :=
  parabolic L ⊓ parabolic F

/-- The full flag stabilizer inside the middle minimal parabolic. -/
def borel (L P F : Submodule (ZMod 2) V) : Subgroup (GL V) :=
  middle L F ⊓ parabolic P

private theorem center_mem_radical {W : Submodule (ZMod 2) V}
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    {T : Subgroup (GL V)} (hWT : radical W ≤ T)
    {z : GL V} (hz : z ∈ (center T).map T.subtype) : z ∈ radical W := by
  obtain ⟨z, hz, rfl⟩ := hz
  apply centralizer_radical_le hW hWt
  apply mem_centralizer_iff.mpr
  intro g hg
  exact congrArg Subtype.val (mem_center_iff.mp hz (⟨g, hWT hg⟩ : T))

/-- A line--hyperplane stabilizer centralizes the common radical. -/
theorem middle_centralizes_radical_inf [FiniteDimensional (ZMod 2) V]
    {L F : Submodule (ZMod 2) V}
    (hL : Module.finrank (ZMod 2) L = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) V) :
    middle L F ≤ centralizer (radical L ⊓ radical F : Set (GL V)) := by
  intro g hg
  apply mem_centralizer_iff.mpr
  intro z hz
  ext v
  have hg' := fixes_line hL hg.1 (hz.1.2 v)
  have hz' := hz.2.1 (g v - v) (displacement_mem_hyperplane hF hg.2 v)
  simp only [map_sub] at hg' hz'
  change z (g v) = g (z v)
  rw [sub_eq_iff_eq_add] at hg' hz'
  rw [hg', hz']
  abel

/-- The center of any intermediate flag stabilizer is centralized by the middle parabolic. -/
theorem middle_centralizes_borel_center [FiniteDimensional (ZMod 2) V]
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) V) :
    middle L F ≤ centralizer ((center (borel L P F)).map (borel L P F).subtype : Set (GL V)) := by
  have hL0 : L ≠ ⊥ := by
    intro h
    have he := congrArg (fun S : Submodule (ZMod 2) V => Module.finrank (ZMod 2) S) h
    simp only [finrank_bot, hL] at he
    omega
  have hFt : F ≠ ⊤ := by
    intro h
    have he := congrArg (fun S : Submodule (ZMod 2) V => Module.finrank (ZMod 2) S) h
    rw [finrank_top] at he
    omega
  have hLt := ne_top_of_le_ne_top hFt (hLP.trans hPF)
  have hF0 := ne_bot_of_le_ne_bot hL0 (hLP.trans hPF)
  have hRL : radical L ≤ borel L P F :=
    le_inf (le_inf (radical_le_parabolic L) (radical_le_nested_parabolic (hLP.trans hPF)))
      (radical_le_nested_parabolic hLP)
  have hRF : radical F ≤ borel L P F :=
    le_inf (le_inf (radical_le_smaller_parabolic (hLP.trans hPF)) (radical_le_parabolic F))
      (radical_le_smaller_parabolic hPF)
  intro g hg
  apply mem_centralizer_iff.mpr
  intro z hz
  exact mem_centralizer_iff.mp (middle_centralizes_radical_inf hL hF hg) z
    ⟨center_mem_radical hL0 hLt hRL hz, center_mem_radical hF0 hFt hRF hz⟩
end BinaryLinear.MiddleParabolic

end
