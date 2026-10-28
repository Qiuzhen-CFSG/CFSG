module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.CubicSylowCentralizer
/-!
# The opposite Borel centralizes the second natural block

The two source components L and K share their full Sylow P. The opposite
original component L₂ commutes with L and contains the cubic torus D₂.
Consequently D₂ fixes P. Since D₂ normalizes K, the short-group action theorem
makes D₂ centralize K. The Baumann subgroup S normalizes K, so its literal
commutator [S,D₂] also centralizes K. Their join is the actual opposite Borel
used by the terminal normalizer argument.

Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The source commuting pair and actual common Sylow discharge the opposite
Borel's centralization, retaining its literal torus and commutator subgroup. -/
theorem source_natural_opposite_borel_centralizes
    (L L₂ K P S D₂ : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) (hPL : P ≤ L)
    (hcomm : L₂ ≤ centralizer (L : Set G)) (hD₂ : Nat.card D₂ = 3)
    (hD₂L : D₂ ≤ L₂) (hD₂K : D₂ ≤ normalizer (K : Set G))
    (hSK : S ≤ normalizer (K : Set G)) :
    D₂ ≤ centralizer (K : Set G) ∧
      (⁅S,D₂⁆ ⊔ D₂ : Subgroup G) ≤ centralizer (K : Set G) := by
  obtain ⟨hd,hs⟩ := IsShort.cubic_and_commutator_centralize K P D₂ S hK hP
    hD₂ hD₂K (hD₂L.trans (hcomm.trans (centralizer_le hPL))) hSK
  exact ⟨hd,sup_le hs hd⟩
end CFSG.Quasithin.Chapter10
