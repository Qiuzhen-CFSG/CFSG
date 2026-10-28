module
public import CFSG.Quasithin.ChapterG.Section11.WholeModels
public import CFSG.Quasithin.ChapterG.Section11.WholeSporadic
public import CFSG.Quasithin.ChapterG.Section11.WholeAlternating
public import CFSG.Quasithin.ChapterG.Section11.WholeBinaryG2
public import CFSG.Quasithin.ChapterG.Section11.WholeSymplectic

/-!
# Every single whole component contradicts the strict markings

Apply the exhaustive actual carrier list and the separately proved module
exclusions. Alternating and binary G2 actions contradict the type-a2 or moved-
plane conditions; nonbinary symplectic actions have transitive moved planes;
sporadic actions violate displacement or relative Sylow-normality bounds.
No remaining single-component recognition premise is assumed.

`StrictWholePair` applies the result to the literal original strict quotient.
Source: Aschbacher--Smith G.11.7 and 6.2.18--19, pp.366--368,690--691.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeSingleExclusion
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- Every single-component carrier is excluded for the original strict
rank-two/type-a2 involution and moved-plane nontransitivity. -/
theorem false_of_single_component
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hd : 6 ≤ finrank (ZMod 2) V)
    (a : G) (ha : a^2=1) (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a)=2)
    (htype : ∀ u, B u (ρ a u)=0)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) : False := by
  have hm := (WholeModels.remaining_single_component h h9 hw hd a ha hr hnt).2
  cases hm with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    have hn' : n=6 ∨ n=7 ∨ n=8 := by omega
    rcases hn' with rfl | rfl | rfl
    · exact WholeAlternating.not_six h9 hd e
    · exact WholeAlternating.not_seven h h9 hd e a ha hr htype
    · exact WholeAlternating.not_eight h h9 hd e a ha hr htype hnt
  | symplectic n hn hm => exact WholeSymplectic.not_nonbinary_model h h9 hn hm a ha hr hnt
  | binary_g2 he => exact WholeBinaryG2.not_binary_model h h9 hd he.some a ha hr htype hnt
  | mathieu_twelve he => exact WholeSporadic.not_mathieu_twelve h h9 hw he.some
  | mathieu_twenty_two he => exact WholeSporadic.not_mathieu_twenty_two h h9 hw he.some
  | janko_two he => exact WholeSporadic.not_janko_two h h9 hS he.some
end CFSG.Quasithin.ChapterG.Section11.WholeSingleExclusion
