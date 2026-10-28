module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.LocalStructure
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreGeometry

/-!
# Quintic quotient filters on the original Cartan pair

The original Input and prime actor give [DS:S] = 5. The genuine F.1.1
pair then identifies its starred left endpoint with DS. Transporting the
proved quotient orders to this literal endpoint excludes binary PSL₂ and
both unitary-three families, and forces any Suzuki marking to Sz(2).
In particular DGS 13.1's both-binary endpoint conclusion is impossible.
The small Ree type clauses are excluded in both orientations by solvability
of the full right quotient, without an isomorphism of amalgams.

These filters use the original sourceS, selected R and embedded two-cores.
They leave exhaustive DGS branch selection and the consequent p ≠ 5 to
the quintic assembly. No global Sylow placement or recognition premise is
added. Source: Aschbacher–Smith 5.2.2, printed pp.647–648, and F.1.9–12,
pp.261–264; DGS Part II, 6.1, 12.9 and 13.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original starred endpoint excludes the linear and unitary rows,
and a Suzuki quotient has precisely the binary parameter. -/
theorem LocalData.quintic_starred_quotient_filters
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    let S := Global.sourceS L H
    let P := ChapterF.Source.starredParabolic ![D ⊔ S,R] S 0
    (∀ f : ℕ, 0 < f →
      ¬ ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 (2 ^ f) ∧
      ¬ ClassicalGroup.IsPSU (P ⧸ pCore 2 P) 3 (2 ^ f) ∧
      ¬ ChapterF.Source.IsSU (P ⧸ pCore 2 P) 3 (2 ^ f)) ∧
    (∀ m : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) → m = 0) := by
  have hf := d.hypothesisF11 h hH c hd hz
  have hi := Input.prime_left_index h hH c hd
  dsimp only
  rw [hf.quintic_starred_left le_sup_right]
  exact ⟨fun _ hn => hf.quintic_excludes_linear_unitary le_sup_right hi hn,
    fun _ he => hf.quintic_suzuki_parameter le_sup_right hi he.some⟩

/-- DGS p.99's small Ree type clauses contradict the original right endpoint.
The disjunction accommodates both orientations of the type statement. -/
theorem LocalData.quintic_not_small_ree_type_quotients
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    let P := ChapterF.Source.parabolic
      ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1
    ¬ (ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 2 ∨
      Nonempty ((P ⧸ pCore 2 P) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) := by
  dsimp only
  intro hq
  exact d.right_parabolic_not_solvable hz
    ((d.hypothesisF11 h hH c hd hz).parabolic_solvable_of_small_ree_quotient 1 hq)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
