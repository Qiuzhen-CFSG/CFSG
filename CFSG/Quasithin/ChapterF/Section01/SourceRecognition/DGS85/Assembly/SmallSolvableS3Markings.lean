module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.SmallSolvableLinearFourMarkings
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Literal local markings for the small-solvable / S₃ pair

The binary linear marking transports the original S₃ quotient to every
actual graph-local actor of that type. The other type retains its original
D₁₀-or-Sz(2) alternatives, including the possible D₁₀ enlargement.
These markings serve the separate distance-one exclusion and the
Chapter 15 distance-three source argument. They do not exclude the
generic pair, which occurs in the Ree/Tits models.
Source: DGS (1985), reduction pp.95--96, Chapters 9 and 11;
Aschbacher--Smith F.1.12 and 15.2.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

/-- An actual S₃ quotient is the binary linear rank-one model. -/
theorem symmetricThree_rankOne_model {H : Type*} [Group H]
    (e : H ≃* Equiv.Perm (Fin 3)) : IsRankOneModel H := by
  exact .linear 1 (by decide) ⟨ZMod 2,inferInstance,inferInstance,
    (by norm_num [Nat.card_eq_fintype_card]),
    ⟨(e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm).trans
      (Theory.PSL2.sl2QuotientEquiv (ZMod 2))⟩⟩

/-- The original binary quotient remains S₃ at each vertex of its type. -/
theorem symmetricThree_graph_quotient (h : HypothesisF11 L S) (j : Bool)
    (e : (family L j ⧸ pCore 2 (family L j)) ≃* Equiv.Perm (Fin 3))
    (v : Vertex F) (hv : v.type = j) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      Equiv.Perm (Fin 3)) := by
  let e₂ := SLTwoPermThree.sl2Two_equiv_perm_three.some
  let eP := (e.trans e₂.symm).trans (Theory.PSL2.sl2QuotientEquiv (ZMod 2))
  exact ⟨(linear_graph_quotient h j eP v hv).some.trans e₂⟩

/-- The complete graph-local catalogue of the original small-solvable/S₃
pair, with the small endpoint first and the binary endpoint second. -/
theorem small_solvable_s3_graph_models (h : HypothesisF11 L S)
    (hm : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* SuzukiMatrixGroup 0))
    (hs : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* Equiv.Perm (Fin 3)))
    (v : Vertex F) : IsRankOneModel (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) := by
  by_cases hv : v.type = true
  · exact symmetricThree_rankOne_model (symmetricThree_graph_quotient h true hs.some v hv).some
  · rcases small_solvable_graph_quotients h false hm v (Bool.eq_false_iff.mpr hv) with hd | hz
    · exact .dihedral hd
    · exact .suzuki 0 hz

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
