module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.WeissEven
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ArcGeneration
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupAction.CubicTree.GeneratedLocals

/-!
# Generated local subgroups in the actual cubic source action

Goldschmidt (2.6) identifies two generated local subgroups with the full
endpoint stabilizers once their join is the original acting group. All
vertices and stabilizers here belong to the literal rank-two coset tree.

For the two-perfect source action, local coverage modulo the edge overlap
and normalization by that overlap give the required generation: the join
is normal with a two-group quotient, which must be trivial. Both terminal
source constructions use this same argument with their own local subgroups.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.6),
printed pp.380--381, as applied in (6.9) and (6.12).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The actual endpoint subgroups are recovered from the two intersection
identities and generation of the original action. -/
theorem CubicTreeAction.generated_locals_eq_stabilizers (h : CubicTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) (P Q : Subgroup G)
    (hP : P ≤ RankTwo.stabilizer F a) (hQ : Q ≤ RankTwo.stabilizer F b)
    (hPQ : P ⊓ RankTwo.stabilizer F b = P ⊓ Q)
    (hQP : Q ⊓ RankTwo.stabilizer F a = P ⊓ Q) (hgen : P ⊔ Q = ⊤) :
    P = RankTwo.stabilizer F a ∧ Q = RankTwo.stabilizer F b := by
  have ha : SimpleGraph.PathTransitivePolygon.GraphAction (RankTwo.graph F) G :=
    ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩
  obtain ⟨hp, hq⟩ := Theory.GroupAction.CubicTree.sup_inf_stabilizers_eq
    h.tree.isAcyclic ha hab P Q hP hQ hPQ hQP
  rw [hgen, top_inf_eq] at hp hq
  exact ⟨hp.symm, hq.symm⟩

/-- Covering both local groups modulo the edge overlap gives generation
when the overlap normalizes both subgroups and the action is two-perfect. -/
theorem TwoPerfectTreeAction.sup_eq_top_of_local_coverage (h : TwoPerfectTreeAction F)
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b) (P Q : Subgroup G)
    (hPN : RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b ≤ normalizer (P : Set G))
    (hQN : RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b ≤ normalizer (Q : Set G))
    (hcoverP : RankTwo.stabilizer F a ≤ P ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b))
    (hcoverQ : RankTwo.stabilizer F b ≤ Q ⊔ (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b)) :
    P ⊔ Q = ⊤ := by
  let H := P ⊔ Q
  let E := RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b
  have hgen : H ⊔ E = ⊤ := by
    apply top_unique
    rw [← h.toCubicTreeAction.adjacent_stabilizers_generate hab]
    exact sup_le (hcoverP.trans (sup_le_sup le_sup_left le_rfl))
      (hcoverQ.trans (sup_le_sup le_sup_right le_rfl))
  have hEN : E ≤ normalizer (H : Set G) :=
    (le_inf hPN hQN).trans (normalizer_inf_normalizer_le_normalizer_sup P Q)
  let : H.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le H.le_normalizer hEN))
  exact h.twoPerfect H inferInstance (isPGroup_quotient_of_sup_eq_top H E
    (h.toCubicTreeAction.edgeStabilizer_isPGroup hab) hgen)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
