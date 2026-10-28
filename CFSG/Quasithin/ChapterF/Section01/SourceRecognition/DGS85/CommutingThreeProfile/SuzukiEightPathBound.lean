module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullCoreUpper
public import Theory.GroupTheory.AmalgamGraph.OddPathExtensionBound
/-!
# The exact two-subgroup bound on a linear-ended eight-path

The source's odd nine-path fixer makes every two-subgroup of an eight-path
fixer act freely on its preceding extensions. The actual quotient markings
give q extensions at a linear endpoint, hence order at most q. This bound
uses the full path fixer and preserves the literal completion inclusion.
It supplies the numerical step in the nonbinary torus-centralizer argument;
the placement of that centralizer in a suitable eight-path fixer remains
a separate geometric obligation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7) and proof of (12.9), printed pp.184,189.
-/
public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- Every two-subgroup fixing a linear-ended eight-path has order at most q. -/
theorem source_suzuki_eight_path_two_subgroup_bound
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 8 v₀) (hp : p.Nonbacktracking)
    (hvi : v₀.type = i) (D : Subgroup (G₀ L S)) (hD : IsPGroup 2 D)
    (hfix : D ≤ pathStabilizer (reducedFamily L S) p) :
    Nat.card D ≤ Nat.card k ∧ Nat.card (D.map (G₀ L S).subtype) ≤ Nat.card k := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hval : Nat.card ((graph F).neighborSet v₀) = Nat.card k + 1 := by
    simpa [hvi,←hfield] using
      source_linear_suzuki_neighbor_cards h i e eSuz hfield v₀
  have hbound : Nat.card D ≤ Nat.card k := by
    have hh := two_subgroup_card_le_preceding_degree_of_odd_extensions F
      (n := 7) p (by rw [hval]; have := Nat.card_pos (α := k); omega)
      (fun {z} hzadj hzne =>
        (source_suzuki_every_nine_path_odd h i hb3 T hT e hz hcard hcardy
          hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
          (⟨⟨v₀,hzadj⟩,p⟩ : BasedWalk (graph F) 9 z) ⟨hzne.symm,hp⟩).1) D hD hfix
    simpa only [hval,Nat.add_sub_cancel] using hh
  exact ⟨hbound,by rw [card_map_of_injective (G₀ L S).subtype_injective]; exact hbound⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
