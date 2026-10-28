module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.TwoNeighborCore
public import Theory.GroupTheory.WeakBNPair.RegularTree.BallKernelCover

/-!
# Interior-star fixation by the actual linear path radicals

A path radical is a two-group fixing both neighbors at every interior turn.
The genuine original SL₂ markings place its image in the middle vertex
core. That core fixes the entire star. Local injectivity of the original
coset covering lifts this fixation to the universal tree; global
injectivity of the covering is not used.

The strict distance-two consumer supplies both endpoint markings from the
original hypotheses and applies this theorem to the literal six-path roots.
This is an input to the root-automorphism argument, not yet a Borel-image
root-sign theorem.
Source: DGS, *Groups and Graphs* (1985), (14.1)--(14.2), pp.210--211;
the local two-neighbor-core argument is the one used in (12.7), p.184.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.Walk
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_two_neighbor_core
    (h : HypothesisF11 L S)
    {k : Bool → Type*} [∀ i, Field (k i)] [∀ i, Finite (k i)] [∀ i, CharP (k i) 2]
    (e : ∀ i : Bool,
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k i))
    {m x y : Vertex (reducedFamily L S)}
    (hx : (graph (reducedFamily L S)).Adj m x)
    (hy : (graph (reducedFamily L S)).Adj m y)
    (hne : x ≠ y) (D : Subgroup (G₀ L S)) (hp : IsPGroup 2 D)
    (hm : D ≤ stabilizer (reducedFamily L S) m)
    (hDx : D ≤ stabilizer (reducedFamily L S) x)
    (hDy : D ≤ stabilizer (reducedFamily L S) y) : D ≤ Q (reducedFamily L S) m := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F m
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hx' : (graph F).Adj (base F m.type) (g⁻¹ • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hx
    change (graph F).Adj (g⁻¹ • m) (g⁻¹ • x) at hh
    rwa [←hg, inv_smul_smul] at hh
  have hy' : (graph F).Adj (base F m.type) (g⁻¹ • y) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hy
    change (graph F).Adj (g⁻¹ • m) (g⁻¹ • y) at hh
    rwa [←hg, inv_smul_smul] at hh
  have hm' : D.map c ≤ stabilizer F (base F m.type) := by
    have hh := map_mono (f := c) hm
    rw [←stabilizer_translate F, ←hg, inv_smul_smul] at hh
    exact hh
  have hD' : D.map c ≤ Q F (base F m.type) :=
    source_linear_two_neighbor_core h m.type (e m.type) hx' hy'
      (fun he => hne ((MulAction.toPerm g⁻¹).injective he))
      (D.map c) (hp.map c) hm'
      (by simpa only [stabilizer_translate] using map_mono (f := c) hDx)
      (by simpa only [stabilizer_translate] using map_mono (f := c) hDy)
  intro d hd
  have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom (hD' (mem_map_of_mem c hd))
  rw [←Q_translate F, hg] at hh
  change g * (g⁻¹ * d * g⁻¹⁻¹) * g⁻¹ ∈ Q F m at hh
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_inv_cancel, mul_one] using hh

/-- Every element of an actual path radical fixes the whole star of each interior vertex. -/
theorem linear_pathRoot_fixes_interior_stars
    (h : HypothesisF11 L S)
    {k : Bool → Type*} [∀ i, Field (k i)] [∀ i, Finite (k i)] [∀ i, CharP (k i) 2]
    (e : ∀ i : Bool,
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k i))
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath)
    (u : (reducedAmalgam L S).Universal)
    (hu : u ∈ pathRoot (X := (reducedAmalgam L S).Universal) p) :
    ∀ j, 0 < j → j < p.length →
      ∀ z, (sourceGraph (reducedAmalgam L S)).Adj (p.getVert j) z → u • z = z := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let R := pathRoot (X := (reducedAmalgam L S).Universal) p
  have hfix (j : ℕ) (hj : j ≤ p.length) :
      R.map f ≤ stabilizer (reducedFamily L S) (cov.vertex (p.getVert j)) := by
    rintro _ ⟨v, hv, rfl⟩
    change f v • cov.vertex (p.getVert j) = cov.vertex (p.getVert j)
    rw [← cov.vertex_smul]
    exact congrArg cov.vertex ((pCoreIn_le 2 _ hv) j hj)
  intro j hj hjl z hz
  have hprev := p.adj_getVert_succ (by omega : j - 1 < p.length)
  rw [show j - 1 + 1 = j by omega] at hprev
  have hnext := p.adj_getVert_succ hjl
  have hne : cov.vertex (p.getVert (j - 1)) ≠ cov.vertex (p.getVert (j + 1)) := by
    intro he
    have he' := (cov.neighbor_bijective (p.getVert j)).1
      (a₁ := ⟨_, hprev.symm⟩) (a₂ := ⟨_, hnext⟩) (Subtype.ext he)
    have hh := hp.getVert_injOn (by omega : j - 1 ≤ p.length)
      (by omega : j + 1 ≤ p.length) (congrArg Subtype.val he')
    omega
  have hcore := linear_two_neighbor_core h e
    (cov.hom.map_adj hprev.symm) (cov.hom.map_adj hnext) hne (R.map f)
    ((isPGroup_pCoreIn 2 (pathFixer (X := (reducedAmalgam L S).Universal) p)).map f)
    (hfix j (by omega)) (hfix (j-1) (by omega)) (hfix (j+1) (by omega))
  have hU := (source_Z_Q_U (reduced_triple h) _).2 (hcore (mem_map_of_mem f hu))
  exact cov.fixes_neighbor_of_image hz u ((pCoreIn_le 2 _ hu) j (by omega))
    (hU _ ((mem_ball_one _ _ _).mpr (Or.inl (cov.hom.map_adj hz))))

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
