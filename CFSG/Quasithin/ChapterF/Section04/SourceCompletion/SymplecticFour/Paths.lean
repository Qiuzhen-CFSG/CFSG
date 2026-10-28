module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Faithfulness
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Apartment
public import Theory.SpecificGroups.SymplecticFour.FlagPaths.Size
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# Five-path actions and the order census for genuine symplectic extensions

The exact inner intersections and inner-times-middle factorization identify
the extension's flag geometry with the native matrix geometry. Its proved
five-path action transfers through the actual universal common cover to
any faithful completion with whole overlap. All valences and finite path
counts transfer with it.

The full extension order bound bounds the number of typed vertices by
2(q + 1)(q² + 1). For q > 2 this is smaller than the rooted four-path
census (q + 1)q³, forcing distinct four-paths with a common endpoint.
This argument retains the extension degree in the group-order hypothesis.
It does not assert geodesicity, quadrangle recognition, or an identification
of the completion with a diagram-preserving extension.

Source: Aschbacher–Smith F.4.3–6 and F.4.24, printed pp.274–277,287–288
of `refs/quasithin.pdf`. The literal original-normalizer consumers are in
the Chapter6 and Chapter12 symplectic completion modules.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]
namespace SourceExtension
variable (E : SourceExtension F)

def innerMap : Sp F →* E.carrier :=
  (MulAut.conj : Sp F →* MulAut (Sp F)).codRestrict E.carrier
    (fun g => E.contains_inner ⟨g,rfl⟩)

theorem innerMap_injective : Function.Injective E.innerMap := by
  intro g h he
  exact inner_injective (F := F) (congrArg Subtype.val he)

private theorem preimage_inner (P : Subgroup (Sp F)) (Q : Subgroup (MulAut (Sp F)))
    (h : Q ⊓ inner F = P.map MulAut.conj) : Q.comap MulAut.conj = P := by
  ext g
  change MulAut.conj g ∈ Q ↔ g ∈ P
  constructor
  · intro hg
    have hm : MulAut.conj g ∈ Q ⊓ inner F := ⟨hg,⟨g,rfl⟩⟩
    rw [h] at hm
    obtain ⟨b,hb,he⟩ := hm
    exact inner_injective (F := F) he ▸ hb
  · intro hg
    exact (h.ge ⟨g,hg,rfl⟩).1

theorem innerMap_comap (i : Bool) :
    (E.modelCompletion.cosetFamily i).comap E.innerMap = FlagPaths.family i := by
  cases i
  · change E.modelCompletion.left.range.comap E.innerMap = pointParabolic
    rw [E.model_left_range]
    exact preimage_inner pointParabolic E.left E.left_inner
  · change E.modelCompletion.right.range.comap E.innerMap = planeParabolic
    rw [E.model_right_range]
    exact preimage_inner planeParabolic E.right E.right_inner

omit [CharP F 2] in
theorem innerMap_representative (a : E.carrier) :
    ∃ g : Sp F, (E.innerMap g)⁻¹ * a ∈
      E.modelCompletion.cosetFamily false ⊓ E.modelCompletion.cosetFamily true := by
  obtain ⟨g,b,hb,he⟩ := E.factor a.val a.property
  refine ⟨g,?_⟩
  have hh : (E.innerMap g)⁻¹ * a = ⟨b,E.left_le hb.1⟩ := by
    apply Subtype.ext
    change (MulAut.conj g)⁻¹ * a.val = b
    rw [he,inv_mul_cancel_left]
  rw [hh]
  change (⟨b,E.left_le hb.1⟩ : E.carrier) ∈ E.modelCompletion.left.range ⊓ E.modelCompletion.right.range
  rw [E.model_left_range,E.model_right_range]
  exact hb

/-- The actual matrix flag graph is unchanged by a genuine extension. -/
def nativeGraphIso : graph (FlagPaths.family (F := F)) ≃g graph E.modelCompletion.cosetFamily :=
  ExtensionGeometry.graphIso _ _ E.innerMap E.innerMap_comap E.innerMap_representative

theorem nativeGraphIso_base (i : Bool) :
    E.nativeGraphIso (base FlagPaths.family i) = base E.modelCompletion.cosetFamily i :=
  ExtensionGeometry.vertex_base _ _ _ _ i

theorem nativeGraphIso_smul (g : Sp F) (v : Vertex (FlagPaths.family (F := F))) :
    E.nativeGraphIso (g • v) = E.innerMap g • E.nativeGraphIso v :=
  ExtensionGeometry.vertex_smul _ _ _ _ g v

/-- F.4.5(7) for the genuine extension, with no restriction on its outer degree. -/
theorem rootPathTransitive_five [Finite F] (i : Bool) :
    RootPathTransitive (graph E.modelCompletion.cosetFamily) E.carrier
      (base E.modelCompletion.cosetFamily i) 5 := by
  rw [←E.nativeGraphIso_base i]
  exact RootPathTransitive.map_graphIso E.nativeGraphIso E.innerMap E.nativeGraphIso_smul
    (FlagPaths.rootPathTransitive_five i)

theorem card_model_neighbors [Finite F] (v : Vertex E.modelCompletion.cosetFamily) :
    Nat.card ((graph E.modelCompletion.cosetFamily).neighborSet v) = Nat.card F + 1 := by
  obtain ⟨w,rfl⟩ := E.nativeGraphIso.surjective v
  exact (Nat.card_congr (E.nativeGraphIso.mapNeighborSet w)).symm.trans (FlagPaths.card_neighbors w)
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)
variable (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)

include hoverlap in
/-- F.4.6(1): transfer the proved native action through the actual whole overlap. -/
theorem rootPathTransitive_five [Finite F] (i : Bool) :
    RootPathTransitive (graph c.cosetFamily) M (base c.cosetFamily i) 5 :=
  (c.rootPathTransitive_iff hoverlap i 5).mp (E.rootPathTransitive_five i)

include hoverlap in
theorem all_rootPathTransitive_five [Finite F] (v : Vertex c.cosetFamily) :
    RootPathTransitive (graph c.cosetFamily) M v 5 := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base c.cosetFamily v
  rw [←hg]
  exact RootPathTransitive.smul
    (⟨fun g _ _ h => (CosetGeometry.translationGraphIso c.cosetFamily g).toHom.map_adj h⟩ :
      GraphAction (graph c.cosetFamily) M)
    (c.rootPathTransitive_five hoverlap v.type) g

omit [CharP F 2] in
theorem card_endpoint_eq_model (i : Bool) :
    Nat.card (c.cosetFamily i) = Nat.card (E.modelCompletion.cosetFamily i) := by
  cases i
  · exact (Nat.card_congr (MonoidHom.ofInjective c.left_injective).toEquiv).symm.trans
      (Nat.card_congr (MonoidHom.ofInjective E.modelCompletion.left_injective).toEquiv)
  · exact (Nat.card_congr (MonoidHom.ofInjective c.right_injective).toEquiv).symm.trans
      (Nat.card_congr (MonoidHom.ofInjective E.modelCompletion.right_injective).toEquiv)

omit [CharP F 2] in
/-- The full extension order bound descends to the entire typed vertex set. -/
theorem card_vertices_le_model [Finite F] [Finite M]
    (hcard : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card (Vertex c.cosetFamily) ≤ Nat.card (Vertex E.modelCompletion.cosetFamily) := by
  have hi (i : Bool) : (c.cosetFamily i).index ≤ (E.modelCompletion.cosetFamily i).index := by
    have hh : Nat.card (c.cosetFamily i) * (c.cosetFamily i).index ≤
        Nat.card (c.cosetFamily i) * (E.modelCompletion.cosetFamily i).index := by
      calc
        Nat.card (c.cosetFamily i) * (c.cosetFamily i).index = Nat.card M :=
          (c.cosetFamily i).card_mul_index
        _ ≤ Nat.card E.carrier := hcard
        _ = Nat.card (c.cosetFamily i) * (E.modelCompletion.cosetFamily i).index := by
          rw [c.card_endpoint_eq_model, Subgroup.card_mul_index]
    exact Nat.le_of_mul_le_mul_left hh Nat.card_pos
  rw [Nat.card_congr (vertexEquivSum c.cosetFamily),
    Nat.card_congr (vertexEquivSum E.modelCompletion.cosetFamily), Nat.card_sum, Nat.card_sum]
  exact Nat.add_le_add (hi false) (hi true)

/-- Cancel the outer extension degree only in the coset count, where the
same degree occurs in the ambient group and both full vertex stabilizers. -/
theorem card_vertices_le [Finite F] [Finite M]
    (hcard : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card (Vertex c.cosetFamily) ≤ 2 * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) := by
  have hm : Nat.card (Vertex E.modelCompletion.cosetFamily) =
      2 * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) :=
    (Nat.card_congr E.nativeGraphIso.toEquiv).symm.trans FlagPaths.card_vertices
  exact (c.card_vertices_le_model hcard).trans_eq hm

include hoverlap in
/-- The full-intersection covering preserves the native valence at every source vertex. -/
theorem card_neighbors [Finite F] (v : Vertex c.cosetFamily) :
    Nat.card ((graph c.cosetFamily).neighborSet v) = Nat.card F + 1 := by
  let u := RankTwoAmalgam.Universal.cosetFamily E.amalgam
  let d₀ := RankTwoAmalgam.Universal.coverData_of_overlap E.amalgam E.modelCompletion E.model_overlap
  let d₁ := RankTwoAmalgam.Universal.coverData_of_overlap E.amalgam c hoverlap
  have hbase (i : Bool) : Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily i)) =
      Nat.card F + 1 := by
    have h₀ := Nat.card_congr (Equiv.ofBijective _ (d₀.neighbor_bijective (base u i)))
    have h₁ := Nat.card_congr (Equiv.ofBijective _ (d₁.neighbor_bijective (base u i)))
    change Nat.card ((graph u).neighborSet (base u i)) =
      Nat.card ((graph E.modelCompletion.cosetFamily).neighborSet (d₀.vertex (base u i))) at h₀
    change Nat.card ((graph u).neighborSet (base u i)) =
      Nat.card ((graph c.cosetFamily).neighborSet (d₁.vertex (base u i))) at h₁
    rw [CoverData.vertex_base] at h₀ h₁
    exact h₁.symm.trans (h₀.trans (E.card_model_neighbors _))
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base c.cosetFamily v
  have hh := Nat.card_congr ((CosetGeometry.translationGraphIso c.cosetFamily g).mapNeighborSet
    (base c.cosetFamily v.type))
  change Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily v.type)) =
    Nat.card ((graph c.cosetFamily).neighborSet (g • base c.cosetFamily v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (hbase v.type)

include hoverlap in
/-- The actual completion has the native census at every finite path length,
including the four-path census needed for the smallness argument. -/
theorem card_paths [Finite F] (k : ℕ) (v : Vertex c.cosetFamily) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) (k+1) v // p.Nonbacktracking} =
      (Nat.card F + 1) * Nat.card F ^ k := by
  have hf {v w : Vertex c.cosetFamily} (h : (graph c.cosetFamily).Adj v w) : w.type = !v.type := by
    have hne := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have : ∀ v : Vertex c.cosetFamily, Finite ((graph c.cosetFamily).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [c.card_neighbors hoverlap]; omega)
  rw [BasedWalk.card_nonbacktracking_succ (graph c.cosetFamily) (fun v => v.type)
    (fun _ => Nat.card F + 1) hf (c.card_neighbors hoverlap)]
  congr 1
  generalize (!v.type) = b
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp [BasedWalk.forwardCount, ih, pow_succ, mul_comm]
include hoverlap in
/-- The full source order bound already forces two distinct native-length
four-paths with the same endpoint. Geodesicity is a separate metric step. -/
theorem four_path_collision [Finite F] [Finite M]
    (hq : 2 < Nat.card F) (hcard : Nat.card M ≤ Nat.card E.carrier)
    (v : Vertex c.cosetFamily) :
    ∃ p q : BasedWalk (graph c.cosetFamily) 4 v,
      p.Nonbacktracking ∧ q.Nonbacktracking ∧ p ≠ q ∧ p.endpoint = q.endpoint := by
  have hc : Nat.card (Vertex c.cosetFamily) <
      Nat.card {p : BasedWalk (graph c.cosetFamily) 4 v // p.Nonbacktracking} := by
    rw [c.card_paths hoverlap 3]
    apply (c.card_vertices_le hcard).trans_lt
    have hmul := Nat.mul_le_mul_right (Nat.card F ^ 2) (show 3 ≤ Nat.card F by omega)
    have hpow : 2 * (Nat.card F ^ 2 + 1) < Nat.card F ^ 3 := by nlinarith
    have hh := Nat.mul_lt_mul_of_pos_left hpow (show 0 < Nat.card F + 1 by omega)
    nlinarith
  have : Finite (Vertex c.cosetFamily) :=
    Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hn : ¬ Function.Injective
      (fun p : {p : BasedWalk (graph c.cosetFamily) 4 v // p.Nonbacktracking} => p.val.endpoint) := by
    intro hi
    exact (Nat.not_lt_of_ge (Nat.card_le_card_of_injective _ hi)) hc
  obtain ⟨p,q,he,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨p.val,q.val,p.property,q.property,fun hh => hne (Subtype.ext hh),he⟩
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
