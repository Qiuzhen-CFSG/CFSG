module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Native
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.LongGirth

/-!
# Local geometry for full general Ree extension completions

The generic source extension retains the full automorphism carrier and its
whole overlap. Faithfulness of the native inner action and generation by the
native parabolics discharge the generic transport premises. The actual native
nine-path action and unequal valences therefore hold in every whole-overlap
completion. Thickness and the long-prefix girth argument make its eight-edge
nonbacktracking walks geodesic. No order or recognition hypothesis is used.

Source: Aschbacher–Smith F.4.3–6, printed pp.274–277.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon

/-- The F.4.3 full extension of the native linear/Suzuki amalgam. -/
abbrev SourceExtension (m : ℕ) :=
  UnitaryNonbinary.SourceExtension (ReeF4.Parabolics.parabolic m .linear)
    (ReeF4.Parabolics.parabolic m .suzuki)

/-- A completion of the full extension, not just its inner subgroup. -/
abbrev Completion {m : ℕ} (E : SourceExtension m) (M : Type*) [Group M] :=
  RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M)

private theorem native_generate (m : ℕ) :
    ReeF4.Parabolics.parabolic m .linear ⊔ ReeF4.Parabolics.parabolic m .suzuki = ⊤ := by
  rw [sup_comm]
  exact GreenBook.LieModels.ReeFour.parabolics_generate m

variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] (c : Completion E M)

theorem completion_connected : (graph c.cosetFamily).Connected :=
  RankTwo.connected c.cosetFamily c.generated

theorem completion_graphAction : GraphAction (graph c.cosetFamily) M where
  map_adj g := (translationGraphIso c.cosetFamily g).toHom.map_adj

/-- The local nine-path action includes the full extension carrier. -/
theorem completion_nine_transitive (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (v : Vertex c.cosetFamily) :
    RootPathTransitive (graph c.cosetFamily) M v 9 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hb := E.completion_rootPathTransitive_of_native (ReeF4.SmallCompletion.conj_injective m hm)
    (native_generate m) c hoverlap v.type 9
    (ReeF4.SourceCompletion.nine_transitive m hm _)
  simpa only [hg] using RootPathTransitive.smul (completion_graphAction E c) hb g

/-- The two marked valences are q+1 and q²+1, including q=8. -/
theorem completion_card_neighbors (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (v : Vertex c.cosetFamily) :
    Nat.card ((graph c.cosetFamily).neighborSet v) =
      (if v.type then (2^(2*m+1))^2 else 2^(2*m+1)) + 1 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hb := (E.completion_card_neighbors_eq_native (ReeF4.SmallCompletion.conj_injective m hm)
    (native_generate m) c hoverlap v.type).trans
    (ReeF4.SourceCompletion.card_neighbors m hm _)
  have hh := Nat.card_congr
    ((translationGraphIso c.cosetFamily g).mapNeighborSet (base c.cosetFamily v.type))
  change Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily v.type)) =
    Nat.card ((graph c.cosetFamily).neighborSet (g • base c.cosetFamily v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans hb

theorem completion_thick (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) : ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
  have hcard : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [completion_card_neighbors E c hm hoverlap]
    cases v.type <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
  let : Finite ((graph c.cosetFamily).neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite ((graph c.cosetFamily).neighborSet v)
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hcard
  by_contra hh
  push Not at hh
  have choices (w : (graph c.cosetFamily).neighborSet v) : w.val = a ∨ w.val = b := by
    by_cases ha : w.val = a
    · exact Or.inl ha
    · exact Or.inr (hh w.val w.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases choices x with hx | hx <;> rcases choices y with hy | hy <;>
    rcases choices z with hz | hz <;> simp_all

/-- Whole-overlap full-extension completions have girth at least sixteen. -/
theorem completion_cycle_length_ge_sixteen (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) (p : (graph c.cosetFamily).Walk v v) (hp : p.IsCycle) :
    16 ≤ p.length :=
  cycle_bound_of_long_root_transitivity (completion_graphAction E c)
    (completion_thick E c hm hoverlap) (by decide : 7 ≤ 9)
    (completion_nine_transitive E c hm hoverlap) (·.type) (fun h => h.1) v p hp

/-- Nonbacktracking eight-walks are actual geodesics before smallness. -/
theorem completion_eight_geodesic (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    {v : Vertex c.cosetFamily} (p : BasedWalk (graph c.cosetFamily) 8 v)
    (hp : p.Nonbacktracking) : (graph c.cosetFamily).dist v p.endpoint = 8 :=
  geodesic_of_half_girth (completion_connected E c)
    (completion_cycle_length_ge_sixteen E c hm hoverlap) p hp

/-- The full extension order bound cancels the matching endpoint orders. -/
theorem completion_card_coset_le [Finite M] (hm : 0 < m)
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤ ReeF4.SmallCompletion.cosetCount m i :=
  (E.completion_card_coset_le_native (ReeF4.SmallCompletion.conj_injective m hm)
    (native_generate m) c horder i).trans_eq (ReeF4.SmallCompletion.card_coset m hm i)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
