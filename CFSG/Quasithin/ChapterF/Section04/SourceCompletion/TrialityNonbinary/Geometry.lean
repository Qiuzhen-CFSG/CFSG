module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts
public import Theory.SpecificGroups.Triality.SmallCompletion.NativeSeven
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.SevenGirth

/-!
# Full-extension local geometry for binary triality

The F.4.3 algebraic extension contract transports the genuine native seven-path
action and the unequal arms/central valences through the whole overlap.
Seven-path transitivity forces girth twelve. The full extension order bound
cancels the marked endpoint orders and gives the native bounds on both coset
spaces, with no restriction on the outer degree. This includes q=4.

Source: Aschbacher--Smith F.4.3--6 and F.4.24, pp.274--277,287--288.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

/-- The actual arms/central extension, retaining the full Borel overlap. -/
abbrev SourceExtension (m : ℕ) (hm : 0 < m) :=
  UnitaryNonbinary.SourceExtension (parabolic (binaryParameters m hm) .arms)
    (parabolic (binaryParameters m hm) .central)

abbrev Completion {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm) (M : Type*) [Group M] :=
  RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M)

theorem native_generate (m : ℕ) (hm : 0 < m) :
    parabolic (binaryParameters m hm) .arms ⊔ parabolic (binaryParameters m hm) .central = ⊤ :=
  parabolic_sup_binary _ rfl

theorem conj_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (MulAut.conj : BinaryCarrier m hm →* MulAut (BinaryCarrier m hm)) :=
  MulAut.conj_injective_of_center_eq_bot (binaryCarrier_center_eq_bot m hm)

theorem native_family (m : ℕ) (hm : 0 < m) :
    UnitaryNonbinary.SourceExtension.nativeFamily
      (P₀ := parabolic (binaryParameters m hm) .arms)
      (P₁ := parabolic (binaryParameters m hm) .central) = SmallCompletion.family m hm := by
  funext i
  cases i <;> rfl

variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)
variable {M : Type*} [Group M] (c : Completion E M)

theorem completion_connected : (graph c.cosetFamily).Connected :=
  RankTwo.connected c.cosetFamily c.generated

theorem completion_graphAction : GraphAction (graph c.cosetFamily) M where
  map_adj g := (translationGraphIso c.cosetFamily g).toHom.map_adj

/-- The local seven-path action includes the full extension carrier. -/
theorem completion_seven_transitive (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (v : Vertex c.cosetFamily) :
    RootPathTransitive (graph c.cosetFamily) M v 7 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hb := E.completion_rootPathTransitive_of_native (conj_injective m hm)
    (native_generate m hm) c hoverlap v.type 7
    (by rw [native_family]; exact SmallCompletion.seven_path_transitive m hm _)
  simpa only [hg] using RootPathTransitive.smul (completion_graphAction E c) hb g

/-- The two marked valences are q³+1 and q+1, including q=4. -/
theorem completion_card_neighbors (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) (v : Vertex c.cosetFamily) :
    Nat.card ((graph c.cosetFamily).neighborSet v) =
      SmallCompletion.degree m hm v.type := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hb := E.completion_card_neighbors_eq_native (conj_injective m hm)
    (native_generate m hm) c hoverlap v.type
  rw [native_family, SmallCompletion.base_neighbor_card] at hb
  have hh := Nat.card_congr
    ((translationGraphIso c.cosetFamily g).mapNeighborSet (base c.cosetFamily v.type))
  change Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily v.type)) =
    Nat.card ((graph c.cosetFamily).neighborSet (g • base c.cosetFamily v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans hb

theorem completion_thick (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : Vertex c.cosetFamily) : ∃ z, (graph c.cosetFamily).Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hq : 1 < (binaryParameters m hm).q := by
    rw [binaryParameters_q]
    exact Nat.one_lt_pow (by omega) (by decide)
  have hcard : 2 < Nat.card ((graph c.cosetFamily).neighborSet v) := by
    rw [completion_card_neighbors E c hoverlap]
    cases v.type <;> simp only [SmallCompletion.degree, Bool.false_eq_true, ↓reduceIte] <;> nlinarith [Nat.le_self_pow (by decide : 3 ≠ 0) (binaryParameters m hm).q]
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

/-- Whole-overlap full-extension completions have girth at least twelve. -/
theorem completion_cycle_length_ge_twelve (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) (p : (graph c.cosetFamily).Walk v v) (hp : p.IsCycle) :
    12 ≤ p.length :=
  cycle_bound_of_seven_transitive (completion_graphAction E c)
    (completion_thick E c hoverlap)
    (completion_seven_transitive E c hoverlap) (·.type) (fun h => h.1) v p hp

/-- The full extension order bound cancels the matching endpoint orders. -/
theorem completion_card_coset_le [Finite M] (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤ SmallCompletion.cosetCount m hm i :=
  (E.completion_card_coset_le_native (conj_injective m hm)
    (native_generate m hm) c horder i).trans_eq (by rw [native_family]; exact SmallCompletion.card_coset m hm i)

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
