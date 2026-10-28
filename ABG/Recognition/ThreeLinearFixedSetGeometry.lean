module
public import Theory.Combinatorics.UniqueIntersectionCounts
public import Theory.Combinatorics.ProjectivePlaneCollineation
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The geometry of Wong's four-line fixed sets

The points are the distinct fixed sets of elements of order three whose
centralizers have order 54. Incidence means that a line belongs to that fixed
set. Conjugation transports these sets, giving the actual induced action on
points and an incidence-preserving action.

The abstract geometric assembly consumes fixed-point counts and either
unique intersections or a lower bound on the fibers of the defining map.
It proves all incidence counts and constructs the plane on this relation.
`ThreeLinearPlane` derives these inputs from Wong's original linear-branch
hypotheses. Keeping the shared definitions here lets the character catalog
refer to the defining class without depending on that final assembly.

Source: Wong, *On finite groups whose 2-Sylow subgroups have cyclic subgroups
of index 2* (1964), Theorem 6(b), pp.110–111.
-/

namespace ABG.ThreeLinearPlane

open scoped Pointwise

variable (G L : Type*) [Group G] [MulAction G L]

/-- The original line action, tagged by its acting group for incidence inference. -/
@[expose] public def Line (_G : Type*) (L : Type*) := L

public instance lineAction : MulAction G (Line G L) :=
  inferInstanceAs (MulAction G L)

public instance lineFinite [Finite L] : Finite (Line G L) :=
  inferInstanceAs (Finite L)

public instance lineFaithful [FaithfulSMul G L] : FaithfulSMul G (Line G L) :=
  inferInstanceAs (FaithfulSMul G L)

/-- The order-three class that supplies Wong's points. -/
@[expose] public def IsPointElement (g : G) : Prop :=
  orderOf g = 3 ∧ Nat.card (Subgroup.centralizer ({g} : Set G)) = 54

private def centralizerEquiv (e : G ≃* G) (a : G) :
    Subgroup.centralizer ({a} : Set G) ≃ Subgroup.centralizer ({e a} : Set G) where
  toFun x := ⟨e x.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.property])⟩
  invFun x := ⟨e.symm x.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)

/-- The defining class is invariant under conjugation. -/
public theorem isPointElement_conj (a g : G) (hg : IsPointElement G g) :
    IsPointElement G (a * g * a⁻¹) := by
  have ho := (MulAut.conj a).orderOf_eq g
  have hc := Nat.card_congr (centralizerEquiv G (MulAut.conj a) g)
  exact ⟨ho.trans hg.1, hc.symm.trans hg.2⟩

/-- The invariant family of fixed sets, with duplicates identified as sets. -/
@[expose] public def pointFamily : SubMulAction G (Set (Line G L)) where
  carrier := {s | ∃ g : G, IsPointElement G g ∧ s = MulAction.fixedBy (Line G L) g}
  smul_mem' a := by
    rintro s ⟨g, hg, rfl⟩
    exact ⟨a * g * a⁻¹, isPointElement_conj G a g hg, MulAction.smul_fixedBy (Line G L) g a⟩

/-- Points are actual fixed subsets of the line type. -/
@[expose] public def Point := ↥(pointFamily G L)

public instance pointFinite [Finite L] : Finite (Point G L) :=
  inferInstanceAs (Finite ↥(pointFamily G L))

public instance pointAction : MulAction G (Point G L) :=
  inferInstanceAs (MulAction G ↥(pointFamily G L))

/-- A point is on a line precisely when that line belongs to its fixed set. -/
public instance incidence : Membership (Point G L) (Line G L) := ⟨fun l p => l ∈ p.val⟩

@[simp] public theorem mem_iff (p : Point G L) (l : Line G L) : p ∈ l ↔ l ∈ p.val := Iff.rfl

/-- Conjugation of the defining elements gives the collineation action. -/
public instance collineationAction : Configuration.IsCollineationAction G (Point G L) (Line G L) where
  smul_mem_smul_iff a p l := by
    change a • l ∈ a • p.val ↔ l ∈ p.val
    exact Set.smul_mem_smul_set_iff

/-- Each point has a defining element in the specified order-three class. -/
public theorem point_spec (p : Point G L) :
    ∃ g : G, IsPointElement G g ∧ p.val = MulAction.fixedBy (Line G L) g := p.property

/-- The fixed-set point defined by a qualifying element. -/
@[expose] public def pointOf (g : G) (hg : IsPointElement G g) : Point G L :=
  ⟨MulAction.fixedBy (Line G L) g, g, hg, rfl⟩

@[simp] public theorem pointOf_mem (g : G) (hg : IsPointElement G g) (l : Line G L) :
    pointOf G L g hg ∈ l ↔ g • l = l := Iff.rfl

/-- The character fixed-point count is the number of lines on a point. -/
public theorem lineCount_eq_four
    (hfour : ∀ g : G, IsPointElement G g → Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (p : Point G L) : Configuration.lineCount (Line G L) p = 4 := by
  obtain ⟨g, hg, heq⟩ := point_spec G L p
  change Nat.card {l : L // l ∈ p.val} = 4
  rw [heq]
  exact hfour g hg

/-- Transfer the group-theoretic pair assertion to the actual point type. -/
public theorem existsUnique_point
    (hex : ∀ l m : Line G L, l ≠ m → ∃ g : G,
      IsPointElement G g ∧ g • l = l ∧ g • m = m)
    (huniq : ∀ g h : G, IsPointElement G g → IsPointElement G h →
      ∀ l m : Line G L, l ≠ m → g • l = l → g • m = m → h • l = l → h • m = m →
        MulAction.fixedBy (Line G L) g = MulAction.fixedBy (Line G L) h)
    (l m : Line G L) (hne : l ≠ m) : ∃! p : Point G L, p ∈ l ∧ p ∈ m := by
  obtain ⟨g, hg, hgl, hgm⟩ := hex l m hne
  refine ⟨pointOf G L g hg, ⟨hgl, hgm⟩, ?_⟩
  intro p hp
  obtain ⟨h, hh, heq⟩ := point_spec G L p
  apply Subtype.ext
  change p.val = MulAction.fixedBy (Line G L) g
  rw [heq]
  have hhl : h • l = l := by
    have hl := hp.1
    change l ∈ p.val at hl
    simpa only [heq, MulAction.mem_fixedBy] using hl
  have hhm : h • m = m := by
    have hm := hp.2
    change m ∈ p.val at hm
    simpa only [heq, MulAction.mem_fixedBy] using hm
  exact huniq h g hh hg l m hne hhl hhm hgl hgm

/-- Double transitivity transports two of one element's four fixed lines to
any prescribed pair. -/
public theorem exists_point_of_two_pretransitive [Finite L]
    [MulAction.IsMultiplyPretransitive G L 2]
    (g : G) (hg : IsPointElement G g)
    (hfour : Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (l m : Line G L) (hne : l ≠ m) : ∃ p : Point G L, p ∈ l ∧ p ∈ m := by
  classical
  let : Fintype (MulAction.fixedBy (Line G L) g) := Fintype.ofFinite _
  have hgt : 1 < Fintype.card (MulAction.fixedBy (Line G L) g) := by
    rw [← Nat.card_eq_fintype_card, hfour]
    decide
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hgt
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  obtain ⟨x, hxa, hxb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp
      (inferInstance : MulAction.IsMultiplyPretransitive G L 2)) hab' hne
  refine ⟨x • pointOf G L g hg, ?_, ?_⟩
  · rw [← hxa]
    exact (Configuration.IsCollineationAction.smul_mem_smul_iff x _ _).mpr a.property
  · rw [← hxb]
    exact (Configuration.IsCollineationAction.smul_mem_smul_iff x _ _).mpr b.property

/-- Eight defining elements per fixed set and 104 elements in the class give
at most thirteen distinct fixed sets. -/
public theorem card_points_le_thirteen [Finite G] [Finite L]
    (hclass : Nat.card {g : G // IsPointElement G g} = 104)
    (hfibers : ∀ p : Point G L,
      8 ≤ Nat.card {g : {g : G // IsPointElement G g} // pointOf G L g.1 g.2 = p}) :
    Nat.card (Point G L) ≤ 13 := by
  classical
  let : Fintype (Point G L) := Fintype.ofFinite _
  let f : {g : G // IsPointElement G g} → Point G L := fun g => pointOf G L g.1 g.2
  have heq := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma, hclass] at heq
  have hle : Nat.card (Point G L) * 8 ≤ 104 := by
    calc
      _ = ∑ _p : Point G L, 8 := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
      _ ≤ ∑ p : Point G L, Nat.card {g : {g : G // IsPointElement G g} // f g = p} :=
        Finset.sum_le_sum (fun p _ => hfibers p)
      _ = 104 := heq
  omega

/-- Assemble the counts and plane after the two-line stabilizer argument. -/
public theorem plane_and_counts [Finite L] (hL : Nat.card L = 13)
    (hfour : ∀ g : G, IsPointElement G g → Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (hpair : ∀ l m : Line G L, l ≠ m → ∃! p : Point G L, p ∈ l ∧ p ∈ m) :
    Nonempty (Configuration.ProjectivePlane (Point G L) (Line G L)) ∧
      Nat.card (Point G L) = 13 ∧
      (∀ l : Line G L, Configuration.pointCount (Point G L) l = 4) ∧
      (∀ p : Point G L, Configuration.lineCount (Line G L) p = 4) := by
  have hlines := lineCount_eq_four G L hfour
  have hcard : Nat.card (Line G L) = 3 ^ 2 + 3 + 1 := hL
  exact ⟨⟨Configuration.projectivePlane_of_unique_intersections 3 (by decide) hcard hlines hpair⟩,
    Configuration.card_points_of_unique_intersections 3 (by decide) hcard hlines hpair,
    Configuration.pointCount_of_unique_intersections 3 (by decide) hcard hlines hpair, hlines⟩

/-- The alternative counting assembly needs eight defining elements per
fixed set, rather than a separate analysis of each pair stabilizer. -/
public theorem plane_and_counts_of_fibers [Finite G] [Finite L]
    [MulAction.IsMultiplyPretransitive G L 2]
    (hL : Nat.card L = 13)
    (hclass : Nat.card {g : G // IsPointElement G g} = 104)
    (hfour : ∀ g : G, IsPointElement G g → Nat.card (MulAction.fixedBy (Line G L) g) = 4)
    (hfibers : ∀ p : Point G L,
      8 ≤ Nat.card {g : {g : G // IsPointElement G g} // pointOf G L g.1 g.2 = p}) :
    Nonempty (Configuration.ProjectivePlane (Point G L) (Line G L)) ∧
      Nat.card (Point G L) = 13 ∧
      (∀ l : Line G L, Configuration.pointCount (Point G L) l = 4) ∧
      (∀ p : Point G L, Configuration.lineCount (Line G L) p = 4) := by
  have hn : Nonempty {g : G // IsPointElement G g} :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card {g : G // IsPointElement G g})).1
  obtain ⟨g, hg⟩ := hn
  have hex := exists_point_of_two_pretransitive G L g hg (hfour g hg)
  have hcard : Nat.card (Line G L) = 3 ^ 2 + 3 + 1 := hL
  have huniq := Configuration.unique_intersections_of_point_bound 3 hcard
    (card_points_le_thirteen G L hclass hfibers) (lineCount_eq_four G L hfour) hex
  exact plane_and_counts G L hL hfour huniq

end ABG.ThreeLinearPlane
