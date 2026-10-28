module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound.OrbitBound.Geometry
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.List.Perm.Basic

/-!
# Counting automorphisms of the homology sum graph by invariant colors

Individualization restricts to a point stabilizer. Every permutation preserving
the sum graph and a coloring preserves its weighted neighbor-color sum.
A checked discrimination table therefore proves preservation of a refined
coloring. Orbit-stabilizer bounds each successive index by the size of the
pivot's cell; an injective final coloring makes the last stabilizer trivial.

The counting argument follows the repository's HS GraphOrder.Basic development.
It applies here to the full permutation group preserving OrbitGeometry.Adj.
The numerical trace in ImageBound/source/refinement.json remains an untrusted
witness until a certificate module checks it. Source motivation and ATLAS
attribution are recorded in ImageBound/source/README.md.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Refinement

/-- The pointwise stabilizer of a list of vertices in the full graph group. -/
def fixing (xs : List (Vertex)) : Subgroup (Equiv.Perm (Vertex)) where
  carrier := {g | g ∈ preservingGroup ∧ ∀ x ∈ xs, g x = x}
  one_mem' := ⟨preservingGroup.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨hg, hx⟩ ⟨hh, hy⟩
    exact ⟨preservingGroup.mul_mem hg hh, fun x hmem => by
      change g (h x) = x
      rw [hy x hmem, hx x hmem]⟩
  inv_mem' := by
    rintro g ⟨hg, hx⟩
    exact ⟨preservingGroup.inv_mem hg, fun x hmem => by
      apply g.injective
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using (hx x hmem).symm⟩

theorem mem_fixing (xs : List (Vertex)) (g : Equiv.Perm (Vertex)) :
    g ∈ fixing xs ↔ g ∈ preservingGroup ∧ ∀ x ∈ xs, g x = x := Iff.rfl

theorem fixing_nil : fixing [] = preservingGroup := by
  ext g
  simp only [mem_fixing, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]

def Preserves (xs : List (Vertex)) (c : Vertex → ℕ) : Prop :=
  ∀ g ∈ fixing xs, ∀ x, c (g x) = c x

/-- Count neighbors in a selected invariant cell. -/
def neighborCount (s : List Vertex) (x : Vertex) : ℕ :=
  s.countP (fun y => decide (Adj x y))

theorem neighborCount_invariant (g : Equiv.Perm Vertex) (hg : g ∈ preservingGroup)
    (s : List Vertex) (hs : s.Nodup) (hc : ∀ x, g x ∈ s ↔ x ∈ s) (x : Vertex) :
    neighborCount s (g x) = neighborCount s x := by
  have he : (s.map g).Perm s := by
    apply (List.perm_ext_iff_of_nodup (hs.map g.injective) hs).mpr
    intro y
    obtain ⟨z, rfl⟩ := g.surjective y
    simpa only [List.mem_map, g.injective.eq_iff, exists_eq_right] using (hc z).symm
  unfold neighborCount
  rw [← he.countP_eq, List.countP_map]
  apply List.countP_congr
  intro y _
  simpa only [Function.comp_apply, decide_eq_true_eq] using hg x y

/-- Refining by neighbor counts in one old color cell preserves invariance.
The new labels may be compressed; only their discrimination property is needed. -/
theorem preserves_count_refinement {xs : List Vertex} {c d : Vertex → ℕ}
    (hc : Preserves xs c) (s : List Vertex) (hs : s.Nodup) (tag : ℕ)
    (hcell : ∀ x, x ∈ s ↔ c x = tag)
    (hd : ∀ x y, c x = c y → neighborCount s x = neighborCount s y → d x = d y) :
    Preserves xs d := by
  intro g hg x
  apply hd (g x) x (hc g hg x)
  apply neighborCount_invariant g hg.1 s hs
  intro y
  rw [hcell, hcell, hc g hg]

/-- A weighted encoding of neighbor counts. Its invariance does not require
injectivity of the encoding: discrimination is checked separately. -/
def signature (c : Vertex → ℕ) (x : Vertex) : ℕ :=
  ∑ y : Vertex, if Adj x y then 1024 ^ c y else 0

theorem signature_invariant (c : Vertex → ℕ) (g : Equiv.Perm (Vertex))
    (hg : g ∈ preservingGroup) (hc : ∀ x, c (g x) = c x) (x : Vertex) :
    signature c (g x) = signature c x := by
  unfold signature
  symm
  apply Fintype.sum_equiv g
  intro y
  simp only [show ∀ x y, Adj (g x) (g y) ↔ Adj x y from hg, hc]

theorem preserves_refine {xs : List (Vertex)} {c d s : Vertex → ℕ}
    (hc : Preserves xs c) (hs : ∀ x, signature c x = s x)
    (hd : ∀ x y, c x = c y → s x = s y → d x = d y) : Preserves xs d := by
  intro g hg x
  apply hd (g x) x (hc g hg x)
  rw [← hs, ← hs]
  exact signature_invariant c g hg.1 (hc g hg) x

theorem preserves_individualize {xs : List (Vertex)} {c d : Vertex → ℕ}
    (hc : Preserves xs c) (v : Vertex)
    (hd : ∀ x y, c x = c y → (x = v ↔ y = v) → d x = d y) :
    Preserves (v :: xs) d := by
  intro g hg x
  have hfix : g v = v := hg.2 v (by simp)
  have hxs : g ∈ fixing xs := ⟨hg.1, fun y hy => hg.2 y (by simp [hy])⟩
  apply hd (g x) x (hc g hxs x)
  exact ⟨fun h => g.injective (h.trans hfix.symm), fun h => h ▸ hfix⟩

def cellSize (c : Vertex → ℕ) (v : Vertex) : ℕ :=
  (Finset.univ.filter (fun x => c x = c v)).card

theorem card_fixing_le {xs : List (Vertex)} {c : Vertex → ℕ}
    (hc : Preserves xs c) (v : Vertex) :
    Nat.card (fixing xs) ≤ cellSize c v * Nat.card (fixing (v :: xs)) := by
  classical
  let e : MulAction.stabilizer (fixing xs) v ≃ fixing (v :: xs) := {
    toFun := fun g => ⟨g.val.val, g.val.property.1, by
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst x
        exact g.property
      · exact g.val.property.2 x h⟩
    invFun := fun g => ⟨⟨g.val, g.property.1, fun x hx =>
      g.property.2 x (List.mem_cons_of_mem v hx)⟩,
      g.property.2 v (List.mem_cons_self)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have horbit : Nat.card (MulAction.orbit (fixing xs) v) ≤ cellSize c v := by
    let f : MulAction.orbit (fixing xs) v → {x : Vertex // c x = c v} := fun x =>
      ⟨x.val, by
        obtain ⟨g, hg⟩ := x.property
        rw [← hg]
        exact hc g.val g.property v⟩
    have h := Nat.card_le_card_of_injective f (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {x : Vertex // c x = c v} => z.val) h))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, cellSize] using h
  calc
    Nat.card (fixing xs) =
        Nat.card (MulAction.orbit (fixing xs) v) *
          Nat.card (MulAction.stabilizer (fixing xs) v) :=
      (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (fixing xs) v)).symm.trans
        (Nat.card_prod _ _)
    _ ≤ cellSize c v * Nat.card (fixing (v :: xs)) := by
      rw [Nat.card_congr e]
      exact Nat.mul_le_mul_right _ horbit

theorem card_fixing_eq_one {xs : List (Vertex)} {c : Vertex → ℕ}
    (hc : Preserves xs c) (hinj : Function.Injective c) : Nat.card (fixing xs) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1, ?_⟩
  intro g
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact hinj (hc g.val g.property x)

/-- The six individualizations in the supplied trace give the required full
permutation-group bound once their invariant colors have been checked. -/
theorem preservingGroup_card_le_of_colors
    (c₁ c₂ c₃ c₄ c₅ c₆ : Vertex → ℕ)
    (h₁ : Preserves [0] c₁)
    (h₂ : Preserves [73, 0] c₂)
    (h₃ : Preserves [33, 73, 0] c₃)
    (h₄ : Preserves [10, 33, 73, 0] c₄)
    (h₅ : Preserves [143, 10, 33, 73, 0] c₅)
    (h₆ : Preserves [1, 143, 10, 33, 73, 0] c₆)
    (n₁ : cellSize c₁ 73 = 2)
    (n₂ : cellSize c₂ 33 = 30)
    (n₃ : cellSize c₃ 10 = 4)
    (n₄ : cellSize c₄ 143 = 8)
    (n₅ : cellSize c₅ 1 = 2)
    (hinj : Function.Injective c₆) : Nat.card preservingGroup ≤ 2661120 := by
  have h₀ : Preserves [] (fun _ => 0) := by intro _ _ _; rfl
  have b₀ := card_fixing_le h₀ 0
  have n₀ : cellSize (fun _ => 0) 0 = 693 := by simp [cellSize]
  rw [fixing_nil, n₀] at b₀
  have b₁ := card_fixing_le h₁ 73
  have b₂ := card_fixing_le h₂ 33
  have b₃ := card_fixing_le h₃ 10
  have b₄ := card_fixing_le h₄ 143
  have b₅ := card_fixing_le h₅ 1
  rw [n₁] at b₁
  rw [n₂] at b₂
  rw [n₃] at b₃
  rw [n₄] at b₄
  rw [n₅] at b₅
  have b₆ := card_fixing_eq_one h₆ hinj
  omega

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.OrbitGeometry.Refinement
