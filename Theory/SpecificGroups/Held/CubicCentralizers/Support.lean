module
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality.Permutations
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.GraphTable

/-! Invariant cells in the literal Held relation bound the centralizer
of a specified permutation. Fixed points, adjacency to the image, and complete
cell neighbor counts are preserved. The existing four-point graph base closes
the orbit–stabilizer chain. Applied below to the two cubic representatives.
Source: ATLAS HeG1-p2058B0; Aschbacher–Smith 2.4.25, p.543. -/

@[expose] public section
namespace Held.CubicCentralizers
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open scoped BigOperators

variable (p : Equiv.Perm (Fin 2058))

def graphCentralizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ Subgroup.centralizer ({p} : Set (Equiv.Perm (Fin 2058)))

def Invariant (n : ℕ) (w : ℕ → ℕ) : Prop :=
  ∀ σ ∈ graphCentralizer p, Fixes n σ → ∀ x, w (σ x).val = w x.val

theorem commutes_point (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer p)
    (x : Fin 2058) : p (σ x) = σ (p x) :=
  congrArg (fun p : Equiv.Perm (Fin 2058) => p x)
    (Subgroup.mem_centralizer_singleton_iff.mp hσ.2).symm

def initial (bs : List (Fin 2058)) (x : Fin 2058) : ℕ :=
  (if p x = x then 2 else if Adj x (p x) then 1 else 0) +
    4 * baseSignature (bs ++ bs.map p ++ (bs.map p).map p) x

theorem initial_invariant (bs : List (Fin 2058))
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer p)
    (hf : ∀ b ∈ bs, σ b = b) (x : Fin 2058) :
    initial p bs (σ x) = initial p bs x := by
  have he : p (σ x) = σ x ↔ p x = x := by
    rw [commutes_point p σ hσ]
    exact σ.injective.eq_iff
  have ha : Adj (σ x) (p (σ x)) ↔ Adj x (p x) := by
    rw [commutes_point p σ hσ]
    exact hσ.1 x (p x)
  have hp : ∀ b ∈ bs.map p, σ b = b := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    rw [←commutes_point p σ hσ,hf c hc]
  have hbs : ∀ b ∈ bs ++ bs.map p ++ (bs.map p).map p, σ b = b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact hf b hb
      · exact hp b hb
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      rw [←commutes_point p σ hσ,hp c hc]
  simp only [initial, he, ha, baseSignature_invariant _ σ hσ.1 hbs]

theorem initial_labels_invariant (n : ℕ) (bs : List (Fin 2058))
    (hb : ∀ b ∈ bs, b.val < n) (w : ℕ → ℕ)
    (hc : ∀ x : Fin 2058, w x.val = initial p bs x) : Invariant p n w := by
  intro σ hσ hf x
  rw [hc, hc, initial_invariant p bs σ hσ (fun b h => hf b (hb b h))]

def neighborCount (S : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  ∑ y ∈ S, if Adj x y then 1 else 0

theorem neighborCount_invariant {n : ℕ} {w : ℕ → ℕ}
    (hw : Invariant p n w) (S : Finset (Fin 2058)) (a : ℕ)
    (hS : ∀ x, x ∈ S ↔ w x.val = a)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ graphCentralizer p) (hf : Fixes n σ)
    (x : Fin 2058) : neighborCount S (σ x) = neighborCount S x := by
  unfold neighborCount
  symm
  apply Finset.sum_bij (fun y _ => σ y)
  · intro y hy
    apply (hS _).mpr
    rw [hw σ hσ hf]
    exact (hS _).mp hy
  · intro y _ z _ h
    exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    apply (hS _).mpr
    have he := hw σ hσ hf (σ.symm y)
    rw [σ.apply_symm_apply] at he
    exact he.symm.trans ((hS _).mp hy)
  · intro y _
    simp only [hσ.1 x y]

theorem narrow_function {n : ℕ} {w v : ℕ → ℕ}
    (hw : Invariant p n w) (f : Fin 2058 → ℕ)
    (hf : ∀ σ ∈ graphCentralizer p, Fixes n σ → ∀ x, f (σ x) = f x)
    (a s : ℕ)
    (hc : ∀ x : Fin 2058,
      v x.val = if w x.val = a ∧ f x = s then 1 else 0) : Invariant p n v := by
  intro σ hσ hfix x
  rw [hc, hc, hw σ hσ hfix x, hf σ hσ hfix x]

public theorem sample_spec_of_count (w : ℕ → ℕ) (a : ℕ)
    (S : Finset (Fin 2058)) (hS : ∀ x ∈ S, w x.val = a)
    (hc : (List.finRange 2058).countP (fun x => w x.val == a) ≤ S.card) :
    ∀ x, x ∈ S ↔ w x.val = a := by
  classical
  let C := Finset.univ.filter (fun x : Fin 2058 => w x.val = a)
  have hsub : S ⊆ C := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS x hx⟩
  have hcard : C.card ≤ S.card := by
    simpa only [C, ← List.toFinset_finRange 2058,
      (List.nodup_finRange 2058).card_eq_countP, Bool.beq_eq_decide_eq] using hc
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  intro x
  rw [he]
  simp [C]

private abbrev S0 := ↥(graphCentralizer p)
private abbrev S1 := ↥(MulAction.stabilizer (S0 p) (0 : Fin 2058))
private abbrev S2 := ↥(MulAction.stabilizer (S1 p) (1 : Fin 2058))
private abbrev S3 := ↥(MulAction.stabilizer (S2 p) (2 : Fin 2058))
private abbrev S4 := ↥(MulAction.stabilizer (S3 p) (3 : Fin 2058))

private theorem fix1 (g : S1 p) : Fixes 1 g.val.val := by
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact g.property

private theorem fix2 (g : S2 p) : Fixes 2 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 1
  · exact fix1 p g.val x h
  · have he : x = 1 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix3 (g : S3 p) : Fixes 3 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 p g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 (g : S4 p) : Fixes 4 g.val.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 p g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

public theorem card_le_of_cells (w : Fin 4 → ℕ → ℕ) (c : Fin 4 → ℕ)
    (hw : ∀ n, Invariant p n.val (w n))
    (hc : ∀ n, Nat.card {x : Fin 2058 // w n x.val = w n n.val} ≤ c n) :
    Nat.card (graphCentralizer p) ≤ c 0 * (c 1 * (c 2 * c 3)) := by
  have h4 : Nat.card (S4 p) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ g.val.val.val.val.property.1 (fix4 p g)
  have h3 : Nat.card (S3 p) ≤ c 3 * Nat.card (S4 p) :=
    orbit_upper (3 : Fin 2058) (fun x => w 3 x.val)
      (fun g x => hw 3 _ g.val.val.val.property (fix3 p g) x) (hc 3)
  have h2 : Nat.card (S2 p) ≤ c 2 * Nat.card (S3 p) :=
    orbit_upper (2 : Fin 2058) (fun x => w 2 x.val)
      (fun g x => hw 2 _ g.val.val.property (fix2 p g) x) (hc 2)
  have h1 : Nat.card (S1 p) ≤ c 1 * Nat.card (S2 p) :=
    orbit_upper (1 : Fin 2058) (fun x => w 1 x.val)
      (fun g x => hw 1 _ g.val.property (fix1 p g) x) (hc 1)
  have h0 : Nat.card (S0 p) ≤ c 0 * Nat.card (S1 p) :=
    orbit_upper (0 : Fin 2058) (fun x => w 0 x.val)
      (fun g x => hw 0 _ g.property (by intro x hx; omega) x) (hc 0)
  rw [h4, mul_one] at h3
  exact h0.trans (Nat.mul_le_mul_left _
    (h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3)))))


end Held.CubicCentralizers
