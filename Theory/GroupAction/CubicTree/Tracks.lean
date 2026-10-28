module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Order.Interval.Set.OrdConnectedLinear
/-!
# Translation tracks and their fixed intervals in a tree

Two elements fixing adjacent vertices and moving the opposite vertex construct
an embedded integer line. Their product translates the line by two, and
involutory choices reflect it about the original vertices. The proof constructs
the alternating sequence explicitly; acyclicity turns its nonbacktracking
finite segments into paths.

A group fixing two points of the line fixes the intervening path. A ray fixer
is finite and conjugate to a containing shifted ray fixer, so the two groups
are equal. Consequently every fixed locus is the whole track or a finite
integer interval. The acting group itself need not be finite.

We use left actions: if `x` fixes vertex zero and `y` fixes vertex one, the
forward translation is `y * x`. This is the reverse product of the source's
right-action notation. The original coset-action consumer is Goldschmidt's
`TrackSetup` in Chapter F.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.9)--(2.11),
printed pp.382--383. Only the two-step translation needed by the classification
is constructed; no unrelated general translation-period theorem is assumed.
-/

@[expose] public section
open SimpleGraph
namespace Theory.GroupAction.CubicTree
variable {V : Type*} {Γ : SimpleGraph V}

def sequenceWalk (f : ℤ → V) (ha : ∀ i, Γ.Adj (f i) (f (i+1)))
    (i : ℤ) : (n : ℕ) → BasedWalk Γ n (f i)
  | 0 => PUnit.unit
  | n+1 => ⟨⟨f (i+1), ha i⟩, sequenceWalk f ha (i+1) n⟩

theorem sequenceWalk_endpoint (f : ℤ → V) (ha : ∀ i, Γ.Adj (f i) (f (i+1)))
    (i : ℤ) (n : ℕ) : (sequenceWalk f ha i n).endpoint = f (i+n) := by
  induction n generalizing i with
  | zero => simp [BasedWalk.endpoint]
  | succ n ih =>
    change (sequenceWalk f ha (i+1) n).endpoint = _
    rw [ih]
    congr 1
    omega

theorem sequenceWalk_nonbacktracking (f : ℤ → V)
    (ha : ∀ i, Γ.Adj (f i) (f (i+1))) (hn : ∀ i, f (i+2) ≠ f i)
    (i : ℤ) (n : ℕ) : (sequenceWalk f ha i n).Nonbacktracking := by
  induction n using Nat.twoStepInduction generalizing i with
  | zero => trivial
  | one => trivial
  | more n h₀ h₁ =>
    refine ⟨?_, h₁ (i+1)⟩
    change f (i+1+1) ≠ f i
    convert hn i using 1
    congr 1
    omega

theorem sequence_injective (hΓ : Γ.IsAcyclic) (f : ℤ → V)
    (ha : ∀ i, Γ.Adj (f i) (f (i+1))) (hn : ∀ i, f (i+2) ≠ f i) :
    Function.Injective f := by
  suffices h : ∀ i j, i ≤ j → f i = f j → i = j by
    intro i j hij
    rcases le_total i j with hle | hle
    · exact h i j hle hij
    · exact (h j i hle hij.symm).symm
  intro i j hij he
  let n := (j-i).toNat
  have hi : i + (n : ℤ) = j := by dsimp [n]; omega
  let p := sequenceWalk f ha i n
  have hp : p.toWalk.IsPath :=
    PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound
      (N := n) (fun v c hc => (hΓ c hc).elim) p
      (sequenceWalk_nonbacktracking f ha hn i n) le_rfl
  have hend : p.endpoint = f i := by rw [sequenceWalk_endpoint, hi, he]
  have hnil := hp.nil_iff_eq.mpr hend.symm
  have hl := hnil.length_eq_zero
  rw [BasedWalk.length_toWalk] at hl
  omega

structure Line (Γ : SimpleGraph V) where
  vertex : ℤ → V
  injective : Function.Injective vertex
  adjacent : ∀ i, Γ.Adj (vertex i) (vertex (i+1))

variable {G : Type*} [Group G] [MulAction G V]
structure Track (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]
    extends Line Γ where
  translation : G
  translate : ∀ i, translation • vertex i = vertex (i+2)

open PathTransitivePolygon

def alternatingVertex (τ : G) (a b : V) (i : ℤ) : V :=
  τ ^ (i / 2) • (if i % 2 = 0 then a else b)

@[simp] theorem alternatingVertex_even (τ : G) (a b : V) (i : ℤ) :
    alternatingVertex τ a b (2*i) = τ^i • a := by
  simp [alternatingVertex]

@[simp] theorem alternatingVertex_odd (τ : G) (a b : V) (i : ℤ) :
    alternatingVertex τ a b (2*i+1) = τ^i • b := by
  have hd : (2*i+1)/2 = i := by omega
  have hm : (2*i+1)%2 = 1 := by omega
  simp [alternatingVertex, hd, hm]

theorem even_or_odd_index (i : ℤ) : ∃ k : ℤ, i=2*k ∨ i=2*k+1 := by
  refine ⟨i/2, ?_⟩
  omega

theorem alternatingVertex_translate (τ : G) (a b : V) (i : ℤ) :
    τ • alternatingVertex τ a b i = alternatingVertex τ a b (i+2) := by
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_index i
  · rw [show 2*k+2=2*(k+1) by omega]
    simp only [alternatingVertex_even, zpow_add, zpow_one, mul_smul]
    rw [← mul_smul, ← mul_smul, (Commute.refl τ).zpow_right k |>.eq]
  · rw [show 2*k+1+2=2*(k+1)+1 by omega]
    simp only [alternatingVertex_odd, zpow_add, zpow_one, mul_smul]
    rw [← mul_smul, ← mul_smul, (Commute.refl τ).zpow_right k |>.eq]


theorem alternatingVertex_adj (hact : GraphAction Γ G) {a b : V}
    (hab : Γ.Adj a b) {x y : G} (hx : x • a = a) (hy : y • b = b)
    (i : ℤ) : Γ.Adj (alternatingVertex (y*x) a b i)
      (alternatingVertex (y*x) a b (i+1)) := by
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_index i
  · simpa only [alternatingVertex_even, alternatingVertex_odd] using
      hact.map_adj ((y*x)^k) hab
  · rw [show 2*k+1+1=2*(k+1) by omega]
    simp only [alternatingVertex_odd, alternatingVertex_even, zpow_add,
      zpow_one, mul_smul, hx]
    exact hact.map_adj ((y*x)^k) (by simpa only [hy] using (hact.map_adj y hab).symm)

theorem alternatingVertex_no_return {a b : V} {x y : G}
    (hx : x • a = a) (hy : y • b = b)
    (hxb : x • b ≠ b) (hya : y • a ≠ a) (i : ℤ) :
    alternatingVertex (y*x) a b (i+2) ≠ alternatingVertex (y*x) a b i := by
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_index i
  · rw [show 2*k+2=2*(k+1) by omega]
    simp only [alternatingVertex_even, zpow_add, zpow_one, mul_smul, hx]
    exact fun he => hya ((MulAction.toPerm ((y*x)^k)).injective he)
  · rw [show 2*k+1+2=2*(k+1)+1 by omega]
    simp only [alternatingVertex_odd, zpow_add, zpow_one, mul_smul]
    intro he
    have he' := (MulAction.toPerm ((y*x)^k)).injective he
    exact hxb ((MulAction.toPerm y).injective (he'.trans hy.symm))

/-- Goldschmidt (2.10), in left-action convention: the translation is `y*x`. -/
def localMoversTrack (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {a b : V} (hab : Γ.Adj a b) {x y : G}
    (hx : x • a = a) (hy : y • b = b)
    (hxb : x • b ≠ b) (hya : y • a ≠ a) : Track Γ G where
  vertex := alternatingVertex (y*x) a b
  injective := sequence_injective hΓ _
    (alternatingVertex_adj hact hab hx hy)
    (alternatingVertex_no_return hx hy hxb hya)
  adjacent := alternatingVertex_adj hact hab hx hy
  translation := y*x
  translate := alternatingVertex_translate (y*x) a b

@[simp] theorem localMoversTrack_zero (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {a b : V} (hab : Γ.Adj a b) {x y : G}
    (hx : x • a = a) (hy : y • b = b)
    (hxb : x • b ≠ b) (hya : y • a ≠ a) :
    (localMoversTrack hΓ hact hab hx hy hxb hya).vertex 0 = a := by
  change alternatingVertex (y*x) a b (2*0)=a
  simp [alternatingVertex]

@[simp] theorem localMoversTrack_one (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {a b : V} (hab : Γ.Adj a b) {x y : G}
    (hx : x • a = a) (hy : y • b = b)
    (hxb : x • b ≠ b) (hya : y • a ≠ a) :
    (localMoversTrack hΓ hact hab hx hy hxb hya).vertex 1 = b := by
  change alternatingVertex (y*x) a b (2*0+1)=b
  simp [alternatingVertex]


theorem sequenceWalk_mem_vertices (f : ℤ → V) (ha : ∀ i, Γ.Adj (f i) (f (i+1)))
    (i : ℤ) (n k : ℕ) (hk : k ≤ n) :
    f (i+k) ∈ (sequenceWalk f ha i n).vertices := by
  induction n generalizing i k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp [BasedWalk.vertices]
  | succ n ih =>
    cases k with
    | zero => simp [BasedWalk.vertices]
    | succ k =>
      change f (i+(k+1:ℕ)) ∈ f i :: (sequenceWalk f ha (i+1) n).vertices
      apply List.mem_cons_of_mem
      have he : i+(k+1:ℕ) = (i+1)+k := by omega
      rw [he]
      exact ih (i+1) k (by omega)

def actionIso (hact : GraphAction Γ G) (g : G) : Γ ≃g Γ where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := hact.adj_iff g

namespace Line
variable (l : Line Γ)

def fixedIndices (U : Set G) : Set ℤ := {i | ∀ g∈U, g • l.vertex i = l.vertex i}

theorem fixed_between (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    {g : G} {i j k : ℤ} (hi : g • l.vertex i = l.vertex i)
    (hj : g • l.vertex j = l.vertex j) (hik : i ≤ k) (hkj : k ≤ j) :
    g • l.vertex k = l.vertex k := by
  let n := (j-i).toNat
  let m := (k-i).toNat
  have hn : i+(n:ℤ)=j := by dsimp [n]; omega
  have hm : i+(m:ℤ)=k := by dsimp [m]; omega
  have hmn : m ≤ n := by dsimp [m,n]; omega
  let p := sequenceWalk l.vertex l.adjacent i n
  have hnb : p.Nonbacktracking := sequenceWalk_nonbacktracking _ _
    (fun t h => by have := l.injective h; omega) i n
  have hend : p.endpoint = l.vertex j := (sequenceWalk_endpoint _ _ _ _).trans (congrArg _ hn)
  have hfixed := BasedWalk.fixes_short_walk
    (N := 2*n) (fun v c hc => (hΓ c hc).elim) p hnb le_rfl
    (actionIso hact g) hi (by change g • p.endpoint = p.endpoint; rw [hend]; exact hj)
  apply hfixed
  rw [← hm]
  exact sequenceWalk_mem_vertices _ _ i n m hmn

theorem fixedIndices_ordConnected (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (U : Set G) : (l.fixedIndices U).OrdConnected := by
  refine ⟨?_⟩
  intro i hi j hj k hk g hg
  exact l.fixed_between hΓ hact (hi g hg) (hj g hg) hk.1 hk.2
end Line


private theorem involutions_exchange_zpow (x y : G) (hx : x*x=1) (hy : y*y=1) (k : ℤ) :
    x*(y*x)^k = (y*x)^(-k)*x := by
  have hix : x⁻¹=x := inv_eq_of_mul_eq_one_left hx
  have hiy : y⁻¹=y := inv_eq_of_mul_eq_one_left hy
  have hc : (MulAut.conj x) (y*x) = (y*x)⁻¹ := by
    simp only [MulAut.conj_apply, mul_inv_rev, hix, hiy, mul_assoc, hx, mul_one]
  calc
    x*(y*x)^k = (MulAut.conj x) ((y*x)^k)*x := by
      simp only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one]
    _ = (y*x)^(-k)*x := by rw [map_zpow, hc, inv_zpow, zpow_neg]

theorem alternatingVertex_left_reflection {a b : V} {x y : G}
    (hx : x • a = a) (hy : y • b = b) (hx2 : x*x=1) (hy2 : y*y=1)
    (i : ℤ) : x • alternatingVertex (y*x) a b i = alternatingVertex (y*x) a b (-i) := by
  have hix : x⁻¹=x := inv_eq_of_mul_eq_one_left hx2
  have hiy : y⁻¹=y := inv_eq_of_mul_eq_one_left hy2
  obtain ⟨k, rfl | rfl⟩ := even_or_odd_index i
  · rw [show -(2*k)=2*(-k) by omega]
    simp only [alternatingVertex_even, ← mul_smul, involutions_exchange_zpow x y hx2 hy2]
    rw [mul_smul, hx]
  · rw [show -(2*k+1)=2*(-k-1)+1 by omega]
    simp only [alternatingVertex_odd, ← mul_smul, involutions_exchange_zpow x y hx2 hy2]
    rw [show -k-1 = -k+(-1) by omega, zpow_add, zpow_neg_one]
    simp only [mul_inv_rev, hix, hiy, mul_smul, hy]

theorem alternatingVertex_right_reflection {a b : V} {x y : G}
    (hx : x • a = a) (hy : y • b = b) (hx2 : x*x=1) (hy2 : y*y=1)
    (i : ℤ) : y • alternatingVertex (y*x) a b i = alternatingVertex (y*x) a b (2-i) := by
  have he : y=(y*x)*x := by rw [mul_assoc, hx2, mul_one]
  calc
    y • alternatingVertex (y*x) a b i =
        (y*x) • (x • alternatingVertex (y*x) a b i) := by
      rw [← mul_smul, ← he]
    _ = (y*x) • alternatingVertex (y*x) a b (-i) := by
      rw [alternatingVertex_left_reflection hx hy hx2 hy2]
    _ = alternatingVertex (y*x) a b (2-i) := by
      rw [alternatingVertex_translate]
      congr 1
      omega

namespace Track
variable (t : Track Γ G)

theorem inverse_translate (i : ℤ) : t.translation⁻¹ • t.vertex i = t.vertex (i-2) := by
  apply (inv_smul_eq_iff).mpr
  simpa only [sub_add_cancel] using (t.translate (i-2)).symm

def rayFixer (a : ℤ) : Subgroup G where
  carrier := {g | ∀ i, a ≤ i → g • t.vertex i = t.vertex i}
  one_mem' := by intro i hi; exact one_smul _ _
  mul_mem' := by intro g h hg hh i hi; rw [mul_smul, hh i hi, hg i hi]
  inv_mem' := by
    intro g hg i hi
    exact (inv_smul_eq_iff).mpr (hg i hi).symm

theorem rayFixer_mono {a b : ℤ} (hab : a ≤ b) : t.rayFixer a ≤ t.rayFixer b :=
  fun _ hg i hi => hg i (hab.trans hi)

theorem rayFixer_conjugate (a : ℤ) :
    (t.rayFixer a).map (MulAut.conj t.translation).toMonoidHom = t.rayFixer (a+2) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩ i hi
    change (t.translation * g * t.translation⁻¹) • t.vertex i = t.vertex i
    rw [mul_smul, mul_smul, t.inverse_translate,
      hg (i-2) (by omega), t.translate]
    congr 1
    omega
  · intro hg
    refine ⟨t.translation⁻¹*g*t.translation, ?_, ?_⟩
    · intro i hi
      rw [mul_smul, mul_smul, t.translate, hg (i+2) (by omega), t.inverse_translate]
      congr 1
      omega
    · change t.translation * (t.translation⁻¹*g*t.translation) * t.translation⁻¹ = g
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

theorem rayFixer_le_stabilizer (a : ℤ) :
    t.rayFixer a ≤ MulAction.stabilizer G (t.vertex a) :=
  fun _ hg => hg a le_rfl

theorem rayFixer_eq_shift (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    (a : ℤ) : t.rayFixer a = t.rayFixer (a+2) := by
  let := hfin (a+2)
  let : Finite (t.rayFixer (a+2)) := Finite.of_injective
    (Subgroup.inclusion (t.rayFixer_le_stabilizer (a+2)))
    (Subgroup.inclusion_injective _)
  apply Subgroup.eq_of_le_of_card_ge (t.rayFixer_mono (by omega))
  rw [← t.rayFixer_conjugate, Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem rayFixer_eq_succ (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    (a : ℤ) : t.rayFixer a = t.rayFixer (a+1) := by
  apply le_antisymm (t.rayFixer_mono (by omega))
  rw [t.rayFixer_eq_shift hfin a]
  exact t.rayFixer_mono (by omega)

theorem rayFixer_eq_add_nat (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    (a : ℤ) (n : ℕ) : t.rayFixer a = t.rayFixer (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      t.rayFixer a = t.rayFixer (a+n) := ih
      _ = t.rayFixer ((a+n)+1) := t.rayFixer_eq_succ hfin (a+n)
      _ = t.rayFixer (a+(n+1:ℕ)) := by congr 1; omega

theorem fixes_all_of_fixes_ray (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    {g : G} {a : ℤ} (hg : g∈t.rayFixer a) (i : ℤ) : g • t.vertex i = t.vertex i := by
  by_cases hi : a ≤ i
  · exact hg i hi
  · have hn : i+((a-i).toNat:ℤ)=a := by omega
    have he := t.rayFixer_eq_add_nat hfin i (a-i).toNat
    rw [hn] at he
    have hg' : g ∈ t.rayFixer i := he.symm ▸ hg
    exact hg' i le_rfl


def reverse : Track Γ G where
  vertex i := t.vertex (-i)
  injective := fun _ _ h => neg_injective (t.injective h)
  adjacent i := by
    have h := (t.adjacent (-i-1)).symm
    rw [sub_add_cancel] at h
    simpa only [neg_add_rev, neg_neg, add_comm, sub_eq_add_neg] using h
  translation := t.translation⁻¹
  translate i := by
    simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using t.inverse_translate (-i)

theorem fixedIndices_eq_univ_of_not_bddAbove
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    (U : Set G) (hU : ¬ BddAbove (t.toLine.fixedIndices U)) :
    t.toLine.fixedIndices U = Set.univ := by
  obtain ⟨a, ha⟩ := nonempty_of_not_bddAbove hU
  apply Set.eq_univ_of_forall
  intro i g hg
  apply t.fixes_all_of_fixes_ray hfin (a := a) (i := i)
  intro j haj
  obtain ⟨k, hk, hjk⟩ := not_bddAbove_iff.mp hU j
  exact t.toLine.fixed_between hΓ hact (ha g hg) (hk g hg) haj hjk.le

theorem fixedIndices_eq_univ_of_not_bddBelow
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i)))
    (U : Set G) (hU : ¬ BddBelow (t.toLine.fixedIndices U)) :
    t.toLine.fixedIndices U = Set.univ := by
  have hrev : ¬ BddAbove (t.reverse.toLine.fixedIndices U) := by
    apply not_bddAbove_iff.mpr
    intro i
    obtain ⟨j, hj, hji⟩ := not_bddBelow_iff.mp hU (-i)
    refine ⟨-j, ?_, by omega⟩
    simpa only [Line.fixedIndices, reverse, Set.mem_ofPred_eq, neg_neg] using hj
  have hall := t.reverse.fixedIndices_eq_univ_of_not_bddAbove hΓ hact
    (fun i => hfin (-i)) U hrev
  apply Set.eq_univ_of_forall
  intro i
  have hi : -i ∈ t.reverse.toLine.fixedIndices U := by rw [hall]; trivial
  simpa only [Line.fixedIndices, reverse, Set.mem_ofPred_eq, neg_neg] using hi

/-- Goldschmidt (2.11): a proper track fixed locus is finite. -/
theorem fixedIndices_finite_or_all
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i))) (U : Set G) :
    (t.toLine.fixedIndices U).Finite ∨ t.toLine.fixedIndices U = Set.univ := by
  by_cases ha : BddAbove (t.toLine.fixedIndices U)
  · by_cases hb : BddBelow (t.toLine.fixedIndices U)
    · exact Or.inl (hb.finite_of_bddAbove ha)
    · exact Or.inr (t.fixedIndices_eq_univ_of_not_bddBelow hΓ hact hfin U hb)
  · exact Or.inr (t.fixedIndices_eq_univ_of_not_bddAbove hΓ hact hfin U ha)

/-- The source's finite subarc includes the empty fixed locus. -/
theorem fixedIndices_eq_univ_or_interval
    (hΓ : Γ.IsAcyclic) (hact : GraphAction Γ G)
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i))) (U : Set G) :
    t.toLine.fixedIndices U = Set.univ ∨
      ∃ a b : ℤ, t.toLine.fixedIndices U = Set.Icc a b := by
  rcases t.fixedIndices_finite_or_all hΓ hact hfin U with hf | hall
  · right
    by_cases he : t.toLine.fixedIndices U = ∅
    · exact ⟨1, 0, he.trans (by simp)⟩
    · have hne := Set.nonempty_iff_ne_empty.mpr he
      exact ⟨sInf (t.toLine.fixedIndices U), sSup (t.toLine.fixedIndices U),
        (hne.ordConnected_iff_of_bdd hf.bddBelow hf.bddAbove).mp
          (t.toLine.fixedIndices_ordConnected hΓ hact U)⟩
  · exact Or.inl hall

end Track

end Theory.GroupAction.CubicTree
