module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ReflectionApartment
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanSaturation
public import Mathlib.Algebra.Ring.Periodic

/-!
# The periodic apartment and the quotient Cartan intersection

The actual apartment relation identifies the endpoints of every length-2n
line segment. Separation at shorter distances proves that two line vertices
are equivalent exactly when their integer coordinates agree modulo 2n.
The Cartan and two chosen reflections act by integer translations and
reflections. Such an action fixing the two quotient vertices of the marked
edge fixes the entire quotient line.

An element of the image Borel and image normalizer can therefore be lifted
to a Borel element fixing the quotient line. Separation propagates actual
fixation along a line path, whose stabilizer puts the lift in the Cartan.
This proves the full image-intersection equation; it is not inferred from
injectivity on the original endpoints.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)--(3.7), pp.77--80,
and the Cartan stabilizer calculation in (14.10), pp.216--217.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
variable {V X Y : Type*} [Group X] [Group Y] [MulAction X V] {Γ : SimpleGraph V}

/-- A separated equivalence with period m identifies precisely the
coordinates congruent modulo m on an embedded line. -/
theorem line_related_iff_mod (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (r : Setoid V) (m : ℕ) (hm : 0 < m) (hsep : Separated r Γ m)
    (hperiod : ∀ i : ℤ, r (l.vertex (i+m)) (l.vertex i)) (i j : ℤ) :
    r (l.vertex i) (l.vertex j) ↔ i % m = j % m := by
  let f : ℤ → Quotient r := fun i => Quotient.mk r (l.vertex i)
  have hf : Function.Periodic f (m:ℤ) := fun i => Quotient.sound (hperiod i)
  have hmod (i : ℤ) : f (i % m) = f i := by
    rw [Int.emod_def]
    simpa only [Int.cast_id, mul_comm] using hf.sub_int_mul_eq (x := i) (i / m)
  have hinj : Set.InjOn f (Set.Ico 0 (m:ℤ)) := by
    intro a ⟨ha0, ham⟩ b ⟨hb0, hbm⟩ he
    apply l.injective
    apply hsep (Quotient.exact he)
    rcases le_total a b with hab | hba
    · have hi : a + ((b-a).toNat : ℤ) = b := by omega
      have hd := line_dist_add_nat hΓ l a (b-a).toNat
      rw [hi] at hd
      rw [hd]
      omega
    · have hi : b + ((a-b).toNat : ℤ) = a := by omega
      have hd := line_dist_add_nat hΓ l b (a-b).toNat
      rw [hi] at hd
      rw [SimpleGraph.dist_comm, hd]
      omega
  constructor
  · intro hij
    apply hinj
      ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
    exact (hmod i).trans ((Quotient.sound hij).trans (hmod j).symm)
  · intro hij
    exact Quotient.exact ((hmod i).symm.trans ((congrArg f hij).trans (hmod j)))

private theorem sequenceWalk_mem_range (l : Line Γ) (i : ℤ) (n : ℕ) :
    ∀ z∈(sequenceWalk l.vertex l.adjacent i n).toWalk.support, z∈Set.range l.vertex := by
  induction n generalizing i with
  | zero =>
    intro z hz
    change z ∈ [l.vertex i] at hz
    exact ⟨i, (List.mem_singleton.mp hz).symm⟩
  | succ n ih =>
    intro z hz
    change z ∈ l.vertex i :: (sequenceWalk l.vertex l.adjacent (i+1) n).toWalk.support at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨i, rfl⟩
    · exact ih (i+1) z hz

/-- The literal apartment relation supplies the period, before proving
any BN-pair axiom or identifying a finite group. -/
theorem apartment_line_period (hΓ : Γ.IsAcyclic) (l : Line Γ) (n : ℕ) (i : ℤ) :
    apartmentSetoid (X := X) Γ (Set.range l.vertex) n
      (l.vertex (i + (2*n:ℕ))) (l.vertex i) := by
  let p := sequenceWalk l.vertex l.adjacent i (2*n)
  have hp : p.toWalk.IsPath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 2*n) (fun v c hc => (hΓ c hc).elim) p
    (sequenceWalk_nonbacktracking _ _ (fun j h => by have := l.injective h; omega) i (2*n))
    le_rfl
  have he := sequenceWalk_endpoint l.vertex l.adjacent i (2*n)
  rw [← he]
  apply (apartmentSetoid (X := X) Γ (Set.range l.vertex) n).symm
  apply Relation.EqvGen.rel
  refine ⟨p.toWalk, hp, BasedWalk.length_toWalk p, 1, ?_⟩
  intro z hz
  exact ⟨z, sequenceWalk_mem_range l i (2*n) z hz, one_smul X z⟩

/-- The two reflections and a pointwise fixer act on the integer line by
translations and reflections; their formulas are derived by generation. -/
theorem line_action_of_generators (f : ℤ → V) (K N : Subgroup X) (x y : X)
    (hK : ∀ k∈K, ∀ i, k • f i = f i)
    (hx : ∀ i, x • f i = f (-i)) (hy : ∀ i, y • f i = f (2-i))
    (hgen : N ≤ Subgroup.closure ((K : Set X) ∪ {x,y})) :
    ∀ g∈N, ∃ c : ℤ, (∀ i, g • f i = f (c+i)) ∨ (∀ i, g • f i = f (c-i)) := by
  intro g hg
  have hg' := hgen hg
  clear hg
  induction hg' using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨0, Or.inl (by simpa only [zero_add] using hK z hz)⟩
    · rcases hz with rfl | rfl
      · exact ⟨0, Or.inr (by simpa only [zero_sub] using hx)⟩
      · exact ⟨2, Or.inr hy⟩
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul a b _ _ ha hb =>
    obtain ⟨c, hc | hc⟩ := ha <;> obtain ⟨d, hd | hd⟩ := hb
    · exact ⟨c+d, Or.inl (by intro i; rw [mul_smul, hd, hc]; congr 1; omega)⟩
    · exact ⟨c+d, Or.inr (by intro i; rw [mul_smul, hd, hc]; congr 1; omega)⟩
    · exact ⟨c-d, Or.inr (by intro i; rw [mul_smul, hd, hc]; congr 1; omega)⟩
    · exact ⟨c-d, Or.inl (by intro i; rw [mul_smul, hd, hc]; congr 1; omega)⟩
  | inv a _ ha =>
    obtain ⟨c, hc | hc⟩ := ha
    · refine ⟨-c, Or.inl ?_⟩
      intro i
      apply (inv_smul_eq_iff).mpr
      rw [hc]
      congr 1
      omega
    · refine ⟨c, Or.inr ?_⟩
      intro i
      apply (inv_smul_eq_iff).mpr
      rw [hc]
      congr 1
      omega

/-- A translation or reflection of a separated periodic line fixing its
marked edge modulo the equivalence fixes every quotient line vertex. -/
theorem line_related_all_of_edge (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (r : Setoid V) (m : ℕ) (hm : 2 < m) (hsep : Separated r Γ m)
    (hperiod : ∀ i : ℤ, r (l.vertex (i+m)) (l.vertex i))
    (g : X) (hform : ∃ c : ℤ,
      (∀ i, g • l.vertex i = l.vertex (c+i)) ∨
      (∀ i, g • l.vertex i = l.vertex (c-i)))
    (hzero : r (g • l.vertex 0) (l.vertex 0))
    (hone : r (g • l.vertex 1) (l.vertex 1)) :
    ∀ i, r (g • l.vertex i) (l.vertex i) := by
  obtain ⟨c, hc | hc⟩ := hform
  · have hz : c % m = 0 := by
      rw [hc, add_zero] at hzero
      simpa only [Int.zero_emod] using
        (line_related_iff_mod hΓ l r m (by omega) hsep hperiod c 0).mp hzero
    intro i
    rw [hc, line_related_iff_mod hΓ l r m (by omega) hsep hperiod,
      Int.add_emod, hz, zero_add, Int.emod_emod]
  · rw [hc, sub_zero] at hzero
    rw [hc] at hone
    have hz := (line_related_iff_mod hΓ l r m (by omega) hsep hperiod c 0).mp hzero
    have ho := (line_related_iff_mod hΓ l r m (by omega) hsep hperiod (c-1) 1).mp hone
    rw [Int.zero_emod] at hz
    rw [Int.sub_emod, hz] at ho
    have hm' : (2:ℤ) < m := by omega
    have hmod1 : (1:ℤ) % m = 1 := Int.emod_eq_of_lt (by omega) (by omega)
    have hmodneg : (-1:ℤ) % m = m-1 := by
      have he : (-1:ℤ) % m = ((m:ℤ)-1) % m := by
        rw [Int.sub_emod, Int.emod_self, hmod1, zero_sub]
      rw [he, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hmod1, zero_sub, hmodneg] at ho
    omega

/-- The quotient Borel--normalizer intersection is the image of the actual
intersection. Its proof uses the periodic line and its original path fixer;
endpoint injectivity alone would not give this conclusion. -/
theorem image_intersection_of_line
    (q : X →* Y) (r : Setoid V)
    (hrelated : ∀ {g h : X}, q g = q h → ∀ a : V, r (g • a) (h • a))
    (hΓ : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (l : Line Γ) (m : ℕ) (hm : 2 < m) (hsep : Separated r Γ m)
    (hperiod : ∀ i : ℤ, r (l.vertex (i+m)) (l.vertex i))
    (B K N : Subgroup X)
    (hBa : B ≤ MulAction.stabilizer X (l.vertex 0))
    (hBb : B ≤ MulAction.stabilizer X (l.vertex 1))
    (hKB : K ≤ B) (hKN : K ≤ N)
    (hform : ∀ g∈N, ∃ c : ℤ,
      (∀ i, g • l.vertex i = l.vertex (c+i)) ∨
      (∀ i, g • l.vertex i = l.vertex (c-i)))
    {z : V} (p : Γ.Walk (l.vertex 0) z)
    (hp : ∀ v∈p.support, v∈Set.range l.vertex)
    (hfix : pathFixer (X := X) p ≤ K) :
    B.map q ⊓ N.map q = (B ⊓ N).map q := by
  apply le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
  rintro y ⟨⟨b, hb, rfl⟩, ⟨g, hg, he⟩⟩
  have hzero := hrelated he (l.vertex 0)
  have hone := hrelated he (l.vertex 1)
  rw [show b • l.vertex 0 = l.vertex 0 from hBa hb] at hzero
  rw [show b • l.vertex 1 = l.vertex 1 from hBb hb] at hone
  have hall := line_related_all_of_edge hΓ.isAcyclic l r m hm hsep hperiod
    g (hform g hg) hzero hone
  have hfixb : b∈pathFixer (X := X) p := by
    apply fixes_path_of_related hΓ.connected hact hsep hm p (hBa hb)
    intro k _
    obtain ⟨i, hi⟩ := hp _ (p.getVert_mem_support k)
    rw [← hi]
    exact r.trans (hrelated he.symm (l.vertex i)) (hall i)
  exact ⟨b, ⟨hKB (hfix hfixb), hKN (hfix hfixb)⟩, rfl⟩

end Theory.GroupTheory.WeakBNPair.RegularTree
