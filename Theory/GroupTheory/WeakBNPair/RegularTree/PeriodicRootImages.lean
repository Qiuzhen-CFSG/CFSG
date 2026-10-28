module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphAction
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicRootSigns
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRoot

/-!
# Matching root images along a periodic apartment

Two actual six-path radicals fixing the same raw root stars have the same
global quotient images once root automorphisms are determined by one exit.
Lift the first root's exit action at the second path endpoint and match it
using the second path radical. Rigidity kills their difference in the
literal global class-action kernel, without comparing local quotient maps.

The periodic line argument then places each signed root conjugate in the
image of the original edge stabilizer: choose a period-twelve translate
whose actual half-path contains the transported marked edge. This retains
the whole Borel. The source consumer supplies interior-star fixation,
exit transitivity and raw-hexagon rigidity.
Source: DGS, *Groups and Graphs* (1985), (3.7), p.80, with the actual roots
of (14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open SimpleGraph SimpleGraph.Walk Subgroup
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {r : Setoid V}

/-- Matching one exit identifies root images under the global class-action quotient. -/
theorem pathRoot_image_mem_of_same_classes
    (hr : Invariant (X := X) r) (htree : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hsep : Separated r Γ 12) (hlift : NeighborLifting Γ r)
    (hrigid : ∀ {a b : Quotient r} (p : (classGraph Γ r).Walk a b),
      p.IsPath → p.length = 6 → ∀ g : X,
      (∀ j, 0 < j → j < 6 → ∀ z, (classGraph Γ r).Adj (p.getVert j) z →
        quotientAction r hr g z = z) → ∀ z,
      (classGraph Γ r).Adj b z → z ≠ p.getVert 5 →
      quotientAction r hr g z = z → ∀ v, quotientAction r hr g v = v)
    {a b c d : V} (p : Γ.Walk a b) (q : Γ.Walk c d)
    (hp : p.IsPath) (hpl : p.length = 6) (hql : q.length = 6)
    (hclasses : ∀ j, j ≤ 6 → r (p.getVert j) (q.getVert j))
    (hpstars : ∀ u ∈ pathRoot (X := X) p, ∀ j, 0 < j → j < 6 →
      ∀ z, Γ.Adj (p.getVert j) z → u • z = z)
    (hqstars : ∀ u ∈ pathRoot (X := X) q, ∀ j, 0 < j → j < 6 →
      ∀ z, Γ.Adj (q.getVert j) z → u • z = z)
    (e : V) (he : Γ.Adj d e) (heprev : e ≠ q.penultimate)
    (hqtrans : ∀ z, Γ.Adj d z → z ≠ q.penultimate →
      ∃ v ∈ pathRoot (X := X) q, v • e = z)
    (u : X) (hu : u ∈ pathRoot (X := X) p) :
    QuotientGroup.mk' (quotientKernel r hr) u ∈
      (pathRoot (X := X) q).map (QuotientGroup.mk' (quotientKernel r hr)) := by
  let π := classGraphMap hsep (by decide : 1 < 12)
  let act := quotientAction r hr
  let P := p.map π
  have hb : Quotient.mk r b = Quotient.mk r d := by
    have hh := Quotient.sound (hclasses 6 le_rfl)
    have hp6 : p.getVert 6 = b := by rw [← hpl, getVert_length]
    have hq6 : q.getVert 6 = d := by rw [← hql, getVert_length]
    simpa only [hp6, hq6] using hh
  have hprev : Quotient.mk r (p.getVert 5) = Quotient.mk r q.penultimate := by
    simpa only [penultimate, hql] using Quotient.sound (hclasses 5 (by decide))
  have hqnil : ¬ q.Nil := by intro hh; have := hh.length_eq_zero; omega
  have heprevClass : Quotient.mk r e ≠ Quotient.mk r q.penultimate := by
    intro heq
    apply heprev
    apply hsep (Quotient.exact heq)
    have hd := htree.connected.dist_triangle (u := e) (v := d) (w := q.penultimate)
    rw [dist_eq_one_iff_adj.mpr he.symm,
      dist_eq_one_iff_adj.mpr (q.adj_penultimate hqnil).symm] at hd
    omega
  have huend : act u (Quotient.mk r d) = Quotient.mk r d := by
    rw [← hb]
    change Quotient.mk r (u • b) = Quotient.mk r b
    exact congrArg (Quotient.mk r) (pathRoot_fixes p hu).1
  have huprev : act u (Quotient.mk r q.penultimate) = Quotient.mk r q.penultimate := by
    rw [← hprev]
    change Quotient.mk r (u • p.getVert 5) = Quotient.mk r (p.getVert 5)
    exact congrArg (Quotient.mk r) ((pCoreIn_le 2 _ hu) 5 (by omega))
  have hadj : (classGraph Γ r).Adj (Quotient.mk r d) (act u (Quotient.mk r e)) := by
    have hh := quotientAction_adj hr hact u (π.map_adj he)
    change (classGraph Γ r).Adj (act u (Quotient.mk r d)) (act u (Quotient.mk r e)) at hh
    rwa [huend] at hh
  obtain ⟨z, hdz, hz⟩ := classGraph_neighbor_lift hlift hadj
  have hzprev : z ≠ q.penultimate := by
    intro hzq
    have hh : act u (Quotient.mk r e) = act u (Quotient.mk r q.penultimate) := by
      rw [huprev, ← hz, hzq]
    exact heprevClass ((act u).injective hh)
  obtain ⟨v, hv, hve⟩ := hqtrans z hdz hzprev
  have hvs : ∀ j, 0 < j → j < 6 → ∀ w,
      (classGraph Γ r).Adj (P.getVert j) w → act v w = w := by
    intro j hj hjl w hw
    have hc := Quotient.sound (hclasses j (by omega))
    have hw' : (classGraph Γ r).Adj (Quotient.mk r (q.getVert j)) w := by
      simp only [P, getVert_map] at hw
      change (classGraph Γ r).Adj (Quotient.mk r (p.getVert j)) w at hw
      rwa [hc] at hw
    exact quotientAction_fixes_neighbor hr hlift (hqstars v hv j hj hjl) hw'
  have hus : ∀ j, 0 < j → j < 6 → ∀ w,
      (classGraph Γ r).Adj (P.getVert j) w → act u w = w := by
    intro j hj hjl w hw
    simp only [P, getVert_map] at hw
    exact quotientAction_fixes_neighbor hr hlift (hpstars u hu j hj hjl) hw
  have hfix : ∀ w, act (v⁻¹ * u) w = w := by
    refine hrigid P (classGraph_map_short_path hsep (by decide) p hp (by omega))
      (by simpa only [P, length_map] using hpl) (v⁻¹ * u) ?_ (Quotient.mk r e) ?_ ?_ ?_
    · intro j hj hjl w hw
      rw [map_mul, map_inv]
      change (act v)⁻¹ (act u w) = w
      rw [hus j hj hjl w hw]
      exact (act v).symm_apply_eq.mpr (hvs j hj hjl w hw).symm
    · change (classGraph Γ r).Adj (Quotient.mk r b) (Quotient.mk r e)
      rw [hb]
      exact π.map_adj he
    · simp only [P, getVert_map]
      change Quotient.mk r e ≠ Quotient.mk r (p.getVert 5)
      rwa [hprev]
    · rw [map_mul, map_inv]
      change (act v)⁻¹ (act u (Quotient.mk r e)) = Quotient.mk r e
      have heval : act u (Quotient.mk r e) = act v (Quotient.mk r e) := by
        change _ = Quotient.mk r (v • e)
        rw [hve]
        exact hz.symm
      rw [heval]
      exact (act v).symm_apply_apply _
  refine ⟨v, hv, ?_⟩
  apply QuotientGroup.kerLift_injective (quotientAction r hr)
  change act v = act u
  apply Equiv.ext
  intro w
  have hh := hfix w
  rw [map_mul, map_inv] at hh
  change (act v)⁻¹ (act u w) = w at hh
  exact ((act v).symm_apply_eq.mp hh).symm

end Theory.GroupTheory.WeakBNPair.RegularTree

open SimpleGraph SimpleGraph.Walk Subgroup
open Theory.GroupAction.CubicTree
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y V : Type*} [Group X] [Group Y] [MulAction X V]
variable {Γ : SimpleGraph V}

private theorem sequenceWalk_getVert (l : Line Γ) (i : ℤ) (n j : ℕ) (hj : j ≤ n) :
    (sequenceWalk l.vertex l.adjacent i n).toWalk.getVert j = l.vertex (i+j) := by
  induction n generalizing i j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      change (sequenceWalk l.vertex l.adjacent (i+1) n).toWalk.getVert j = _
      rw [ih (i+1) j (by omega)]
      congr 1
      omega

/-- A finite oriented segment with its literal line endpoints. -/
def lineSegment (l : Line Γ) (i : ℤ) (n : ℕ) : Γ.Walk (l.vertex i) (l.vertex (i+n)) :=
  (sequenceWalk l.vertex l.adjacent i n).toWalk.copy rfl (sequenceWalk_endpoint _ _ _ _)

@[simp] theorem lineSegment_length (l : Line Γ) (i : ℤ) (n : ℕ) :
    (lineSegment l i n).length = n := by simp only [lineSegment, length_copy, BasedWalk.length_toWalk]

theorem lineSegment_getVert (l : Line Γ) (i : ℤ) (n j : ℕ) (hj : j ≤ n) :
    (lineSegment l i n).getVert j = l.vertex (i+j) := by
  simpa only [lineSegment, getVert_copy] using sequenceWalk_getVert l i n j hj

theorem lineSegment_isPath (hΓ : Γ.IsAcyclic) (l : Line Γ) (i : ℤ) (n : ℕ) :
    (lineSegment l i n).IsPath := by
  rw [lineSegment, isPath_copy]
  exact PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound
    (N := n) (fun v c hc => (hΓ c hc).elim) _
    (sequenceWalk_nonbacktracking _ _ (fun j hh => by have := l.injective hh; omega) i n) le_rfl

theorem lineSegment_support (l : Line Γ) (i : ℤ) (n : ℕ) :
    ∀ z ∈ (lineSegment l i n).support, z ∈ Set.range l.vertex := by
  intro z hz
  obtain ⟨j, hjz, hj⟩ := mem_support_iff_exists_getVert.mp hz
  exact ⟨i+j, (lineSegment_getVert l i n j (by simpa only [lineSegment_length] using hj)).symm.trans hjz⟩

/-- Periodic root-image comparison supplies the original edge-stabilizer signs. -/
theorem periodic_root_image_sign (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (Q : X →* Y) (B : Subgroup X)
    (hB : ∀ g : X, g • l.vertex 0 = l.vertex 0 → g • l.vertex 1 = l.vertex 1 → g ∈ B)
    (hroot : ∀ d : ℤ, d % 12 = 0 →
      (pathRoot (X := X) (lineSegment l 0 6)).map Q ≤
        (pathRoot (X := X) (lineSegment l d 6)).map Q)
    (t : X) (ht : ∀ j : ℤ, t • l.vertex j = l.vertex (-j))
    (x : X) (j k : ℤ) (hx₀ : x • l.vertex 0 = l.vertex j)
    (hx₁ : x • l.vertex 1 = l.vertex k) (hadj : Γ.Adj (l.vertex j) (l.vertex k)) :
    (∀ u ∈ pathRoot (X := X) (lineSegment l 0 6), Q (x⁻¹*u*x) ∈ B.map Q) ∨
    (∀ u ∈ pathRoot (X := X) (lineSegment l 0 6), Q ((t*x)⁻¹*u*(t*x)) ∈ B.map Q) := by
  have hmem (g : X) (j k : ℤ)
      (hg₀ : g • l.vertex 0 = l.vertex j) (hg₁ : g • l.vertex 1 = l.vertex k)
      (hjk : k = j+1 ∨ k = j-1)
      (a b : ℤ) (ha₀ : 0 ≤ a) (ha : a ≤ 6) (hb₀ : 0 ≤ b) (hb : b ≤ 6)
      (hja : j % 12 = a % 12) (hkb : k % 12 = b % 12)
      (u : X) (hu : u ∈ pathRoot (X := X) (lineSegment l 0 6)) :
      Q (g⁻¹*u*g) ∈ B.map Q := by
    let d := j-a
    have hd : d % 12 = 0 := by dsimp [d]; omega
    have hj : j = d+a := by dsimp [d]; omega
    have hk : k = d+b := by dsimp [d]; rcases hjk with hjk | hjk <;> omega
    obtain ⟨v, hv, he⟩ := hroot d hd (mem_map_of_mem Q hu)
    have hvfix (c : ℤ) (hc₀ : 0 ≤ c) (hc : c ≤ 6) : v • l.vertex (d+c) = l.vertex (d+c) := by
      have hh := (pCoreIn_le 2 _ hv) c.toNat (by rw [lineSegment_length]; omega)
      rw [lineSegment_getVert l d 6 c.toNat (by omega), Int.toNat_of_nonneg hc₀] at hh
      exact hh
    refine ⟨g⁻¹*v*g, hB _ ?_ ?_, ?_⟩
    · simp only [mul_smul, hg₀, hj, hvfix a ha₀ ha]
      rw [← hj, ← hg₀, inv_smul_smul]
    · simp only [mul_smul, hg₁, hk, hvfix b hb₀ hb]
      rw [← hk, ← hg₁, inv_smul_smul]
    · simp only [map_mul, map_inv, he]
  have hjk := (line_adjacent_iff hΓ l j k).mp hadj
  rcases periodic_edge_half 6 (by decide) j k hjk with
      ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩ | ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩
  · exact Or.inl (hmem x j k hx₀ hx₁ hjk a b ha₀ ha hb₀ hb hja hkb)
  · apply Or.inr
    apply hmem (t*x) (-j) (-k)
      (by rw [mul_smul,hx₀,ht]) (by rw [mul_smul,hx₁,ht])
      (by rcases hjk with hh | hh; right; omega; left; omega)
      a b ha₀ ha hb₀ hb hja hkb

end Theory.GroupTheory.WeakBNPair.RegularTree
