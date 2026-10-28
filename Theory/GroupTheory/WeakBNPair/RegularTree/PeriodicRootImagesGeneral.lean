module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicRootImages

/-!
# Periodic root images for arbitrary path length

Match one exit of two path radicals representing the same quotient root.
Interior-star fixation and root rigidity then identify their global quotient
images. Periodic translates of the half-apartment supply a representative
fixing the original edge, so the root signs lie in the whole Borel image.
This extends the six-path calculation to the four-path source consumer.
Source: DGS, Groups and Graphs (1985), (3.7), p.80.
-/

@[expose] public noncomputable section
open SimpleGraph SimpleGraph.Walk Subgroup Theory.GroupAction.CubicTree
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y V : Type*} [Group X] [Group Y] [MulAction X V]
variable {Γ : SimpleGraph V} {r : Setoid V}

/-- Matching one exit identifies root images under the global class-action quotient. -/
theorem pathRoot_image_mem_of_same_classes_of_length
    (n : ℕ) (hn : 1 < n)
    (hr : Invariant (X := X) r) (htree : Γ.IsTree)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hsep : Separated r Γ (2*n)) (hlift : NeighborLifting Γ r)
    (hrigid : ∀ {a b : Quotient r} (p : (classGraph Γ r).Walk a b),
      p.IsPath → p.length = n → ∀ g : X,
      (∀ j, 0 < j → j < n → ∀ z, (classGraph Γ r).Adj (p.getVert j) z →
        quotientAction r hr g z = z) → ∀ z,
      (classGraph Γ r).Adj b z → z ≠ p.getVert (n-1) →
      quotientAction r hr g z = z → ∀ v, quotientAction r hr g v = v)
    {a b c d : V} (p : Γ.Walk a b) (q : Γ.Walk c d)
    (hp : p.IsPath) (hpl : p.length = n) (hql : q.length = n)
    (hclasses : ∀ j, j ≤ n → r (p.getVert j) (q.getVert j))
    (hpstars : ∀ u ∈ pathRoot (X := X) p, ∀ j, 0 < j → j < n →
      ∀ z, Γ.Adj (p.getVert j) z → u • z = z)
    (hqstars : ∀ u ∈ pathRoot (X := X) q, ∀ j, 0 < j → j < n →
      ∀ z, Γ.Adj (q.getVert j) z → u • z = z)
    (e : V) (he : Γ.Adj d e) (heprev : e ≠ q.penultimate)
    (hqtrans : ∀ z, Γ.Adj d z → z ≠ q.penultimate →
      ∃ v ∈ pathRoot (X := X) q, v • e = z)
    (u : X) (hu : u ∈ pathRoot (X := X) p) :
    QuotientGroup.mk' (quotientKernel r hr) u ∈
      (pathRoot (X := X) q).map (QuotientGroup.mk' (quotientKernel r hr)) := by
  let π := classGraphMap hsep (by omega : 1 < (2*n))
  let act := quotientAction r hr
  let P := p.map π
  have hb : Quotient.mk r b = Quotient.mk r d := by
    have hh := Quotient.sound (hclasses n le_rfl)
    have hp6 : p.getVert n = b := by rw [← hpl, getVert_length]
    have hq6 : q.getVert n = d := by rw [← hql, getVert_length]
    simpa only [hp6, hq6] using hh
  have hprev : Quotient.mk r (p.getVert (n-1)) = Quotient.mk r q.penultimate := by
    simpa only [penultimate, hql] using Quotient.sound (hclasses (n-1) (by omega))
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
    change Quotient.mk r (u • p.getVert (n-1)) = Quotient.mk r (p.getVert (n-1))
    exact congrArg (Quotient.mk r) ((pCoreIn_le 2 _ hu) (n-1) (by omega))
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
  have hvs : ∀ j, 0 < j → j < n → ∀ w,
      (classGraph Γ r).Adj (P.getVert j) w → act v w = w := by
    intro j hj hjl w hw
    have hc := Quotient.sound (hclasses j (by omega))
    have hw' : (classGraph Γ r).Adj (Quotient.mk r (q.getVert j)) w := by
      simp only [P, getVert_map] at hw
      change (classGraph Γ r).Adj (Quotient.mk r (p.getVert j)) w at hw
      rwa [hc] at hw
    exact quotientAction_fixes_neighbor hr hlift (hqstars v hv j hj hjl) hw'
  have hus : ∀ j, 0 < j → j < n → ∀ w,
      (classGraph Γ r).Adj (P.getVert j) w → act u w = w := by
    intro j hj hjl w hw
    simp only [P, getVert_map] at hw
    exact quotientAction_fixes_neighbor hr hlift (hpstars u hu j hj hjl) hw
  have hfix : ∀ w, act (v⁻¹ * u) w = w := by
    refine hrigid P (classGraph_map_short_path hsep (by omega) p hp (by omega))
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
      change Quotient.mk r e ≠ Quotient.mk r (p.getVert (n-1))
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


/-- Periodic root-image comparison supplies the original edge-stabilizer signs. -/
theorem periodic_root_image_sign_of_length (hΓ : Γ.IsAcyclic) (l : Line Γ)
    (n : ℕ) (hn : 1 < n) (Q : X →* Y) (B : Subgroup X)
    (hB : ∀ g : X, g • l.vertex 0 = l.vertex 0 → g • l.vertex 1 = l.vertex 1 → g ∈ B)
    (hroot : ∀ d : ℤ, d % (2*n:ℕ) = 0 →
      (pathRoot (X := X) (lineSegment l 0 n)).map Q ≤
        (pathRoot (X := X) (lineSegment l d n)).map Q)
    (t : X) (ht : ∀ j : ℤ, t • l.vertex j = l.vertex (-j))
    (x : X) (j k : ℤ) (hx₀ : x • l.vertex 0 = l.vertex j)
    (hx₁ : x • l.vertex 1 = l.vertex k) (hadj : Γ.Adj (l.vertex j) (l.vertex k)) :
    (∀ u ∈ pathRoot (X := X) (lineSegment l 0 n), Q (x⁻¹*u*x) ∈ B.map Q) ∨
    (∀ u ∈ pathRoot (X := X) (lineSegment l 0 n), Q ((t*x)⁻¹*u*(t*x)) ∈ B.map Q) := by
  have hmem (g : X) (j k : ℤ)
      (hg₀ : g • l.vertex 0 = l.vertex j) (hg₁ : g • l.vertex 1 = l.vertex k)
      (hjk : k = j+1 ∨ k = j-1)
      (a b : ℤ) (ha₀ : 0 ≤ a) (ha : a ≤ n) (hb₀ : 0 ≤ b) (hb : b ≤ n)
      (hja : j % (2*n:ℕ) = a % (2*n:ℕ)) (hkb : k % (2*n:ℕ) = b % (2*n:ℕ))
      (u : X) (hu : u ∈ pathRoot (X := X) (lineSegment l 0 n)) :
      Q (g⁻¹*u*g) ∈ B.map Q := by
    let d := j-a
    have hd : d % (2*n:ℕ) = 0 := by
      dsimp only [d]
      simp only [Int.sub_emod, hja, sub_self, Int.zero_emod]
    have hj : j = d+a := by dsimp [d]; omega
    have hk : k = d+b := by
      have he : (k-j-(b-a)) % (2*n:ℕ) = 0 := by
        rw [Int.sub_emod (k-j) (b-a), Int.sub_emod k j, Int.sub_emod b a,
          hkb, hja, sub_self, Int.zero_emod]
      have hm : (0:ℤ) < (2*n:ℕ) := by omega
      have hbound : -(2*n:ℕ) < k-j-(b-a) ∧ k-j-(b-a) < (2*n:ℕ) := by
        rcases hjk with hjk | hjk <;> omega
      have hz : k-j-(b-a) = 0 := by
        have hdvd := Int.dvd_of_emod_eq_zero he
        obtain ⟨t,ht⟩ := hdvd
        have ht0 : t=0 := by
          nlinarith
        simp only [ht0,mul_zero] at ht
        exact ht
      dsimp [d]
      omega
    obtain ⟨v, hv, he⟩ := hroot d hd (mem_map_of_mem Q hu)
    have hvfix (c : ℤ) (hc₀ : 0 ≤ c) (hc : c ≤ n) : v • l.vertex (d+c) = l.vertex (d+c) := by
      have hh := (pCoreIn_le 2 _ hv) c.toNat (by rw [lineSegment_length]; omega)
      rw [lineSegment_getVert l d n c.toNat (by omega), Int.toNat_of_nonneg hc₀] at hh
      exact hh
    refine ⟨g⁻¹*v*g, hB _ ?_ ?_, ?_⟩
    · simp only [mul_smul, hg₀, hj, hvfix a ha₀ ha]
      rw [← hj, ← hg₀, inv_smul_smul]
    · simp only [mul_smul, hg₁, hk, hvfix b hb₀ hb]
      rw [← hk, ← hg₁, inv_smul_smul]
    · simp only [map_mul, map_inv, he]
  have hjk := (line_adjacent_iff hΓ l j k).mp hadj
  rcases periodic_edge_half n (by omega) j k hjk with
      ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩ | ⟨a,b,ha₀,ha,hb₀,hb,hja,hkb⟩
  · exact Or.inl (hmem x j k hx₀ hx₁ hjk a b ha₀ ha hb₀ hb hja hkb)
  · apply Or.inr
    apply hmem (t*x) (-j) (-k)
      (by rw [mul_smul,hx₀,ht]) (by rw [mul_smul,hx₁,ht])
      (by rcases hjk with hh | hh; right; omega; left; omega)
      a b ha₀ ha hb₀ hb hja hkb

end Theory.GroupTheory.WeakBNPair.RegularTree
