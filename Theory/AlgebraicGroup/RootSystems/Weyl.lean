module

public import Theory.AlgebraicGroup.RootSystems.Coxeter
public import Theory.AlgebraicGroup.RootSystems.RankTwoOrder

set_option linter.style.haveILetI false

universe u

namespace Theory.AlgebraicGroup

open SimpleGraph
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

/-- A positive-definite Cartan matrix with an exact simple three-arm support
cannot contain arm prefixes of sizes one, two, and five. -/
public lemma not_cartan_three_arm_affineE8_prefix_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n0 n1 n2 : ℕ}
    (e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ κ)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inl l)))) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hcenterBond0 :
      A (e none) (e (some (Sum.inl 0))) = -1 ∧
      A (e (some (Sum.inl 0))) (e none) = -1)
    (hcenterBond1 :
      A (e none) (e (some (Sum.inr (Sum.inl 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl 0)))) (e none) = -1)
    (hcenterBond2 :
      A (e none) (e (some (Sum.inr (Sum.inr 0)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr 0)))) (e none) = -1)
    (hsimple0 : ∀ r : Fin (n0 + 1), 0 < r.val →
      A (e (some (Sum.inl ⟨r.val - 1, by omega⟩)))
          (e (some (Sum.inl r))) = -1 ∧
      A (e (some (Sum.inl r)))
          (e (some (Sum.inl ⟨r.val - 1, by omega⟩))) = -1)
    (hsimple1 : ∀ r : Fin (n1 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inl r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inl r))))
          (e (some (Sum.inr (Sum.inl ⟨r.val - 1, by omega⟩)))) = -1)
    (hsimple2 : ∀ r : Fin (n2 + 1), 0 < r.val →
      A (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩))))
          (e (some (Sum.inr (Sum.inr r)))) = -1 ∧
      A (e (some (Sum.inr (Sum.inr r))))
          (e (some (Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩)))) = -1)
    (hn1 : 1 ≤ n1) (hn2 : 4 ≤ n2) : False := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  let f0 : Fin (n0 + 1) → κ := fun j => e (some (Sum.inl j))
  let f1 : Fin (n1 + 1) → κ := fun j => e (some (Sum.inr (Sum.inl j)))
  let f2 : Fin (n2 + 1) → κ := fun j => e (some (Sum.inr (Sum.inr j)))
  have hf0 : Function.Injective f0 := by
    intro j l hjl
    simpa [f0] using e.injective hjl
  have hf1 : Function.Injective f1 := by
    intro j l hjl
    simpa [f1] using e.injective hjl
  have hf2 : Function.Injective f2 := by
    intro j l hjl
    simpa [f2] using e.injective hjl
  have hc0 : ∀ j, e none ≠ f0 j := by
    intro j hj
    simpa [f0] using e.injective hj
  have hc1 : ∀ j, e none ≠ f1 j := by
    intro j hj
    simpa [f1] using e.injective hj
  have hc2 : ∀ j, e none ≠ f2 j := by
    intro j hj
    simpa [f2] using e.injective hj
  have h01 : ∀ j l, f0 j ≠ f1 l := by
    intro j l hjl
    simpa [f0, f1] using e.injective hjl
  have h02 : ∀ j l, f0 j ≠ f2 l := by
    intro j l hjl
    simpa [f0, f2] using e.injective hjl
  have h12 : ∀ j l, f1 j ≠ f2 l := by
    intro j l hjl
    simpa [f1, f2] using e.injective hjl
  obtain ⟨ep, hpref⟩ :=
    simpleGraph_three_arm_affineE8_prefix_embedding
      G (e none) f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12
      (by simpa [G, f0] using hcenter0)
      (by simpa [G, f1] using hcenter1)
      (by simpa [G, f2] using hcenter2)
      (by simpa [G, f0] using hpath0)
      (by simpa [G, f1] using hpath1)
      (by simpa [G, f2] using hpath2)
      (by simpa [G, f0, f1] using hcross01)
      (by simpa [G, f0, f2] using hcross02)
      (by simpa [G, f1, f2] using hcross12)
      hn1 hn2
  have hedge : ∀ x y, G.Adj x y → A x y = -1 := by
    simpa [G] using
      cartan_three_arm_support_adj_entry_eq_neg_one A e
        hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
        hcross01 hcross02 hcross12 hcenterBond0 hcenterBond1 hcenterBond2
        hsimple0 hsimple1 hsimple2
  apply not_cartan_affineE8_of_support_numbering A d hdiag hpos ep hpref
  intro i j hij
  exact hedge (ep i) (ep j) ((hpref i j).mpr hij)

/-- At a three-legged Cartan support star, positive definiteness forces every
incident bond product to be one.  The leaf-pair zero hypotheses describe the
actual support-star configuration and carry no classification conclusion. -/
public lemma cartan_threeStar_incident_products_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a b e : κ) (he : Function.Injective ![c, a, b, e])
    (hca : A c a ≠ 0) (hcb : A c b ≠ 0) (hce : A c e ≠ 0)
    (hleaf : ∀ i j : Fin 3, i ≠ j →
      A (![a, b, e] i) (![a, b, e] j) = 0 ∧
      A (![a, b, e] j) (![a, b, e] i) = 0) :
    A c a * A a c = 1 ∧ A c b * A b c = 1 ∧ A c e * A e c = 1 := by
  have hca_ne : c ≠ a := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (1 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 1) hv
  have hcb_ne : c ≠ b := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (2 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 2) hv
  have hce_ne : c ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 3) hv
  have hab_ne : a ≠ b := by
    intro h
    have hv := he (show (![c, a, b, e] (1 : Fin 4)) = (![c, a, b, e] (2 : Fin 4)) by simp [h])
    exact (by decide : (1 : Fin 4) ≠ 2) hv
  have hae_ne : a ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (1 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (1 : Fin 4) ≠ 3) hv
  have hbe_ne : b ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (2 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (2 : Fin 4) ≠ 3) hv
  have hpa := cartan_rankTwo_nonzero_bounds A hrank hca_ne hca
  have hpb := cartan_rankTwo_nonzero_bounds A hrank hcb_ne hcb
  have hpe := cartan_rankTwo_nonzero_bounds A hrank hce_ne hce
  have hsum_ab := cartan_twoNeighbor_edgeProducts_sum_le_three A d hdiag hrank hpos c a b hca_ne hcb_ne hab_ne hca hcb
  have hsum_ae := cartan_twoNeighbor_edgeProducts_sum_le_three A d hdiag hrank hpos c a e hca_ne hce_ne hae_ne hca hce
  have hsum_be := cartan_twoNeighbor_edgeProducts_sum_le_three A d hdiag hrank hpos c b e hcb_ne hce_ne hbe_ne hcb hce
  have hpa_le_two : A c a * A a c ≤ 2 := by omega
  have hpb_le_two : A c b * A b c ≤ 2 := by omega
  have hpe_le_two : A c e * A e c ≤ 2 := by omega
  have hstar : A c a * A a c + A c b * A b c + A c e * A e c ≤ 3 := by
    by_contra hbad
    have hsub := hpos.submatrix he
    let x : Fin 4 → ℤ := ![2, -A a c, -A b c, -A e c]
    have hx : x ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp [x] at h0
    have hquad := hsub.dotProduct_mulVec_pos hx
    have hab0 : A a b = 0 := by simpa using (hleaf 0 1 (by decide)).1
    have hae0 : A a e = 0 := by simpa using (hleaf 0 2 (by decide)).1
    have hba0 : A b a = 0 := by simpa using (hleaf 1 0 (by decide)).1
    have hbe0 : A b e = 0 := by simpa using (hleaf 1 2 (by decide)).1
    have hea0 : A e a = 0 := by simpa using (hleaf 2 0 (by decide)).1
    have heb0 : A e b = 0 := by simpa using (hleaf 2 1 (by decide)).1
    simp [x, Matrix.submatrix, Matrix.diagonal_mul, dotProduct, Matrix.mulVec,
      hdiag, hab0, hae0, hba0, hbe0, hea0, heb0, Fin.sum_univ_succ] at hquad
    ring_nf at hquad
    have hdc : 0 < d c := by
      have hc := hpos.diag_pos (i := c)
      simp [Matrix.diagonal_mul, hdiag] at hc
      omega
    have hsum : 4 ≤ A c a * A a c + A c b * A b c + A c e * A e c := by omega
    nlinarith
  constructor
  · have hp := hpa.2.2
    omega
  constructor
  · have hp := hpb.2.2
    omega
  · have hp := hpe.2.2
    omega

/-- Endpoints of a triple Cartan bond are leaves in the support graph. -/
public lemma cartan_tripleBond_endpoints_degree_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (a b : κ) (hab : a ≠ b)
    (hprod : A a b * A b a = 3) :
    (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree a = 1 ∧
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree b = 1 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have endpoint_degree (c l : κ) (hcl : c ≠ l)
      (hp : A c l * A l c = 3) : G.degree c = 1 := by
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    have hnz : A c l ≠ 0 := by
      intro h
      rw [h, zero_mul] at hp
      omega
    refine ⟨l, ?_, ?_⟩
    · change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c l
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hcl, Or.inl hnz⟩
    · intro w hadj
      by_contra hwl
      have hcw : c ≠ w := hadj.ne
      have hadj' : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c w := hadj
      rw [SimpleGraph.fromRel_adj] at hadj'
      have hnzw : A c w ≠ 0 := by
        rcases hadj'.2 with hforward | hreverse
        · exact hforward
        · have hb := cartan_rankTwo_nonzero_bounds A hrank hcw.symm hreverse
          omega
      have hwb := cartan_rankTwo_nonzero_bounds A hrank hcw hnzw
      have hpw : 1 ≤ A c w * A w c := hwb.2.2
      have hsum := cartan_twoNeighbor_edgeProducts_sum_le_three
        A d hdiag hrank hpos c l w hcl hcw (fun h => hwl h.symm) hnz hnzw
      omega
  constructor
  · exact endpoint_degree a b hab hprod
  · apply endpoint_degree b a hab.symm
    simpa [mul_comm] using hprod

/-- The undirected support graph of a finite positive-definite Cartan-style
matrix has degree at most three at every vertex. -/
public lemma cartanSupport_degree_le_three
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef) (c : κ) :
    (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c ≤ 3 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  change G.degree c ≤ 3
  by_contra hdeg
  have hfour : 4 ≤ G.degree c := by omega
  have hcard : Fintype.card (Fin 4) ≤ (G.neighborFinset c).card := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hfour
  obtain ⟨l, hl⟩ := Function.Embedding.exists_of_card_le_finset hcard
  apply not_cartan_fourNeighbors_of_diagonal_mul_posDef A d hdiag hrank hpos c l
  · intro a
    have hmem := hl ⟨a, rfl⟩
    have hadj : G.Adj c (l a) := by simpa using hmem
    exact hadj.ne
  · intro a
    have hmem := hl ⟨a, rfl⟩
    have hadj : G.Adj c (l a) := by simpa using hmem
    change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c (l a) at hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hforward | hreverse
    · exact hforward
    · have hb := cartan_rankTwo_nonzero_bounds A hrank hadj.1.symm hreverse
      omega

/-- A unique internal double edge on a simple path can occur in a positive
finite Cartan matrix only as the middle edge of a four-vertex path.  The
hypotheses give the matrix entries directly and contain no classification
conclusion. -/
public lemma cartan_path_internal_heavy_eq_middle_four_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n r : ℕ} (e : Fin n ≃ κ) (u v : ℤ)
    (hentries : ∀ i j : Fin n, A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = r then u else -1
      else if j.val + 1 = i.val then
        if j.val = r then v else -1
      else 0)
    (huv : u * v = 2) (hleft : 0 < r) (hright : r + 2 < n) :
    n = 4 ∧ r = 1 := by
  by_contra hconcl
  have hn5 : 5 ≤ n := by omega
  by_cases hlongLeft : 2 ≤ r
  · let f : Fin 5 ↪ Fin n :=
      ⟨fun i => ⟨r - 2 + i.val, by omega⟩, by
        intro i j hij
        apply Fin.ext
        have hval := congrArg Fin.val hij
        dsimp at hval ⊢
        omega⟩
    have h0 : r - 2 ≠ r := by omega
    have h1 : r - 2 + 1 ≠ r := by omega
    have h2 : r - 2 + 2 = r := by omega
    have h3 : r - 2 + 3 ≠ r := by omega
    have hfval : ∀ i : Fin 5, (f i).val = r - 2 + i.val := by
      intro i
      rfl
    have hA5 : ∀ i j, A (e (f i)) (e (f j)) =
        if i = j then 2 else if
          (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
          (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then -1 else if
          (i = 2 ∧ j = 3) then u else if
          (i = 3 ∧ j = 2) then v else 0 := by
      intro i j
      rw [hentries]
      fin_cases i <;> fin_cases j <;>
        simp [hfval, h0, h1, h2, h3] <;> omega
    exact not_cartan_five_path_internal_heavy_of_diagonal_mul_posDef
      A d hpos (f.trans e.toEmbedding) u v hA5 huv
  · have hr : r = 1 := by omega
    let f : Fin 5 ↪ Fin n :=
      ⟨fun i => ⟨r + 3 - i.val, by omega⟩, by
        intro i j hij
        apply Fin.ext
        have hval := congrArg Fin.val hij
        dsimp at hval ⊢
        omega⟩
    have hA5 : ∀ i j, A (e (f i)) (e (f j)) =
        if i = j then 2 else if
          (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
          (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then -1 else if
          (i = 2 ∧ j = 3) then v else if
          (i = 3 ∧ j = 2) then u else 0 := by
      intro i j
      rw [hentries]
      fin_cases i <;> fin_cases j <;>
        simp [f, hr]
    have hvu : v * u = 2 := by simpa [mul_comm] using huv
    exact not_cartan_five_path_internal_heavy_of_diagonal_mul_posDef
      A d hpos (f.trans e.toEmbedding) v u hA5 hvu

set_option maxHeartbeats 800000 in
/-- The explicit affine-`D` row-entry interface feeds the null-vector
construction into the two-degree-three-vertices positive-definiteness core.
All decomposition data remain ordinary theorem parameters. -/
public lemma not_cartan_two_degree_three_vertices_of_affineD_row_entries
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {m : ℕ} (hm : 0 < m) (e : Fin (m + 5) ↪ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hleft₁ : A (e 0) (e 1) = -1)
    (hright₁ : A (e ⟨m, by omega⟩) (e ⟨m - 1, by omega⟩) = -1)
    (ha₁ : A (e 0) (e ⟨m + 1, by omega⟩) = -1)
    (ha₂ : A (e 0) (e ⟨m + 2, by omega⟩) = -1)
    (hā₁ : A (e ⟨m + 1, by omega⟩) (e 0) = -1)
    (hā₂ : A (e ⟨m + 2, by omega⟩) (e 0) = -1)
    (hb₁ : A (e ⟨m, by omega⟩) (e ⟨m + 3, by omega⟩) = -1)
    (hb₂ : A (e ⟨m, by omega⟩) (e ⟨m + 4, by omega⟩) = -1)
    (hback₁ : A (e ⟨m + 3, by omega⟩) (e ⟨m, by omega⟩) = -1)
    (hback₂ : A (e ⟨m + 4, by omega⟩) (e ⟨m, by omega⟩) = -1)
    (hpath₁ : ∀ (i : Fin (m + 5)) (hi : i.val < m),
      A (e i) (e ⟨i.val + 1, by omega⟩) = -1)
    (hpath₂ : ∀ (i : Fin (m + 5)) (hi : i.val < m),
      A (e ⟨i.val + 1, by omega⟩) (e i) = -1)
    (hzero₀ : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ ⟨m + 1, by omega⟩ →
      j ≠ ⟨m + 2, by omega⟩ → A (e 0) (e j) = 0)
    (hzeroₘ : ∀ j, j ≠ ⟨m, by omega⟩ → j ≠ ⟨m - 1, by omega⟩ →
      j ≠ ⟨m + 3, by omega⟩ → j ≠ ⟨m + 4, by omega⟩ →
      A (e ⟨m, by omega⟩) (e j) = 0)
    (hzeroPath : ∀ i j, 0 < i.val → i.val < m → i ≠ j →
      j.val + 1 ≠ i.val → i.val + 1 ≠ j.val → A (e i) (e j) = 0)
    (hzeroA₁ : ∀ j, j ≠ ⟨m + 1, by omega⟩ → j ≠ 0 →
      A (e ⟨m + 1, by omega⟩) (e j) = 0)
    (hzeroA₂ : ∀ j, j ≠ ⟨m + 2, by omega⟩ → j ≠ 0 →
      A (e ⟨m + 2, by omega⟩) (e j) = 0)
    (hzeroB₁ : ∀ j, j ≠ ⟨m + 3, by omega⟩ → j ≠ ⟨m, by omega⟩ →
      A (e ⟨m + 3, by omega⟩) (e j) = 0)
    (hzeroB₂ : ∀ j, j ≠ ⟨m + 4, by omega⟩ → j ≠ ⟨m, by omega⟩ →
      A (e ⟨m + 4, by omega⟩) (e j) = 0) : False := by
  obtain ⟨x, hx, hker⟩ := affineD_mulVec_eq_zero_of_row_entries hm A e
    hdiag hleft₁ hright₁ ha₁ ha₂ hā₁ hā₂ hb₁ hb₂ hback₁ hback₂
    hpath₁ hpath₂ hzero₀ hzeroₘ hzeroPath hzeroA₁ hzeroA₂ hzeroB₁ hzeroB₂
  exact not_cartan_two_degree_three_vertices_of_diagonal_mul_posDef
    A d hpos e x hx hker

open SimpleGraph

/-- If a finite tree has degree at most three and only `c` can have degree
three, then every connected component left after deleting `c` is a nonempty
finite path.  The result returns an ordinary path numbering and stores no
classification conclusion in auxiliary data. -/
public lemma simpleGraph_tree_deleted_component_pathGraph_numbering
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (c : V)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (huniq : ∀ v, G.degree v = 3 → v = c)
    (C : (G.induce {c}ᶜ).ConnectedComponent) :
    ∃ n : ℕ, ∃ e : Fin (n + 1) ≃ C.supp,
      ∀ i j, C.toSimpleGraph.Adj (e i) (e j) ↔
        (pathGraph (n + 1)).Adj i j := by
  classical
  have hHacyc : (G.induce {c}ᶜ).IsAcyclic := by
    exact hG.isAcyclic.induce ({c}ᶜ : Set V)
  have htreeC : C.toSimpleGraph.IsTree := by
    exact hHacyc.isTree_connectedComponent C
  have hdegC : ∀ x, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    have hCH : C.toSimpleGraph.degree x ≤ (G.induce {c}ᶜ).degree x.val := by
      exact simpleGraph_degree_le_of_injective_hom C.toSimpleGraph
        (G.induce {c}ᶜ) C.toSimpleGraph_hom Subtype.val_injective x
    have hHG : (G.induce {c}ᶜ).degree x.val ≤ G.degree x.val.val :=
      simpleGraph_induce_degree_le G ({c}ᶜ : Set V) x.val
    have hle3 : G.degree x.val.val ≤ 3 := hdegree _
    have hne3 : G.degree x.val.val ≠ 3 := by
      intro heq
      have hxc : x.val.val = c := huniq _ heq
      exact x.val.property (by simpa using hxc)
    omega
  obtain ⟨m, e, he⟩ :=
    simpleGraph_pathGraph_numbering_of_isTree_degree_le_two
      C.toSimpleGraph htreeC hdegC
  obtain ⟨x, hx⟩ := C.nonempty_supp
  let i : Fin m := e.symm ⟨x, hx⟩
  have hm : m ≠ 0 := by
    intro hm
    subst m
    exact Fin.elim0 i
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero hm
  exact ⟨n, e, he⟩

/-- Every positive subsystem is the positive subsystem of a base.

This is GLS3, Theorem 1.8.2. -/
public theorem base_toPositiveSubsystem_surjective
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    Function.Surjective (RootPairing.Base.toPositiveSubsystem (P := P)) := by
  intro S
  let b : P.Base := Classical.choice P.nonempty_base
  obtain ⟨g, hg⟩ := exists_weylGroup_translate_base_toPositiveSubsystem P b S
  exact ⟨g • b, hg⟩

/-- The Weyl group acts transitively on bases.

This is GLS3, Theorem 1.8.2. -/
public theorem weylGroup_action_on_bases_transitive
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    MulAction.IsPretransitive P.weylGroup P.Base := by
  constructor
  intro b c
  obtain ⟨g, hg⟩ :=
    exists_weylGroup_translate_base_toPositiveSubsystem P b c.toPositiveSubsystem
  exact ⟨g, base_toPositiveSubsystem_injective (P := P) hg⟩

open scoped SimpleGraph

/-- The support graph of a finite positive-definite Cartan-style matrix is
acyclic. -/
public lemma cartanSupport_isAcyclic
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef) :
    (SimpleGraph.fromRel fun i j => A i j ≠ 0).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro m hm hcycle
  exact not_cartan_supportCycle_of_diagonal_mul_posDef
    (m - 3) A d hdiag hrank hpos (by
    rw [Nat.sub_add_cancel hm]
    exact hcycle)

public theorem _root_.RootPairing.Base.exists_word_decomposition
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) :
    ∃ n : ℕ, ∃ l : List b.support, l.length = n ∧ b.wordProd l = g := by
  rcases b.exists_wordProd_eq g with ⟨l, hl⟩
  exact ⟨l.length, l, rfl, hl⟩

@[expose]
public noncomputable def _root_.RootPairing.Base.wordLength
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) : ℕ := by
  classical
  exact Nat.find (RootPairing.Base.exists_word_decomposition b g)

public lemma _root_.RootPairing.Base.wordLength_spec
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) :
    ∃ l : List b.support, l.length = b.wordLength g ∧ b.wordProd l = g := by
  classical
  unfold RootPairing.Base.wordLength
  exact Nat.find_spec (RootPairing.Base.exists_word_decomposition b g)

public lemma _root_.RootPairing.Base.wordLength_le
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (l : List b.support) (hl : b.wordProd l = g) :
    b.wordLength g ≤ l.length := by
  classical
  unfold RootPairing.Base.wordLength
  apply Nat.find_min' (RootPairing.Base.exists_word_decomposition b g)
  exact ⟨l, rfl, hl⟩

@[simp]
public lemma _root_.RootPairing.Base.wordLength_one
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) : b.wordLength 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact b.wordLength_le 1 [] (by simp)

public lemma _root_.RootPairing.Base.wordLength_mul_simpleReflection_le
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support) :
    b.wordLength (g * b.simpleReflection j) ≤ b.wordLength g + 1 := by
  rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
  have h := b.wordLength_le (g * b.simpleReflection j) (l ++ [j]) (by
    rw [b.wordProd_append, hprod]
    rfl)
  simpa [hlen] using h

public lemma _root_.RootPairing.Base.wordLength_mul_simpleReflection_of_not_isPos
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm g j)) :
    b.wordLength (g * b.simpleReflection j) + 1 = b.wordLength g := by
  rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
  have hneg' : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) j) := by
    rwa [hprod]
  rcases b.exchange_word l j hneg' with ⟨l', hl'prod, hl'len⟩
  have hupper : b.wordLength (g * b.simpleReflection j) ≤ l'.length := by
    apply b.wordLength_le _ l'
    rw [hl'prod, hprod]
  have hlower := b.wordLength_mul_simpleReflection_le
    (g * b.simpleReflection j) j
  have hsq : (g * b.simpleReflection j) * b.simpleReflection j = g := by
    rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
  rw [hsq] at hlower
  omega

public lemma _root_.RootPairing.Base.wordLength_mul_simpleReflection_of_isPos
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support)
    (hpos : b.IsPos (P.weylGroupToPerm g j)) :
    b.wordLength (g * b.simpleReflection j) = b.wordLength g + 1 := by
  letI := P.indexNeg
  have hneg : ¬ b.IsPos
      (P.weylGroupToPerm (g * b.simpleReflection j) j) := by
    change ¬ b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j j))
    change ¬ b.IsPos (P.weylGroupToPerm g (-j))
    rw [P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not b]
    exact not_not_intro hpos
  have h := b.wordLength_mul_simpleReflection_of_not_isPos
    (g * b.simpleReflection j) j hneg
  have hsq : (g * b.simpleReflection j) * b.simpleReflection j = g := by
    rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
  rw [hsq] at h
  exact h.symm

public lemma _root_.RootPairing.Base.wordProd_reverse
    {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} (b : P.Base) (l : List b.support) :
    b.wordProd l.reverse = (b.wordProd l)⁻¹ := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.reverse_cons, b.wordProd_append, b.wordProd_cons, ih]
      simp

/-- The Weyl group acts freely on the set of bases.

This is GLS3, Theorem 1.8.2. -/
public theorem weylGroup_action_on_bases_free
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    IsCancelSMul P.weylGroup P.Base := by
  classical
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g b hgb
  have hex : ∃ n : ℕ, ∃ l : List b.support,
      l.length = n ∧ b.wordProd l = g := by
    rcases b.exists_wordProd_eq g with ⟨l, hl⟩
    exact ⟨l.length, l, rfl, hl⟩
  let n := Nat.find hex
  obtain ⟨l, hlen, hprod⟩ := Nat.find_spec hex
  by_cases hl : l = []
  · subst l
    simpa using hprod.symm
  · let j : b.support := l.getLast hl
    let p : List b.support := l.dropLast
    have hl_decomp : p ++ [j] = l := List.dropLast_append_getLast hl
    have hg_word : b.wordProd p * b.simpleReflection j = g := by
      change b.wordProd p * b.wordProd [j] = g
      rw [← b.wordProd_append, hl_decomp, hprod]
    have hjpos : b.IsPos (j : ι) := b.isPos_of_mem_support j.property
    have hgjpos : b.IsPos (P.weylGroupToPerm g j) := by
      have h := _root_.RootPairing.Base.isPos_mapAut_of
        (g : RootPairing.Aut P) b hjpos
      change (g • b).IsPos (P.weylGroupToPerm g j) at h
      rwa [hgb] at h
    have hpneg : ¬ b.IsPos (P.weylGroupToPerm (b.wordProd p) j) := by
      letI := P.indexNeg
      have hgj : P.weylGroupToPerm g j =
          -(P.weylGroupToPerm (b.wordProd p) j) := by
        rw [← hg_word]
        change P.weylGroupToPerm (b.wordProd p)
            (P.reflectionPerm j j) = _
        change P.weylGroupToPerm (b.wordProd p) (-j) = _
        exact P.weylGroupToPerm_neg (b.wordProd p) j
      rw [hgj, RootPairing.Base.IsPos.neg_iff_not b] at hgjpos
      exact hgjpos
    rcases b.exchange_word p j hpneg with ⟨l', hl'prod, hl'len⟩
    have hcandidate : ∃ m : List b.support,
        m.length = l'.length ∧ b.wordProd m = g :=
      ⟨l', rfl, hl'prod.trans hg_word⟩
    have hmin : n ≤ l'.length := Nat.find_min' hex hcandidate
    have hp_len : p.length + 1 = l.length := by
      rw [← hl_decomp]
      simp
    omega

section

/-- The reduced crystallographic surjective core of Theorem 1.8.3(i): the
Coxeter matrix whose entries are the actual orders of pairwise products of
simple reflections has a canonical presented group mapping onto the Weyl
group, with the canonical generators mapping to those simple reflections.

The remaining step for the full presentation is injectivity of this map. -/
private lemma coxeterPresentationSurjection_exists
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) :
    ∃ C : CoxeterMatrix b.support, ∃ φ : C.Group →* P.weylGroup,
      (∀ i j : b.support,
        C i j = orderOf (b.simpleReflection i * b.simpleReflection j)) ∧
      (∀ i : b.support, φ (C.simple i) = b.simpleReflection i) ∧
      Function.Surjective φ := by
  have hsimple : Function.Injective b.simpleReflection :=
    b.simpleReflection_injective
  let C : CoxeterMatrix b.support := {
    M := fun i j => orderOf (b.simpleReflection i * b.simpleReflection j)
    isSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      simpa [mul_inv_rev] using
        orderOf_inv (b.simpleReflection i * b.simpleReflection j)
    diagonal i := by simp
    off_diagonal i j hij := by
      intro horder
      have hprod := orderOf_eq_one_iff.mp horder
      apply hij
      apply hsimple
      calc
        b.simpleReflection i = b.simpleReflection i * 1 := by simp
        _ = b.simpleReflection i *
            (b.simpleReflection i * b.simpleReflection j) := by rw [hprod]
        _ = b.simpleReflection j := by simp [← mul_assoc]
  }
  have hC (i j : b.support) :
      C i j = orderOf (b.simpleReflection i * b.simpleReflection j) := rfl
  have hlift : C.IsLiftable b.simpleReflection := by
    intro i j
    change (b.simpleReflection i * b.simpleReflection j) ^
      orderOf (b.simpleReflection i * b.simpleReflection j) = 1
    exact pow_orderOf_eq_one _
  let φ : C.Group →* P.weylGroup :=
    C.toCoxeterSystem.lift ⟨b.simpleReflection, hlift⟩
  have hφsimple (i : b.support) : φ (C.simple i) = b.simpleReflection i := by
    exact C.toCoxeterSystem.lift_apply_simple hlift i
  have hword (l : List b.support) :
      φ (C.toCoxeterSystem.wordProd l) = b.wordProd l := by
    induction l with
    | nil => simp
    | cons i l ih =>
        rw [C.toCoxeterSystem.wordProd_cons, map_mul]
        change φ (C.simple i) * φ (C.toCoxeterSystem.wordProd l) = _
        rw [hφsimple, ih, _root_.RootPairing.Base.wordProd_cons]
  refine ⟨C, φ, hC, hφsimple, ?_⟩
  intro g
  obtain ⟨l, hl⟩ := b.exists_wordProd_eq g
  exact ⟨C.toCoxeterSystem.wordProd l, (hword l).trans hl⟩

end

section

/-- The full Coxeter presentation follows from an explicit deletion
condition.  This conditional form is retained as a reusable assembly lemma.

This is GLS3, Theorem 1.8.3(i). -/
public theorem weylGroup_coxeterPresentation_of_deletion
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base)
    (hdel : ∀ (C : CoxeterMatrix b.support),
      (∀ i j : b.support,
        C i j = orderOf (b.simpleReflection i * b.simpleReflection j)) →
      ∀ l : List b.support, b.wordProd l = 1 →
        Relation.ReflTransGen (CoxeterMove C) l []) :
    ∃ C : CoxeterMatrix b.support, ∃ cs : CoxeterSystem C P.weylGroup,
      (∀ i j : b.support,
        C i j = orderOf (b.simpleReflection i * b.simpleReflection j)) ∧
      (∀ i : b.support,
        CoxeterSystem.simple cs i = b.simpleReflection i) := by
  obtain ⟨C, φ, hC, hφsimple, hsurj⟩ :=
    coxeterPresentationSurjection_exists b
  have hword : ∀ l : List b.support,
      φ (C.toCoxeterSystem.wordProd l) = b.wordProd l := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
        rw [C.toCoxeterSystem.wordProd_cons, map_mul]
        change φ (C.simple i) * φ (C.toCoxeterSystem.wordProd l) = _
        rw [hφsimple, ih, _root_.RootPairing.Base.wordProd_cons]
  have hinv : ∀ l : List b.support,
      b.wordProd l.reverse = (b.wordProd l)⁻¹ := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
        simp only [List.reverse_cons, RootPairing.Base.wordProd_append,
          _root_.RootPairing.Base.wordProd_cons, ih]
        simp
  have happ : ∀ l m : List b.support,
      b.wordProd (l ++ m) = b.wordProd l * b.wordProd m := by
    intro l m
    exact b.wordProd_append l m
  have hinj : Function.Injective φ := by
    apply coxeterHom_injective_of_deletion C φ b.wordProd hword hinv happ
    intro l hl
    exact hdel C hC l hl
  obtain ⟨cs, hcs⟩ := coxeterSystem_of_bijective_presentedGroup_hom C φ
    ⟨hinj, hsurj⟩
  refine ⟨C, cs, hC, ?_⟩
  intro i
  exact (hcs i).trans (hφsimple i)

end

/-- Three distinct support neighbors of one Cartan vertex are all attached by
simple bonds. -/
public lemma cartan_threeNeighbors_incident_products_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a b e : κ) (he : Function.Injective ![c, a, b, e])
    (hca : A c a ≠ 0) (hcb : A c b ≠ 0) (hce : A c e ≠ 0) :
    A c a * A a c = 1 ∧ A c b * A b c = 1 ∧ A c e * A e c = 1 := by
  have hca_ne : c ≠ a := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (1 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 1) hv
  have hcb_ne : c ≠ b := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (2 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 2) hv
  have hce_ne : c ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (0 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (0 : Fin 4) ≠ 3) hv
  have hab_ne : a ≠ b := by
    intro h
    have hv := he (show (![c, a, b, e] (1 : Fin 4)) = (![c, a, b, e] (2 : Fin 4)) by simp [h])
    exact (by decide : (1 : Fin 4) ≠ 2) hv
  have hae_ne : a ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (1 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (1 : Fin 4) ≠ 3) hv
  have hbe_ne : b ≠ e := by
    intro h
    have hv := he (show (![c, a, b, e] (2 : Fin 4)) = (![c, a, b, e] (3 : Fin 4)) by simp [h])
    exact (by decide : (2 : Fin 4) ≠ 3) hv
  have outer_zero (x y : κ) (hcx_ne : c ≠ x) (hcy_ne : c ≠ y)
      (hxy_ne : x ≠ y) (hcx : A c x ≠ 0) (hcy : A c y ≠ 0) :
      A x y = 0 ∧ A y x = 0 := by
    by_cases hxy0 : A x y = 0
    · rcases hrank x y hxy_ne with h0 | h11 | h12 | h21 | h13 | h31
      · exact h0
      all_goals omega
    · have hcxB := cartan_rankTwo_nonzero_bounds A hrank hcx_ne hcx
      have hcyB := cartan_rankTwo_nonzero_bounds A hrank hcy_ne hcy
      have hxyB := cartan_rankTwo_nonzero_bounds A hrank hxy_ne hxy0
      let f : Fin 3 → κ := ![c, x, y]
      have hinj : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [f]
      exfalso
      apply not_cartan_weightedTriangle_of_diagonal_mul_posDef A d hpos ⟨f, hinj⟩
      · intro i
        exact hdiag _
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [f]
  have hab0 := outer_zero a b hca_ne hcb_ne hab_ne hca hcb
  have hae0 := outer_zero a e hca_ne hce_ne hae_ne hca hce
  have hbe0 := outer_zero b e hcb_ne hce_ne hbe_ne hcb hce
  apply cartan_threeStar_incident_products_eq_one
    A d hdiag hrank hpos c a b e he hca hcb hce
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- In a connected finite Cartan support graph, a product-three bond exhausts
the graph, so its two endpoints are the only vertices. -/
public lemma cartan_tripleBond_card_eq_two
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (a b : κ) (hab : a ≠ b) (hprod : A a b * A b a = 3) :
    Fintype.card κ = 2 := by
  have hdeg := cartan_tripleBond_endpoints_degree_one
    A d hdiag hrank hpos a b hab hprod
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hab_nz : A a b ≠ 0 := by
    intro hz
    have hp := hprod
    rw [hz, zero_mul] at hp
    norm_num at hp
  have hba_nz : A b a ≠ 0 := by
    intro hz
    have hp := hprod
    rw [hz, mul_zero] at hp
    norm_num at hp
  have huniqA : ∀ w, G.Adj a w → w = b := by
    obtain ⟨u, hu, huniq⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg.1
    have hu' : u = b := by
      have hbu : b = u := by
        apply huniq b
        change G.Adj a b
        change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj a b
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hab, Or.inl hab_nz⟩
      exact hbu.symm
    intro w hw
    exact hu'.symm ▸ huniq w hw
  have huniqB : ∀ w, G.Adj b w → w = a := by
    obtain ⟨u, hu, huniq⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg.2
    have hu' : u = a := by
      have hau : a = u := by
        apply huniq a
        change G.Adj b a
        change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj b a
        rw [SimpleGraph.fromRel_adj]
        exact ⟨hab.symm, Or.inl hba_nz⟩
      exact hau.symm
    intro w hw
    exact hu'.symm ▸ huniq w hw
  have hall : ∀ j : κ, j = a ∨ j = b := by
    intro j
    apply hconn (fun x => x = a ∨ x = b) (i := a) (j := j)
    · exact Or.inl rfl
    · intro i j hi hji
      rcases hi with hia | hib
      · subst i
        by_cases hja : j = a
        · exact Or.inl hja
        · right
          apply huniqA j
          rw [SimpleGraph.fromRel_adj]
          exact ⟨Ne.symm hja, Or.inr hji⟩
      · subst i
        by_cases hjb : j = b
        · exact Or.inr hjb
        · left
          apply huniqB j
          rw [SimpleGraph.fromRel_adj]
          exact ⟨Ne.symm hjb, Or.inr hji⟩
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_eq_two_iff.mpr
  refine ⟨a, b, hab, ?_⟩
  ext j
  simp [hall j]

open SimpleGraph

/-- The component belonging to a neighbor of the deleted branch center has a
path numbering oriented from that neighbor.  All endpoint and degree facts are
proved as ordinary propositions rather than stored in an arm structure. -/
public lemma simpleGraph_tree_neighbor_component_oriented_pathGraph_numbering
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (c a : V) (hca : G.Adj c a)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (huniq : ∀ v, G.degree v = 3 → v = c) :
    ∃ n : ℕ, ∃ e : Fin (n + 1) ≃
        ((G.induce {c}ᶜ).connectedComponentMk
          (⟨a, by simpa using hca.ne.symm⟩ : ({c}ᶜ : Set V))).supp,
      e 0 = ⟨⟨a, by simpa using hca.ne.symm⟩,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩ ∧
      ∀ i j,
        ((G.induce {c}ᶜ).connectedComponentMk
            (⟨a, by simpa using hca.ne.symm⟩ : ({c}ᶜ : Set V))).toSimpleGraph.Adj (e i) (e j) ↔
          (pathGraph (n + 1)).Adj i j := by
  classical
  let av : ({c}ᶜ : Set V) := ⟨a, by simpa using hca.ne.symm⟩
  let C := (G.induce {c}ᶜ).connectedComponentMk av
  obtain ⟨n, e, he⟩ :=
    simpleGraph_tree_deleted_component_pathGraph_numbering
      G hG c hdegree huniq C
  let u : C.supp := ⟨av, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have ha_ne3 : G.degree a ≠ 3 := by
    intro ha3
    exact hca.ne.symm (huniq a ha3)
  have ha_le2 : G.degree a ≤ 2 := by
    have := hdegree a
    omega
  have hav_le1 : (G.induce {c}ᶜ).degree av ≤ 1 := by
    have hdrop :=
      simpleGraph_induce_compl_singleton_degree_add_one_eq_of_adj G hca
    change (G.induce {c}ᶜ).degree av + 1 = G.degree a at hdrop
    omega
  have hu_le1 : C.toSimpleGraph.degree u ≤ 1 := by
    calc
      C.toSimpleGraph.degree u ≤ (G.induce {c}ᶜ).degree av :=
        simpleGraph_degree_le_of_injective_hom C.toSimpleGraph
          (G.induce {c}ᶜ) C.toSimpleGraph_hom Subtype.val_injective u
      _ ≤ 1 := hav_le1
  obtain ⟨e', he'0, he'⟩ :=
    simpleGraph_pathGraph_numbering_reorient_at_degree_le_one
      C.toSimpleGraph n e he u hu_le1
  exact ⟨n, e', he'0, he'⟩

/-- Bases are in bijection with positive subsystems. -/
public noncomputable def base_equiv_positiveSubsystem
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    P.Base ≃ P.PositiveSubsystem :=
  Equiv.ofBijective RootPairing.Base.toPositiveSubsystem
    ⟨base_toPositiveSubsystem_injective (P := P),
      base_toPositiveSubsystem_surjective P⟩

open scoped SimpleGraph

/-- A nonempty finite Cartan support graph is a tree: the closure-induction
connectedness premise gives connectedness, while positive symmetrizability
gives acyclicity. -/
public lemma cartanSupport_isTree
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    (SimpleGraph.fromRel fun i j => A i j ≠ 0).IsTree := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hpre : G.Preconnected := by
    exact cartanSupport_preconnected A hconn
  have hconn' : G.Connected := ⟨hpre⟩
  have hacyc : G.IsAcyclic := by
    exact cartanSupport_isAcyclic A d hdiag hrank hpos
  exact ⟨hconn', hacyc⟩

open scoped SimpleGraph

/-- Distinct support neighbors of one Cartan vertex cannot be adjacent when the
support graph is acyclic.  Consequently both directed Cartan entries between
the two neighbors vanish. -/
public lemma cartanSupport_two_neighbors_nonadjacent
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a b : κ)
    (he : Function.Injective ![c, a, b])
    (hca : (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c a)
    (hcb : (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c b) :
    A a b = 0 ∧ A b a = 0 := by
  let G : SimpleGraph κ := SimpleGraph.fromRel (fun i j => A i j ≠ 0)
  have hacyc : G.IsAcyclic := by
    exact cartanSupport_isAcyclic A d hdiag hrank hpos
  have hcaG : G.Adj c a := hca
  have hcbG : G.Adj c b := hcb
  have hneca : c ≠ a := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (he (by simp [h]))
  have hnecb : c ≠ b := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (he (by simp [h]))
  have hneab : a ≠ b := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (he (by simp [h]))
  have hneac : a ≠ c := hneca.symm
  have hnebc : b ≠ c := hnecb.symm
  have hnabG : ¬ G.Adj a b := by
    intro habG
    let w : G.Walk c c := SimpleGraph.Walk.cons hcaG
      (SimpleGraph.Walk.cons habG
        (SimpleGraph.Walk.cons hcbG.symm SimpleGraph.Walk.nil))
    have hw : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      simp [w, hneca, hnecb, hneab, hneac, hnebc]
    exact hacyc w hw
  have hnabRel : ¬ (A a b ≠ 0 ∨ A b a ≠ 0) := by
    intro hab
    apply hnabG
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hneab, hab⟩
  exact by
    push Not at hnabRel
    exact hnabRel

/-- A simple root reflection has determinant `-1` on the root space. -/
public lemma _root_.RootPairing.Base.det_simpleReflection
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    (b : P.Base) (j : b.support) :
    LinearEquiv.det (RootPairing.Equiv.weightEquiv P P
      (b.simpleReflection j : RootPairing.Aut P)) = (-1 : Rˣ) := by
  classical
  letI : Fintype b.support := Fintype.ofFinite b.support
  let : Module.Finite R M := Module.Finite.of_basis b.toWeightBasis
  let B := b.toWeightBasis
  let f : M →ₗ[R] M := P.reflection j
  let A : Matrix b.support b.support R := LinearMap.toMatrix B B f
  let c : b.support → R := A j
  have hrows : A = Matrix.updateRow 1 j c := by
    ext r k
    by_cases hr : r = j
    · subst r
      simp [c]
    · simp only [Matrix.updateRow_apply, if_neg hr, Matrix.one_apply]
      change (LinearMap.toMatrix B B f) r k = if r = k then 1 else 0
      rw [LinearMap.toMatrix_apply]
      simp [f, B, P.reflection_apply_root, hr, Finsupp.single_apply, eq_comm]
  have hc : c = ∑ k, c k • (1 : Matrix b.support b.support R) k := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
    simp
  have hcj : c j = -1 := by
    dsimp [c, A, f, B]
    rw [LinearMap.toMatrix_apply]
    simp
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [← LinearMap.det_toMatrix B]
  change A.det = (-1 : R)
  rw [hrows, hc, Matrix.det_updateRow_sum, hcj]
  simp

/-- Determinant character of the Weyl group on the root space. -/
public noncomputable def _root_.RootPairing.weylDet
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) : P.weylGroup →* Rˣ :=
  LinearEquiv.det.comp ((RootPairing.Equiv.weightHom P).comp P.weylGroup.subtype)

public lemma _root_.RootPairing.Base.weylDet_simpleReflection
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    (b : P.Base) (j : b.support) :
    P.weylDet (b.simpleReflection j) = (-1 : Rˣ) := by
  classical
  letI : Fintype b.support := Fintype.ofFinite b.support
  let : Module.Finite R M := Module.Finite.of_basis b.toWeightBasis
  exact b.det_simpleReflection j

public lemma _root_.RootPairing.Base.weylDet_wordProd
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    (b : P.Base) (l : List b.support) :
    P.weylDet (b.wordProd l) = (-1 : Rˣ) ^ l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [b.wordProd_cons, map_mul, b.weylDet_simpleReflection, ih]
      simp [pow_succ, mul_comm]

/-- The type of positive roots sent to negative roots by a Weyl-group element. -/
public abbrev _root_.RootPairing.Base.InversionRoot
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (g : P.weylGroup) :=
  {i : ι // b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm g i)}

/-- The number `N_b(g)` of positive roots sent to negative roots by `g`. -/
@[expose]
public noncomputable def _root_.RootPairing.Base.inversionNumber
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) (g : P.weylGroup) : ℕ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact Fintype.card (b.InversionRoot g)

public lemma _root_.RootPairing.Base.inversion_iff_mul_simpleReflection_of_isPos
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support)
    (hpos : b.IsPos (P.weylGroupToPerm g j)) (i : ι) :
    (b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm (g * b.simpleReflection j) i)) ↔
      i = j ∨ ∃ k, b.IsPos k ∧ ¬ b.IsPos (P.weylGroupToPerm g k) ∧
        i = P.reflectionPerm j k := by
  letI := P.indexNeg
  constructor
  · rintro ⟨hipos, hineg⟩
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      refine ⟨P.reflectionPerm j i, hipos.reflectionPerm j.property hij, ?_, ?_⟩
      · change ¬ b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j i)) at hineg
        exact hineg
      · symm
        exact P.reflectionPerm_self j i
  · rintro (rfl | ⟨k, hkpos, hkneg, rfl⟩)
    · refine ⟨b.isPos_of_mem_support j.property, ?_⟩
      change ¬ b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j j))
      change ¬ b.IsPos (P.weylGroupToPerm g (-j))
      rw [P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not b]
      exact not_not_intro hpos
    · have hkj : k ≠ j := by
        intro hkj
        subst k
        exact hkneg hpos
      refine ⟨hkpos.reflectionPerm j.property hkj, ?_⟩
      change ¬ b.IsPos
        (P.weylGroupToPerm g (P.reflectionPerm j (P.reflectionPerm j k)))
      simpa using hkneg

public lemma _root_.RootPairing.Base.inversionNumber_mul_simpleReflection_of_isPos
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support)
    (hpos : b.IsPos (P.weylGroupToPerm g j)) :
    b.inversionNumber (g * b.simpleReflection j) = b.inversionNumber g + 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI := P.indexNeg
  have hgjneg : ¬ b.IsPos (P.weylGroupToPerm (g * b.simpleReflection j) j) := by
    change ¬ b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j j))
    change ¬ b.IsPos (P.weylGroupToPerm g (-j))
    rw [P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not b]
    exact not_not_intro hpos
  let e : b.InversionRoot (g * b.simpleReflection j) ≃ Option (b.InversionRoot g) := {
    toFun x := if hx : x.val = j then none else
      some ⟨P.reflectionPerm j x.val,
        x.property.1.reflectionPerm j.property hx,
        by
          change ¬ b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j x.val))
          exact x.property.2⟩
    invFun x := match x with
      | none => ⟨j, b.isPos_of_mem_support j.property, hgjneg⟩
      | some x =>
          have hxj : x.val ≠ j := by
            intro hxj
            exact x.property.2 (hxj ▸ hpos)
          ⟨P.reflectionPerm j x.val,
            x.property.1.reflectionPerm j.property hxj,
            by
              change ¬ b.IsPos
                (P.weylGroupToPerm g (P.reflectionPerm j (P.reflectionPerm j x.val)))
              simpa using x.property.2⟩
    left_inv x := by
      by_cases hx : x.val = j
      · simp only [dif_pos hx]
        apply Subtype.ext
        exact hx.symm
      · simp only [dif_neg hx]
        apply Subtype.ext
        exact P.reflectionPerm_self j x.val
    right_inv x := by
      cases x with
      | none => simp
      | some x =>
          have hxj : x.val ≠ j := by
            intro hxj
            exact x.property.2 (hxj ▸ hpos)
          have hrefj : P.reflectionPerm j x.val ≠ j := by
            intro h
            have h' := congrArg (P.reflectionPerm j) h
            have hxneg : x.val = -(j : ι) := by simpa using h'
            have hxpos := x.property.1
            rw [hxneg, RootPairing.Base.IsPos.neg_iff_not b] at hxpos
            exact hxpos (b.isPos_of_mem_support j.property)
          simp only [dif_neg hrefj]
          apply congrArg some
          apply Subtype.ext
          exact P.reflectionPerm_self j x.val
  }
  change Fintype.card (b.InversionRoot (g * b.simpleReflection j)) =
    Fintype.card (b.InversionRoot g) + 1
  rw [Fintype.card_congr e, Fintype.card_option]

@[simp]
public lemma _root_.RootPairing.Base.inversionNumber_one
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (b : P.Base) : b.inversionNumber 1 = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  exact x.property.2 (by simpa using x.property.1)

public lemma _root_.RootPairing.Base.inversionNumber_mul_simpleReflection_of_not_isPos
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support)
    (hneg : ¬ b.IsPos (P.weylGroupToPerm g j)) :
    b.inversionNumber (g * b.simpleReflection j) + 1 = b.inversionNumber g := by
  letI := P.indexNeg
  have hpos : b.IsPos (P.weylGroupToPerm (g * b.simpleReflection j) j) := by
    change b.IsPos (P.weylGroupToPerm g (P.reflectionPerm j j))
    change b.IsPos (P.weylGroupToPerm g (-j))
    rw [P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not b]
    exact hneg
  have h := b.inversionNumber_mul_simpleReflection_of_isPos
    (g * b.simpleReflection j) j hpos
  have hsq : (g * b.simpleReflection j) * b.simpleReflection j = g := by
    rw [mul_assoc, b.simpleReflection_mul_self, mul_one]
  rw [hsq] at h
  exact h.symm

/-- Theorem 1.8.3(d): right multiplication by a simple reflection changes
word length by one, with the sign determined by the image of its simple root. -/
public theorem wordLength_simpleReflection_iff_isPositive
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) (j : b.support) :
    (b.wordLength (g * b.simpleReflection j) = b.wordLength g + 1 ↔
      b.IsPos (P.weylGroupToPerm g j)) ∧
    (b.wordLength (g * b.simpleReflection j) + 1 = b.wordLength g ↔
      ¬ b.IsPos (P.weylGroupToPerm g j)) := by
  constructor
  · constructor
    · intro hlen
      by_contra hneg
      have h := b.wordLength_mul_simpleReflection_of_not_isPos g j hneg
      omega
    · exact b.wordLength_mul_simpleReflection_of_isPos g j
  · constructor
    · intro hlen hpos
      have h := b.wordLength_mul_simpleReflection_of_isPos g j hpos
      omega
    · exact b.wordLength_mul_simpleReflection_of_not_isPos g j

/-- The Weyl group acts regularly on the set of bases: the action is
transitive and has trivial point stabilizers.

This is GLS3, Theorem 1.8.2. -/
public theorem weylGroup_action_on_bases_regular
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    MulAction.IsPretransitive P.weylGroup P.Base ∧ IsCancelSMul P.weylGroup P.Base :=
  ⟨weylGroup_action_on_bases_transitive P,
    weylGroup_action_on_bases_free P⟩

/-- Every edge incident to a degree-three Cartan support vertex has bond
product one. -/
public lemma cartanSupport_degree_three_edgeProduct_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c = 3)
    (hadj : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c a) :
    A c a * A a c = 1 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hdegG : G.degree c = 3 := hdeg
  have hcard : Fintype.card (G.neighborSet c) = 3 := by
    exact (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := c)).trans hdegG
  let E : Fin 3 ≃ G.neighborSet c := (Fintype.equivFinOfCardEq hcard).symm
  let l : Fin 3 → κ := fun i => (E i).1
  have hl_adj (i : Fin 3) : G.Adj c (l i) := (E i).2
  have hl_inj : Function.Injective l := by
    intro i j hij
    apply E.injective
    apply Subtype.ext
    exact hij
  have hc_ne (i : Fin 3) : c ≠ l i := (hl_adj i).ne
  have hlc_ne (i : Fin 3) : l i ≠ c := (hc_ne i).symm
  have hl01 : l 0 ≠ l 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (hl_inj h)
  have hl02 : l 0 ≠ l 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (hl_inj h)
  have hl12 : l 1 ≠ l 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (hl_inj h)
  have he : Function.Injective ![c, l 0, l 1, l 2] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hnz (i : Fin 3) : A c (l i) ≠ 0 := by
    have hi := hl_adj i
    change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c (l i) at hi
    rw [SimpleGraph.fromRel_adj] at hi
    rcases hi.2 with hforward | hreverse
    · exact hforward
    · have hb := cartan_rankTwo_nonzero_bounds A hrank hi.1.symm hreverse
      omega
  have hp := cartan_threeNeighbors_incident_products_eq_one
    A d hdiag hrank hpos c (l 0) (l 1) (l 2) he (hnz 0) (hnz 1) (hnz 2)
  let aa : G.neighborSet c := ⟨a, hadj⟩
  obtain ⟨i, hi⟩ := E.surjective aa
  have hia : l i = a := congrArg Subtype.val hi
  rcases hp with ⟨hp0, hp1, hp2⟩
  fin_cases i
  · subst a
    exact hp0
  · subst a
    exact hp1
  · subst a
    exact hp2

open SimpleGraph

/-- A finite tree with a unique degree-three center is the center together with
three oriented path components.  The result uses an ordinary `Option`/`Sum`
equivalence and explicit adjacency equivalences; no arm structure stores a
graph or classification conclusion. -/
public lemma simpleGraph_tree_three_arm_global_sigma_numbering
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (c : V)
    (hdegree : ∀ v, G.degree v ≤ 3)
    (hcenter : G.degree c = 3)
    (huniq : ∀ v, G.degree v = 3 → v = c) :
    ∃ a : Fin 3 → V, (∀ i, G.Adj c (a i)) ∧
    ∃ n0 n1 n2 : ℕ,
      ∃ e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ V,
        e none = c ∧
        e (some (Sum.inl 0)) = a 0 ∧
        e (some (Sum.inr (Sum.inl 0))) = a 1 ∧
        e (some (Sum.inr (Sum.inr 0))) = a 2 ∧
        (∀ j, G.Adj (e none) (e (some (Sum.inl j))) ↔ j = 0) ∧
        (∀ j, G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0) ∧
        (∀ j, G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0) ∧
        (∀ j l, G.Adj (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
          (pathGraph (n0 + 1)).Adj j l) ∧
        (∀ j l, G.Adj (e (some (Sum.inr (Sum.inl j))))
          (e (some (Sum.inr (Sum.inl l)))) ↔
          (pathGraph (n1 + 1)).Adj j l) ∧
        (∀ j l, G.Adj (e (some (Sum.inr (Sum.inr j))))
          (e (some (Sum.inr (Sum.inr l)))) ↔
          (pathGraph (n2 + 1)).Adj j l) ∧
        (∀ j l, ¬ G.Adj (e (some (Sum.inl j)))
          (e (some (Sum.inr (Sum.inl l))))) ∧
        (∀ j l, ¬ G.Adj (e (some (Sum.inl j)))
          (e (some (Sum.inr (Sum.inr l))))) ∧
        (∀ j l, ¬ G.Adj (e (some (Sum.inr (Sum.inl j))))
          (e (some (Sum.inr (Sum.inr l))))) := by
  classical
  obtain ⟨a, ha, hainj, hcompinj, hcover⟩ :=
    simpleGraph_tree_degree_three_deleted_components G hG c hcenter
  choose n en henz hpath using fun i =>
    simpleGraph_tree_neighbor_component_oriented_pathGraph_numbering
      G hG c (a i) (ha i) hdegree huniq
  let n0 := n 0
  let n1 := n 1
  let n2 := n 2
  let e₀ : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) → V := fun x =>
    match x with
    | none => c
    | some (Sum.inl j) => (en 0 j).1.1
    | some (Sum.inr (Sum.inl j)) => (en 1 j).1.1
    | some (Sum.inr (Sum.inr j)) => (en 2 j).1.1
  have he₀_none : e₀ none = c := rfl
  have he₀_zero : e₀ (some (Sum.inl 0)) = a 0 := by
    exact congrArg Subtype.val (congrArg (fun z => z.1) (henz 0))
  have he₁_zero : e₀ (some (Sum.inr (Sum.inl 0))) = a 1 := by
    exact congrArg Subtype.val (congrArg (fun z => z.1) (henz 1))
  have he₂_zero : e₀ (some (Sum.inr (Sum.inr 0))) = a 2 := by
    exact congrArg Subtype.val (congrArg (fun z => z.1) (henz 2))
  have hcomp_eq_of_vertex_eq : ∀ i (j : Fin (n i + 1)),
      (G.induce {c}ᶜ).connectedComponentMk (en i j) =
        (G.induce {c}ᶜ).connectedComponentMk
          ⟨a i, by simpa using (ha i).ne.symm⟩ := by
    intro i j
    exact ((G.induce {c}ᶜ).connectedComponentMk
      ⟨a i, by simpa using (ha i).ne.symm⟩).mem_supp_iff _ |>.mp
        (en i j).property
  have he₀_inj : Function.Injective e₀ := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some z =>
            cases z with
            | inl j =>
                exact False.elim ((en 0 j).1.2 hxy.symm)
            | inr z =>
                cases z with
                | inl j => exact False.elim ((en 1 j).1.2 hxy.symm)
                | inr j => exact False.elim ((en 2 j).1.2 hxy.symm)
    | some x =>
        cases y with
        | none =>
            cases x with
            | inl j => exact False.elim ((en 0 j).1.2 hxy)
            | inr z =>
                cases z with
                | inl j => exact False.elim ((en 1 j).1.2 hxy)
                | inr j => exact False.elim ((en 2 j).1.2 hxy)
        | some y =>
            cases x with
            | inl j =>
                cases y with
                | inl l =>
                    change (en 0 j).1.1 = (en 0 l).1.1 at hxy
                    exact congrArg (fun q => some (Sum.inl q))
                      ((en 0).injective (Subtype.ext (Subtype.ext hxy)))
                | inr z =>
                    cases z with
                    | inl l =>
                        exfalso
                        change (en 0 j).1.1 = (en 1 l).1.1 at hxy
                        have hvsub : (⟨(en 0 j).1.1, (en 0 j).1.2⟩ : ({c}ᶜ : Set V)) =
                            ⟨(en 1 l).1.1, (en 1 l).1.2⟩ := Subtype.ext hxy
                        have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                          hvsub
                        exact ((show (0 : Fin 3) ≠ 1 from by decide)
                          (hcompinj ((hcomp_eq_of_vertex_eq 0 j).symm.trans
                            (heq.trans (hcomp_eq_of_vertex_eq 1 l))))).elim
                    | inr l =>
                        exfalso
                        change (en 0 j).1.1 = (en 2 l).1.1 at hxy
                        have hvsub : (⟨(en 0 j).1.1, (en 0 j).1.2⟩ : ({c}ᶜ : Set V)) =
                            ⟨(en 2 l).1.1, (en 2 l).1.2⟩ := Subtype.ext hxy
                        have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                          hvsub
                        exact ((show (0 : Fin 3) ≠ 2 from by decide)
                          (hcompinj ((hcomp_eq_of_vertex_eq 0 j).symm.trans
                            (heq.trans (hcomp_eq_of_vertex_eq 2 l))))).elim
            | inr z =>
                cases z with
                | inl j =>
                    cases y with
                    | inl l =>
                        exfalso
                        change (en 1 j).1.1 = (en 0 l).1.1 at hxy
                        have hvsub : (⟨(en 1 j).1.1, (en 1 j).1.2⟩ : ({c}ᶜ : Set V)) =
                            ⟨(en 0 l).1.1, (en 0 l).1.2⟩ := Subtype.ext hxy
                        have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                          hvsub
                        exact ((show (1 : Fin 3) ≠ 0 from by decide)
                          (hcompinj ((hcomp_eq_of_vertex_eq 1 j).symm.trans
                            (heq.trans (hcomp_eq_of_vertex_eq 0 l))))).elim
                    | inr w =>
                        cases w with
                        | inl l =>
                            change (en 1 j).1.1 = (en 1 l).1.1 at hxy
                            exact congrArg (fun q => some (Sum.inr (Sum.inl q)))
                              ((en 1).injective (Subtype.ext (Subtype.ext hxy)))
                        | inr l =>
                            exfalso
                            change (en 1 j).1.1 = (en 2 l).1.1 at hxy
                            have hvsub : (⟨(en 1 j).1.1, (en 1 j).1.2⟩ : ({c}ᶜ : Set V)) =
                                ⟨(en 2 l).1.1, (en 2 l).1.2⟩ := Subtype.ext hxy
                            have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                              hvsub
                            exact ((show (1 : Fin 3) ≠ 2 from by decide)
                              (hcompinj ((hcomp_eq_of_vertex_eq 1 j).symm.trans
                                (heq.trans (hcomp_eq_of_vertex_eq 2 l))))).elim
                | inr j =>
                    cases y with
                    | inl l =>
                        exfalso
                        change (en 2 j).1.1 = (en 0 l).1.1 at hxy
                        have hvsub : (⟨(en 2 j).1.1, (en 2 j).1.2⟩ : ({c}ᶜ : Set V)) =
                            ⟨(en 0 l).1.1, (en 0 l).1.2⟩ := Subtype.ext hxy
                        have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                          hvsub
                        exact ((show (2 : Fin 3) ≠ 0 from by decide)
                          (hcompinj ((hcomp_eq_of_vertex_eq 2 j).symm.trans
                            (heq.trans (hcomp_eq_of_vertex_eq 0 l))))).elim
                    | inr w =>
                        cases w with
                        | inl l =>
                            exfalso
                            change (en 2 j).1.1 = (en 1 l).1.1 at hxy
                            have hvsub : (⟨(en 2 j).1.1, (en 2 j).1.2⟩ : ({c}ᶜ : Set V)) =
                                ⟨(en 1 l).1.1, (en 1 l).1.2⟩ := Subtype.ext hxy
                            have heq := congrArg (G.induce {c}ᶜ).connectedComponentMk
                              hvsub
                            exact ((show (2 : Fin 3) ≠ 1 from by decide)
                              (hcompinj ((hcomp_eq_of_vertex_eq 2 j).symm.trans
                                (heq.trans (hcomp_eq_of_vertex_eq 1 l))))).elim
                        | inr l =>
                            change (en 2 j).1.1 = (en 2 l).1.1 at hxy
                            exact congrArg (fun q => some (Sum.inr (Sum.inr q)))
                              ((en 2).injective (Subtype.ext (Subtype.ext hxy)))
  have he₀_surj : Function.Surjective e₀ := by
    intro v
    by_cases hvc : v = c
    · exact ⟨none, by simpa [e₀] using hvc.symm⟩
    · let vv : {v : V // v ≠ c} := ⟨v, hvc⟩
      obtain ⟨i, hi⟩ := hcover vv
      obtain ⟨j, hj⟩ := (en i).surjective ⟨vv, (by
        exact ((G.induce {c}ᶜ).connectedComponentMk
          ⟨a i, by simpa using (ha i).ne.symm⟩).mem_supp_iff _ |>.mpr
            (by exact hi))⟩
      fin_cases i
      · exact ⟨some (Sum.inl j), congrArg (fun q => q.1.1) hj⟩
      · exact ⟨some (Sum.inr (Sum.inl j)), congrArg (fun q => q.1.1) hj⟩
      · exact ⟨some (Sum.inr (Sum.inr j)), congrArg (fun q => q.1.1) hj⟩
  let e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ V :=
    Equiv.ofBijective e₀ ⟨he₀_inj, he₀_surj⟩
  have hc_adj0 : ∀ j : Fin (n0 + 1),
      G.Adj (e none) (e (some (Sum.inl j))) ↔ j = 0 := by
    intro j
    change G.Adj c ((en 0 j).1.1) ↔ j = 0
    have hcomp := hcomp_eq_of_vertex_eq 0 j
    constructor
    · intro hcj
      obtain ⟨x, hx, hxreach, hxuniq⟩ :=
        simpleGraph_tree_existsUnique_neighbor_reachable_without_center
          G hG c (en 0 j).1.1 (en 0 j).1.2
      have hvrefl : (G.induce {c}ᶜ).Reachable (en 0 j) (en 0 j) :=
        ⟨SimpleGraph.Walk.nil⟩
      have hjx : (en 0 j).1.1 = x := hxuniq _ hcj hvrefl
      have h0x : a 0 = x := hxuniq (a 0) (ha 0) (SimpleGraph.ConnectedComponent.exact hcomp).symm
      have hval : (en 0 j).1.1 = a 0 := hjx.trans h0x.symm
      apply (en 0).injective
      exact Subtype.ext (Subtype.ext (hval.trans he₀_zero.symm))
    · intro hj
      subst j
      rw [show (en 0 0).1.1 = a 0 by exact he₀_zero]
      exact ha 0
  have hc_adj1 : ∀ j : Fin (n1 + 1),
      G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0 := by
    intro j
    change G.Adj c ((en 1 j).1.1) ↔ j = 0
    constructor
    · intro hcj
      obtain ⟨x, hx, hxreach, hxuniq⟩ :=
        simpleGraph_tree_existsUnique_neighbor_reachable_without_center
          G hG c (en 1 j).1.1 (en 1 j).1.2
      have hvrefl : (G.induce {c}ᶜ).Reachable (en 1 j) (en 1 j) :=
        ⟨SimpleGraph.Walk.nil⟩
      have hjx : (en 1 j).1.1 = x := hxuniq _ hcj hvrefl
      have h0x : a 1 = x := hxuniq (a 1) (ha 1) (SimpleGraph.ConnectedComponent.exact
        (hcomp_eq_of_vertex_eq 1 j)).symm
      have hval : (en 1 j).1.1 = a 1 := hjx.trans h0x.symm
      apply (en 1).injective
      exact Subtype.ext (Subtype.ext (hval.trans he₁_zero.symm))
    · intro hj
      subst j
      rw [show (en 1 0).1.1 = a 1 by exact he₁_zero]
      exact ha 1
  have hc_adj2 : ∀ j : Fin (n2 + 1),
      G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0 := by
    intro j
    change G.Adj c ((en 2 j).1.1) ↔ j = 0
    constructor
    · intro hcj
      obtain ⟨x, hx, hxreach, hxuniq⟩ :=
        simpleGraph_tree_existsUnique_neighbor_reachable_without_center
          G hG c (en 2 j).1.1 (en 2 j).1.2
      have hvrefl : (G.induce {c}ᶜ).Reachable (en 2 j) (en 2 j) :=
        ⟨SimpleGraph.Walk.nil⟩
      have hjx : (en 2 j).1.1 = x := hxuniq _ hcj hvrefl
      have h0x : a 2 = x := hxuniq (a 2) (ha 2) (SimpleGraph.ConnectedComponent.exact
        (hcomp_eq_of_vertex_eq 2 j)).symm
      have hval : (en 2 j).1.1 = a 2 := hjx.trans h0x.symm
      apply (en 2).injective
      exact Subtype.ext (Subtype.ext (hval.trans he₂_zero.symm))
    · intro hj
      subst j
      rw [show (en 2 0).1.1 = a 2 by exact he₂_zero]
      exact ha 2
  have ha_adj0 : ∀ j l, G.Adj (e (some (Sum.inl j)))
      (e (some (Sum.inl l))) ↔ (pathGraph (n0 + 1)).Adj j l := by
    intro j l
    change G.Adj ((en 0 j).1.1) ((en 0 l).1.1) ↔ _
    exact hpath 0 j l
  have ha_adj1 : ∀ j l, G.Adj (e (some (Sum.inr (Sum.inl j))))
      (e (some (Sum.inr (Sum.inl l)))) ↔ (pathGraph (n1 + 1)).Adj j l := by
    intro j l
    change G.Adj ((en 1 j).1.1) ((en 1 l).1.1) ↔ _
    exact hpath 1 j l
  have ha_adj2 : ∀ j l, G.Adj (e (some (Sum.inr (Sum.inr j))))
      (e (some (Sum.inr (Sum.inr l)))) ↔ (pathGraph (n2 + 1)).Adj j l := by
    intro j l
    change G.Adj ((en 2 j).1.1) ((en 2 l).1.1) ↔ _
    exact hpath 2 j l
  have hcross01 : ∀ j l, ¬ G.Adj (e (some (Sum.inl j)))
      (e (some (Sum.inr (Sum.inl l)))) := by
    intro j l hadj
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := G.induce {c}ᶜ) (show (G.induce {c}ᶜ).Adj (en 0 j) (en 1 l) from hadj)
    exact (show (0 : Fin 3) ≠ 1 from by decide)
      (hcompinj ((hcomp_eq_of_vertex_eq 0 j).symm.trans
        (heq.trans (hcomp_eq_of_vertex_eq 1 l))))
  have hcross02 : ∀ j l, ¬ G.Adj (e (some (Sum.inl j)))
      (e (some (Sum.inr (Sum.inr l)))) := by
    intro j l hadj
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := G.induce {c}ᶜ) (show (G.induce {c}ᶜ).Adj (en 0 j) (en 2 l) from hadj)
    exact (show (0 : Fin 3) ≠ 2 from by decide)
      (hcompinj ((hcomp_eq_of_vertex_eq 0 j).symm.trans
        (heq.trans (hcomp_eq_of_vertex_eq 2 l))))
  have hcross12 : ∀ j l, ¬ G.Adj (e (some (Sum.inr (Sum.inl j))))
      (e (some (Sum.inr (Sum.inr l)))) := by
    intro j l hadj
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := G.induce {c}ᶜ) (show (G.induce {c}ᶜ).Adj (en 1 j) (en 2 l) from hadj)
    exact (show (1 : Fin 3) ≠ 2 from by decide)
      (hcompinj ((hcomp_eq_of_vertex_eq 1 j).symm.trans
        (heq.trans (hcomp_eq_of_vertex_eq 2 l))))
  refine ⟨a, ha, n0, n1, n2, e, he₀_none, he₀_zero, he₁_zero, he₂_zero,
    hc_adj0, hc_adj1, hc_adj2, ha_adj0, ha_adj1, ha_adj2,
    hcross01, hcross02, hcross12⟩

/-- Deleting a support-graph leaf preserves the Cartan closure-induction
connectedness premise on the complementary principal submatrix. -/
public lemma cartanSubmatrix_compl_leaf_closureInduction
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nontrivial κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (v : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1) :
    ∀ (p : {i : κ // i ≠ v} → Prop) {i j : {i : κ // i ≠ v}}, p i →
      (∀ i j, p i → A.submatrix Subtype.val Subtype.val j i ≠ 0 → p j) → p j := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have htree : G.IsTree := by
    exact cartanSupport_isTree A d hdiag hrank hconn hpos
  have hpre : (G.induce {v}ᶜ).Preconnected :=
    (htree.connected.induce_compl_singleton_of_degree_eq_one hdeg).preconnected
  have hgraph :
      (SimpleGraph.fromRel fun i j : {i : κ // i ≠ v} =>
        A.submatrix Subtype.val Subtype.val i j ≠ 0) = G.induce {v}ᶜ := by
    ext i j
    change (SimpleGraph.fromRel fun i j : {i : κ // i ≠ v} =>
      A.submatrix Subtype.val Subtype.val i j ≠ 0).Adj i j ↔ G.Adj i j
    rw [SimpleGraph.fromRel_adj]
    change (i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0)) ↔
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj i j
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hij, hA⟩
      exact ⟨fun h => hij (Subtype.ext h), hA⟩
    · rintro ⟨hij, hA⟩
      exact ⟨fun h => hij (congrArg Subtype.val h), hA⟩
  apply cartanClosureInduction_of_support_preconnected
    (A.submatrix Subtype.val Subtype.val)
  · intro i j hij
    exact hrank i j (fun h => hij (Subtype.ext h))
  · rw [hgraph]
    exact hpre

/-- A nontrivial finite connected positive-definite Cartan support graph has a
leaf. -/
public lemma cartanSupport_exists_leaf
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nontrivial κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    ∃ v, (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1 := by
  classical
  exact (cartanSupport_isTree A d hdiag hrank hconn hpos).exists_vert_degree_one_of_nontrivial

open scoped BigOperators

/-- A nontrivial finite Cartan support tree has two distinct leaves.  This is
the finite-tree endpoint needed when a path branch is chosen for induction. -/
public lemma cartanSupport_exists_two_leaves
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nontrivial κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    ∃ u v, u ≠ v ∧
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree u = 1 ∧
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have htree : G.IsTree := by
    exact cartanSupport_isTree A d hdiag hrank hconn hpos
  obtain ⟨u, hu⟩ := htree.exists_vert_degree_one_of_nontrivial
  by_contra hnone
  have hdegpos : ∀ w, 0 < G.degree w := by
    intro w
    exact htree.connected.preconnected.degree_pos_of_nontrivial w
  have hdeg2 : ∀ w, w ≠ u → 2 ≤ G.degree w := by
    intro w hwu
    have hne : G.degree w ≠ 1 := by
      intro hw
      exact hnone ⟨w, u, hwu, hw, hu⟩
    have hp := hdegpos w
    omega
  have hsumlower : 1 + 2 * (Fintype.card κ - 1) ≤ ∑ w, G.degree w := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
    have hrest : ∑ w ∈ Finset.univ.erase u, 2 ≤
        ∑ w ∈ Finset.univ.erase u, G.degree w := by
      apply Finset.sum_le_sum
      intro w hw
      exact hdeg2 w (Finset.ne_of_mem_erase hw)
    have hcard : (Finset.univ.erase u).card = Fintype.card κ - 1 := by
      simp
    have hrest' : 2 * (Finset.univ.erase u).card ≤
        ∑ w ∈ Finset.univ.erase u, G.degree w := by
      simpa [Finset.sum_const, Nat.mul_comm] using hrest
    rw [hcard] at hrest'
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hedge := htree.card_edgeFinset
  omega

open SimpleGraph

/-- A nonempty connected positive-definite Cartan support graph whose degrees
are all at most two admits an exact finite path-graph numbering. -/
public lemma cartanSupport_pathGraph_numbering_of_degree_le_two
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (hdegree : ∀ x, (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree x ≤ 2) :
    ∃ n : ℕ, ∃ e : Fin n ≃ κ,
      ∀ i j,
        (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
          (pathGraph n).Adj i j := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have htree : G.IsTree := cartanSupport_isTree A d hdiag hrank hconn hpos
  exact simpleGraph_pathGraph_numbering_of_isTree_degree_le_two G htree hdegree

/-- The determinant assertion of Theorem 1.8.3(c): the determinant of a Weyl
element on the root space is `(-1)` raised to its simple-reflection length. -/
public theorem weylDet_eq_negOne_pow_wordLength
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) :
    P.weylDet g = (-1 : Rˣ) ^ b.wordLength g := by
  rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
  calc
    P.weylDet g = P.weylDet (b.wordProd l) := congrArg P.weylDet hprod.symm
    _ = (-1 : Rˣ) ^ l.length := b.weylDet_wordProd l
    _ = (-1 : Rˣ) ^ b.wordLength g := by rw [hlen]

/-- The first assertion of Theorem 1.8.3(c): shortest simple-reflection word
length equals the number of positive roots transformed to negative roots. -/
public theorem wordLength_eq_inversionNumber
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (g : P.weylGroup) :
    b.wordLength g = b.inversionNumber g := by
  generalize hn : b.wordLength g = n
  induction n using Nat.strong_induction_on generalizing g with
  | h n ih =>
      rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
      by_cases hl : l = []
      · subst l
        have hg : g = 1 := by simpa using hprod.symm
        subst g
        simpa using hn.symm
      · let j : b.support := l.getLast hl
        let p : List b.support := l.dropLast
        have hl_decomp : p ++ [j] = l := List.dropLast_append_getLast hl
        have hg : b.wordProd p * b.simpleReflection j = g := by
          change b.wordProd p * b.wordProd [j] = g
          rw [← b.wordProd_append, hl_decomp, hprod]
        have hp_le : b.wordLength (b.wordProd p) ≤ p.length :=
          b.wordLength_le _ p rfl
        have hg_le := b.wordLength_mul_simpleReflection_le
          (b.wordProd p) j
        rw [hg] at hg_le
        have hp_len : b.wordLength (b.wordProd p) = p.length := by
          rw [← hlen, ← hl_decomp] at hg_le
          simp only [List.length_append, List.length_singleton] at hg_le
          omega
        have hp_lt : b.wordLength (b.wordProd p) < n := by
          rw [hp_len, ← hn, ← hlen, ← hl_decomp]
          simp
        have ihp := ih _ hp_lt (b.wordProd p) rfl
        have hpos : b.IsPos (P.weylGroupToPerm (b.wordProd p) j) := by
          by_contra hneg
          have hdec := b.wordLength_mul_simpleReflection_of_not_isPos
            (b.wordProd p) j hneg
          rw [hg, hp_len, ← hlen, ← hl_decomp] at hdec
          simp at hdec
          omega
        have hN := b.inversionNumber_mul_simpleReflection_of_isPos
          (b.wordProd p) j hpos
        rw [hg] at hN
        have hn_len : n = p.length + 1 := by
          rw [← hn, ← hlen, ← hl_decomp]
          simp
        calc
          n = p.length + 1 := hn_len
          _ = b.wordLength (b.wordProd p) + 1 := by rw [hp_len]
          _ = b.inversionNumber (b.wordProd p) + 1 := by rw [ihp]
          _ = b.inversionNumber g := hN.symm

/-- Every edge incident to a degree-three Cartan support vertex has both
directed Cartan entries equal to `-1`. -/
public lemma cartanSupport_degree_three_edge_entries_eq_neg_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c = 3)
    (hadj : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c a) :
    A c a = -1 ∧ A a c = -1 := by
  have hprod := cartanSupport_degree_three_edgeProduct_eq_one
    A d hdiag hrank hpos c a hdeg hadj
  rcases hrank c a hadj.ne with h0 | h11 | h12 | h21 | h13 | h31
  · norm_num [h0.1, h0.2] at hprod
  · exact h11
  · norm_num [h12.1, h12.2] at hprod
  · norm_num [h21.1, h21.2] at hprod
  · norm_num [h13.1, h13.2] at hprod
  · norm_num [h31.1, h31.2] at hprod

/-- Deleting a support leaf preserves all four intrinsic matrix hypotheses
used by the finite Cartan classifier.  The result is an ordinary conjunction,
not a proof-bearing data structure. -/
public lemma cartanSubmatrix_compl_leaf_hypotheses
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nontrivial κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (v : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1) :
    (∀ i : {i : κ // i ≠ v},
      A.submatrix Subtype.val Subtype.val i i = 2) ∧
    (∀ i j : {i : κ // i ≠ v}, i ≠ j →
      (A.submatrix Subtype.val Subtype.val i j = 0 ∧
        A.submatrix Subtype.val Subtype.val j i = 0) ∨
      (A.submatrix Subtype.val Subtype.val i j = -1 ∧
        A.submatrix Subtype.val Subtype.val j i = -1) ∨
      (A.submatrix Subtype.val Subtype.val i j = -1 ∧
        A.submatrix Subtype.val Subtype.val j i = -2) ∨
      (A.submatrix Subtype.val Subtype.val i j = -2 ∧
        A.submatrix Subtype.val Subtype.val j i = -1) ∨
      (A.submatrix Subtype.val Subtype.val i j = -1 ∧
        A.submatrix Subtype.val Subtype.val j i = -3) ∨
      (A.submatrix Subtype.val Subtype.val i j = -3 ∧
        A.submatrix Subtype.val Subtype.val j i = -1)) ∧
    (∀ (p : {i : κ // i ≠ v} → Prop) {i j : {i : κ // i ≠ v}}, p i →
      (∀ i j, p i → A.submatrix Subtype.val Subtype.val j i ≠ 0 → p j) → p j) ∧
    (Matrix.diagonal (d ∘ (Subtype.val : {i : κ // i ≠ v} → κ)) *
      A.submatrix (Subtype.val : {i : κ // i ≠ v} → κ)
        (Subtype.val : {i : κ // i ≠ v} → κ)).PosDef := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact hdiag i
  · intro i j hij
    exact hrank i j (fun h => hij (Subtype.ext h))
  · exact cartanSubmatrix_compl_leaf_closureInduction
      A d hdiag hrank hconn hpos v hdeg
  · simpa using diagonal_mul_submatrix_posDef A d
      (Function.Embedding.subtype fun i => i ≠ v) hpos

open SimpleGraph

/-- The finite Cartan support tree either has a degree-three branch vertex or
admits an exact path-graph numbering. -/
public lemma cartanSupport_exists_degree_three_or_pathGraph_numbering
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    (∃ c, (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c = 3) ∨
      ∃ n : ℕ, ∃ e : Fin n ≃ κ,
        ∀ i j,
          (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
            (pathGraph n).Adj i j := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  by_cases hbranch : ∃ c, G.degree c = 3
  · exact Or.inl hbranch
  · right
    apply cartanSupport_pathGraph_numbering_of_degree_le_two
      A d hdiag hrank hconn hpos
    intro x
    have hle := cartanSupport_degree_le_three A d hdiag hrank hpos x
    have hne :
        (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree x ≠ 3 := by
      intro hx
      apply hbranch
      exact ⟨x, hx⟩
    omega

/-- Theorem 1.8.3(e): the inversions of a reduced word are exactly its
successive suffix transforms of the corresponding simple roots. -/
public theorem reducedWord_inversions_characterization
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support)
    (hmin : l.length = b.wordLength (b.wordProd l)) (i : ι) :
    (b.IsPos i ∧ ¬ b.IsPos (P.weylGroupToPerm (b.wordProd l) i)) ↔
      ∃ p : List b.support, ∃ j : b.support, ∃ q : List b.support,
        l = p ++ j :: q ∧ i = P.weylGroupToPerm (b.wordProd q)⁻¹ j := by
  induction l using List.reverseRecOn generalizing i with
  | nil => simp
  | append_singleton p j ih =>
      have hp_le : b.wordLength (b.wordProd p) ≤ p.length :=
        b.wordLength_le _ p rfl
      have hall_le := b.wordLength_mul_simpleReflection_le (b.wordProd p) j
      have hprod : b.wordProd (p ++ [j]) = b.wordProd p * b.simpleReflection j := by
        simp
      rw [← hprod, ← hmin] at hall_le
      have hpmin : p.length = b.wordLength (b.wordProd p) := by
        simp only [List.length_append, List.length_singleton] at hall_le
        omega
      have hpos : b.IsPos (P.weylGroupToPerm (b.wordProd p) j) := by
        by_contra hneg
        have hdec := b.wordLength_mul_simpleReflection_of_not_isPos
          (b.wordProd p) j hneg
        rw [← hprod, ← hmin, ← hpmin] at hdec
        simp at hdec
        omega
      rw [hprod, b.inversion_iff_mul_simpleReflection_of_isPos _ j hpos i]
      constructor
      · rintro (rfl | ⟨k, hkpos, hkneg, rfl⟩)
        · exact ⟨p, j, [], by simp, by simp⟩
        · have hk := (ih hpmin k).mp ⟨hkpos, hkneg⟩
          rcases hk with ⟨a, x, q, hp, hk⟩
          refine ⟨a, x, q ++ [j], ?_, ?_⟩
          · rw [hp, List.append_assoc]
            rfl
          · rw [hk]
            simp [RootPairing.Base.wordProd_append,
              RootPairing.Base.simpleReflection, RootPairing.weylGroup.ofIdx]
      · rintro ⟨a, x, q, hl, hi⟩
        by_cases hq : q = []
        · subst q
          simp at hl hi
          rcases hl with ⟨rfl, rfl⟩
          exact Or.inl hi
        · let q' : List b.support := q.dropLast
          let y : b.support := q.getLast hq
          have hq_decomp : q' ++ [y] = q := List.dropLast_append_getLast hq
          rw [← hq_decomp] at hl
          have hl' : p ++ [j] = (a ++ x :: q') ++ [y] := by
            simpa [List.append_assoc] using hl
          have hjy : y = j := by
            have hlast := congrArg List.getLast? hl'
            rw [List.getLast?_append_of_ne_nil p (by simp),
              List.getLast?_append_of_ne_nil (a ++ x :: q') (by simp)] at hlast
            simpa using hlast.symm
          rw [hjy] at hl' hq_decomp
          have hp_eq : p = a ++ x :: q' := by
            exact List.append_cancel_right
              (show p ++ [j] = (a ++ x :: q') ++ [j] from hl')
          right
          refine ⟨P.weylGroupToPerm (b.wordProd q')⁻¹ x, ?_, ?_, ?_⟩
          · have hInv : b.IsPos (P.weylGroupToPerm (b.wordProd q')⁻¹ x) ∧
                ¬ b.IsPos (P.weylGroupToPerm (b.wordProd p)
                  (P.weylGroupToPerm (b.wordProd q')⁻¹ x)) := by
              rw [ih hpmin]
              exact ⟨a, x, q', hp_eq, rfl⟩
            exact hInv.1
          · have hInv : b.IsPos (P.weylGroupToPerm (b.wordProd q')⁻¹ x) ∧
                ¬ b.IsPos (P.weylGroupToPerm (b.wordProd p)
                  (P.weylGroupToPerm (b.wordProd q')⁻¹ x)) := by
              rw [ih hpmin]
              exact ⟨a, x, q', hp_eq, rfl⟩
            exact hInv.2
          · rw [hi, ← hq_decomp]
            simp [RootPairing.Base.wordProd_append,
              RootPairing.Base.simpleReflection, RootPairing.weylGroup.ofIdx]

open scoped SimpleGraph

/-!
This owner assembles the affine-`D` contradiction after the finite-tree
decomposition has been made explicit.  The row and zero-entry hypotheses are
ordinary theorem premises, rather than fields of a conclusion-bearing data
structure.  They are exactly the local conditions consumed by
`affineD_mulVec_eq_zero_of_row_entries`.
-/
public lemma not_cartan_support_two_degree_three_vertices_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c₁ c₂ : κ) (hneq : c₁ ≠ c₂)
    (hdeg₁ : (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).degree c₁ = 3)
    (hdeg₂ : (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).degree c₂ = 3)
    (hrows :
      ∀ {p : (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Walk c₁ c₂}
        (hp : p.IsPath)
        {a₁ a₂ b₁ b₂ : κ},
        a₁ ≠ a₂ → b₁ ≠ b₂ →
        a₁ ≠ b₁ → a₁ ≠ b₂ → a₂ ≠ b₁ → a₂ ≠ b₂ →
        (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c₁ a₁ →
        (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c₁ a₂ →
        (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c₂ b₁ →
        (SimpleGraph.fromRel (fun i j => A i j ≠ 0)).Adj c₂ b₂ →
        a₁ ∉ p.support → a₂ ∉ p.support →
        b₁ ∉ p.support → b₂ ∉ p.support →
        (e : Fin (p.length + 5) ↪ κ) →
        (∀ i : Fin (p.length + 1),
          e (Fin.castAdd 4 i) = p.getVert i) →
        e (Fin.natAdd (p.length + 1) (0 : Fin 4)) = a₁ →
        e (Fin.natAdd (p.length + 1) (1 : Fin 4)) = a₂ →
        e (Fin.natAdd (p.length + 1) (2 : Fin 4)) = b₁ →
        e (Fin.natAdd (p.length + 1) (3 : Fin 4)) = b₂ →
        A (e 0) (e 1) = -1 ∧
        A (e ⟨p.length, by omega⟩) (e ⟨p.length - 1, by omega⟩) = -1 ∧
        A (e 0) (e ⟨p.length + 1, by omega⟩) = -1 ∧
        A (e 0) (e ⟨p.length + 2, by omega⟩) = -1 ∧
        A (e ⟨p.length + 1, by omega⟩) (e 0) = -1 ∧
        A (e ⟨p.length + 2, by omega⟩) (e 0) = -1 ∧
        A (e ⟨p.length, by omega⟩) (e ⟨p.length + 3, by omega⟩) = -1 ∧
        A (e ⟨p.length, by omega⟩) (e ⟨p.length + 4, by omega⟩) = -1 ∧
        A (e ⟨p.length + 3, by omega⟩) (e ⟨p.length, by omega⟩) = -1 ∧
        A (e ⟨p.length + 4, by omega⟩) (e ⟨p.length, by omega⟩) = -1 ∧
        (∀ i : Fin (p.length + 5), ∀ hi : i.val < p.length,
          A (e i) (e ⟨i.val + 1, by omega⟩) = -1) ∧
        (∀ i : Fin (p.length + 5), ∀ hi : i.val < p.length,
          A (e ⟨i.val + 1, by omega⟩) (e i) = -1) ∧
        (∀ j, j ≠ 0 → j ≠ 1 →
          j ≠ ⟨p.length + 1, by omega⟩ →
          j ≠ ⟨p.length + 2, by omega⟩ →
          A (e 0) (e j) = 0) ∧
        (∀ j, j ≠ ⟨p.length, by omega⟩ →
          j ≠ ⟨p.length - 1, by omega⟩ →
          j ≠ ⟨p.length + 3, by omega⟩ →
          j ≠ ⟨p.length + 4, by omega⟩ →
          A (e ⟨p.length, by omega⟩) (e j) = 0) ∧
        (∀ i j, 0 < i.val → i.val < p.length → i ≠ j →
          j.val + 1 ≠ i.val → i.val + 1 ≠ j.val →
          A (e i) (e j) = 0) ∧
        (∀ j, j ≠ ⟨p.length + 1, by omega⟩ → j ≠ 0 →
          A (e ⟨p.length + 1, by omega⟩) (e j) = 0) ∧
        (∀ j, j ≠ ⟨p.length + 2, by omega⟩ → j ≠ 0 →
          A (e ⟨p.length + 2, by omega⟩) (e j) = 0) ∧
        (∀ j, j ≠ ⟨p.length + 3, by omega⟩ →
          j ≠ ⟨p.length, by omega⟩ →
          A (e ⟨p.length + 3, by omega⟩) (e j) = 0) ∧
        (∀ j, j ≠ ⟨p.length + 4, by omega⟩ →
          j ≠ ⟨p.length, by omega⟩ →
          A (e ⟨p.length + 4, by omega⟩) (e j) = 0)) : False := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel (fun i j => A i j ≠ 0)
  have htree : G.IsTree := by
    exact cartanSupport_isTree A d hdiag hrank hconn hpos
  obtain ⟨p, hp, a₁, a₂, b₁, b₂, ha12, hb12, hab₁, hab₂, hac₁, hac₂,
      ha₁adj, ha₂adj, hb₁adj, hb₂adj, ha₁off, ha₂off, hb₁off, hb₂off⟩ :=
    simpleGraph_two_degree_three_vertices_offPath_neighbors G htree c₁ c₂
      hneq hdeg₁ hdeg₂
  obtain ⟨e, hepath, hea₁, hea₂, heb₁, heb₂⟩ :=
    central_path_plus_four_offpath_embedding hp ha12 hb12 hab₁ hab₂ hac₁ hac₂
      ha₁off ha₂off hb₁off hb₂off
  have hpNil : ¬p.Nil := by
    intro h
    exact hneq (hp.nil_iff_eq.mp h)
  have hm : 0 < p.length := by
    exact Nat.pos_of_ne_zero (by
      intro hz
      apply hpNil
      exact SimpleGraph.Walk.length_eq_zero_iff.mp hz)
  let e5 : Fin (p.length + 5) ↪ κ := by
    simpa [Nat.add_assoc] using e
  have hepath5 : ∀ i : Fin (p.length + 1),
      e5 (Fin.castAdd 4 i) = p.getVert i := by
    intro i
    simpa [e5, Nat.add_assoc] using hepath i
  have hea₁5 : e5 (Fin.natAdd (p.length + 1) (0 : Fin 4)) = a₁ := by
    simpa [e5, Nat.add_assoc] using hea₁
  have hea₂5 : e5 (Fin.natAdd (p.length + 1) (1 : Fin 4)) = a₂ := by
    simpa [e5, Nat.add_assoc] using hea₂
  have heb₁5 : e5 (Fin.natAdd (p.length + 1) (2 : Fin 4)) = b₁ := by
    simpa [e5, Nat.add_assoc] using heb₁
  have heb₂5 : e5 (Fin.natAdd (p.length + 1) (3 : Fin 4)) = b₂ := by
    simpa [e5, Nat.add_assoc] using heb₂
  rcases hrows hp ha12 hb12 hab₁ hab₂ hac₁ hac₂ ha₁adj ha₂adj hb₁adj hb₂adj
      ha₁off ha₂off hb₁off hb₂off e5 hepath5 hea₁5 hea₂5 heb₁5 heb₂5 with
    ⟨hleft₁, hright₁, ha₁, ha₂, hā₁, hā₂, hb₁, hb₂, hback₁, hback₂,
      hpath₁, hpath₂, hzero₀, hzeroₘ, hzeroPath, hzeroA₁, hzeroA₂,
      hzeroB₁, hzeroB₂⟩
  have hleafA₁ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₁ a₁ hdeg₁ ha₁adj
  have hleafA₂ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₁ a₂ hdeg₁ ha₂adj
  have hleafB₁ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₂ b₁ hdeg₂ hb₁adj
  have hleafB₂ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₂ b₂ hdeg₂ hb₂adj
  have he0 : e5 0 = c₁ := by
    have h := hepath5 (0 : Fin (p.length + 1))
    simpa [Fin.castAdd] using h
  have hem : e5 ⟨p.length, by omega⟩ = c₂ := by
    have h := hepath5 (⟨p.length, by omega⟩ : Fin (p.length + 1))
    simpa using h
  have ha₁deg : A (e5 0)
      (e5 (Fin.natAdd (p.length + 1) (0 : Fin 4))) = -1 := by
    rw [he0, hea₁5]
    exact hleafA₁.1
  have ha₂deg : A (e5 0)
      (e5 (Fin.natAdd (p.length + 1) (1 : Fin 4))) = -1 := by
    rw [he0, hea₂5]
    exact hleafA₂.1
  have hā₁deg : A (e5 (Fin.natAdd (p.length + 1) (0 : Fin 4))) (e5 0) = -1 := by
    rw [hea₁5, he0]
    exact hleafA₁.2
  have hā₂deg : A (e5 (Fin.natAdd (p.length + 1) (1 : Fin 4))) (e5 0) = -1 := by
    rw [hea₂5, he0]
    exact hleafA₂.2
  have hb₁deg : A (e5 ⟨p.length, by omega⟩)
      (e5 (Fin.natAdd (p.length + 1) (2 : Fin 4))) = -1 := by
    rw [hem, heb₁5]
    exact hleafB₁.1
  have hb₂deg : A (e5 ⟨p.length, by omega⟩)
      (e5 (Fin.natAdd (p.length + 1) (3 : Fin 4))) = -1 := by
    rw [hem, heb₂5]
    exact hleafB₂.1
  have hback₁deg : A (e5 (Fin.natAdd (p.length + 1) (2 : Fin 4)))
      (e5 ⟨p.length, by omega⟩) = -1 := by
    rw [heb₁5, hem]
    exact hleafB₁.2
  have hback₂deg : A (e5 (Fin.natAdd (p.length + 1) (3 : Fin 4)))
      (e5 ⟨p.length, by omega⟩) = -1 := by
    rw [heb₂5, hem]
    exact hleafB₂.2
  have hdiag5 : ∀ i, A (e5 i) (e5 i) = 2 := by
    intro i
    exact hdiag _
  exact not_cartan_two_degree_three_vertices_of_affineD_row_entries
    A d hpos hm e5 hdiag5 hleft₁ hright₁ ha₁deg ha₂deg hā₁deg hā₂deg
    hb₁deg hb₂deg hback₁deg hback₂deg
    hpath₁ hpath₂ hzero₀ hzeroₘ hzeroPath hzeroA₁ hzeroA₂
    hzeroB₁ hzeroB₂

open SimpleGraph

set_option maxHeartbeats 800000 in
/-- A first heavy edge on one arm of an exact three-arm Cartan support
contradicts positive definiteness.  All arm and entry facts are ordinary
hypotheses. -/
public lemma not_cartan_three_arm_first_heavy_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c : κ) {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → κ) (f1 : Fin (n1 + 1) → κ)
    (f2 : Fin (n2 + 1) → κ)
    (hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f2 j) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f0 l) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f1 l) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f2 j) (f2 l) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f2 l))
    (hdeg : (SimpleGraph.fromRel fun x y => A x y ≠ 0).degree c = 3)
    {m : ℕ} (hm : 0 < m) (hmn : m ≤ n0)
    (hsimple : ∀ r : Fin (n0 + 1), 0 < r.val → r.val < m →
      A (f0 ⟨r.val - 1, by omega⟩) (f0 r) = -1 ∧
      A (f0 r) (f0 ⟨r.val - 1, by omega⟩) = -1)
    (hheavy : 2 ≤
      A (f0 ⟨m - 1, by omega⟩) (f0 ⟨m, by omega⟩) *
      A (f0 ⟨m, by omega⟩) (f0 ⟨m - 1, by omega⟩)) : False := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  have hc0adj : G.Adj c (f0 0) := (hcenter0 0).mpr rfl
  have hc1adj : G.Adj c (f1 0) := (hcenter1 0).mpr rfl
  have hc2adj : G.Adj c (f2 0) := (hcenter2 0).mpr rfl
  have hc0simple := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c (f0 0) hdeg hc0adj
  have hc1simple := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c (f1 0) hdeg hc1adj
  have hc2simple := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c (f2 0) hdeg hc2adj
  obtain ⟨e, he0, he1, he2, hearm, hsupport⟩ :=
    simpleGraph_three_arm_prefix_branch_embedding G c f0 f1 f2
      hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12 hcenter0 hcenter1 hcenter2
      hpath0 hpath1 hpath2 hcross01 hcross02 hcross12 hm hmn
  let is : Fin (m + 4) := ⟨m + 2, by omega⟩
  let ie : Fin (m + 4) := ⟨m + 3, by omega⟩
  let u : ℤ := A (e is) (e ie)
  let v : ℤ := A (e ie) (e is)
  have heStart : e is = f0 ⟨m - 1, by omega⟩ := by
    have h := hearm (⟨m - 1, by omega⟩ : Fin (m + 1))
    calc
      e is = e ⟨(m - 1) + 3, by omega⟩ := by
        apply congrArg e
        apply Fin.ext
        simp [is]
        omega
      _ = f0 ⟨m - 1, by omega⟩ := h
  have heEnd : e ie = f0 ⟨m, by omega⟩ := by
    have h := hearm (⟨m, by omega⟩ : Fin (m + 1))
    calc
      e ie = e ⟨m + 3, by omega⟩ := by
        apply congrArg e
        apply Fin.ext
        rfl
      _ = f0 ⟨m, by omega⟩ := h
  have heRoot : e ⟨3, by omega⟩ = f0 0 := by
    have h := hearm (0 : Fin (m + 1))
    calc
      e ⟨3, by omega⟩ = e ⟨(0 : Fin (m + 1)).val + 3, by omega⟩ := by
        apply congrArg e
        apply Fin.ext
        rfl
      _ = f0 (Fin.castLE (Nat.succ_le_succ hmn) 0) := h
      _ = f0 0 := by simp
  have huvy : 2 ≤ u * v := by
    simpa [u, v, heStart, heEnd] using hheavy
  let i0 : Fin (m + 4) := ⟨0, by omega⟩
  let i1 : Fin (m + 4) := ⟨1, by omega⟩
  let i2 : Fin (m + 4) := ⟨2, by omega⟩
  let i3 : Fin (m + 4) := ⟨3, by omega⟩
  have he0' : e i0 = f1 0 := by
    rw [show i0 = 0 by apply Fin.ext; rfl]
    exact he0
  have he1' : e i1 = f2 0 := by
    rw [show i1 = 1 by apply Fin.ext; rfl]
    exact he1
  have he2' : e i2 = c := by
    rw [show i2 = 2 by apply Fin.ext; rfl]
    exact he2
  have heRoot' : e i3 = f0 0 := by
    rw [show i3 = ⟨3, by omega⟩ by apply Fin.ext; rfl]
    exact heRoot
  apply not_cartan_branch_single_heavy_of_support_numbering
    A d hdiag hpos hm e u v hsupport
  · intro i j hleaf
    rcases hleaf with h | h | h | h
    · have hi : i = i0 := Fin.ext h.1
      have hj : j = i2 := Fin.ext h.2
      rw [hi, hj, he0', he2']
      exact hc1simple.2
    · have hi : i = i2 := Fin.ext h.1
      have hj : j = i0 := Fin.ext h.2
      rw [hi, hj, he2', he0']
      exact hc1simple.1
    · have hi : i = i1 := Fin.ext h.1
      have hj : j = i2 := Fin.ext h.2
      rw [hi, hj, he1', he2']
      exact hc2simple.2
    · have hi : i = i2 := Fin.ext h.1
      have hj : j = i1 := Fin.ext h.2
      rw [hi, hj, he2', he1']
      exact hc2simple.1
  · intro i j hi hij hjm
    by_cases hi2 : i.val = 2
    · have hii : i = i2 := Fin.ext hi2
      have hjj : j = i3 := by
        apply Fin.ext
        simp [i3]
        omega
      rw [hii, hjj, he2', heRoot']
      exact hc0simple.1
    · let ri : Fin (m + 1) := ⟨i.val - 3, by omega⟩
      let rj : Fin (m + 1) := ⟨j.val - 3, by omega⟩
      have hei : e i = f0 (Fin.castLE (Nat.succ_le_succ hmn) ri) := by
        have h := hearm ri
        rw [← h]
        apply congrArg e
        apply Fin.ext
        simp [ri]
        omega
      have hej : e j = f0 (Fin.castLE (Nat.succ_le_succ hmn) rj) := by
        have h := hearm rj
        rw [← h]
        apply congrArg e
        apply Fin.ext
        simp [rj]
        omega
      let r : Fin (n0 + 1) := Fin.castLE (Nat.succ_le_succ hmn) rj
      have hrs := hsimple r (by simp [r, rj]; omega) (by simp [r, rj]; omega)
      rw [hei, hej]
      change A (f0 (Fin.castLE (Nat.succ_le_succ hmn) ri)) (f0 r) = -1
      have hpred : Fin.castLE (Nat.succ_le_succ hmn) ri =
          (⟨r.val - 1, by omega⟩ : Fin (n0 + 1)) := by
        apply Fin.ext
        simp [ri, rj, r]
        omega
      rw [hpred]
      exact hrs.1
  · intro i j hj hij him
    by_cases hj2 : j.val = 2
    · have hjj : j = i2 := Fin.ext hj2
      have hii : i = i3 := by
        apply Fin.ext
        simp [i3]
        omega
      rw [hii, hjj, heRoot', he2']
      exact hc0simple.2
    · let ri : Fin (m + 1) := ⟨i.val - 3, by omega⟩
      let rj : Fin (m + 1) := ⟨j.val - 3, by omega⟩
      have hei : e i = f0 (Fin.castLE (Nat.succ_le_succ hmn) ri) := by
        have h := hearm ri
        rw [← h]
        apply congrArg e
        apply Fin.ext
        simp [ri]
        omega
      have hej : e j = f0 (Fin.castLE (Nat.succ_le_succ hmn) rj) := by
        have h := hearm rj
        rw [← h]
        apply congrArg e
        apply Fin.ext
        simp [rj]
        omega
      let r : Fin (n0 + 1) := Fin.castLE (Nat.succ_le_succ hmn) ri
      have hrs := hsimple r (by simp [r, ri]; omega) (by simp [r, ri]; omega)
      rw [hei, hej]
      change A (f0 r) (f0 (Fin.castLE (Nat.succ_le_succ hmn) rj)) = -1
      have hpred : Fin.castLE (Nat.succ_le_succ hmn) rj =
          (⟨r.val - 1, by omega⟩ : Fin (n0 + 1)) := by
        apply Fin.ext
        simp [ri, rj, r]
        omega
      rw [hpred]
      exact hrs.2
  · intro i j hi hj
    have hii : i = is := Fin.ext (by simpa [is] using hi)
    have hjj : j = ie := Fin.ext (by simpa [ie] using hj)
    simp [hii, hjj, u]
  · intro i j hi hj
    have hii : i = ie := Fin.ext (by simpa [ie] using hi)
    have hjj : j = is := Fin.ext (by simpa [is] using hj)
    simp [hii, hjj, v]
  · exact huvy

/-- A finite Cartan classifier can be applied directly after deleting a
support leaf.  The recursive entry point is an ordinary higher-order theorem:
the classification result is supplied by `classify`, not stored in a
definition or structure. -/
public lemma finiteCartanClassifier_apply_compl_leaf
    {κ : Type u} [Fintype κ] [DecidableEq κ] [Nontrivial κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (v : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1)
    (C : ∀ {ι : Type u}, Matrix ι ι ℤ → Prop)
    (classify :
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
        (∀ i, M i i = 2) →
        (∀ i j, i ≠ j →
          (M i j = 0 ∧ M j i = 0) ∨
          (M i j = -1 ∧ M j i = -1) ∨
          (M i j = -1 ∧ M j i = -2) ∨
          (M i j = -2 ∧ M j i = -1) ∨
          (M i j = -1 ∧ M j i = -3) ∨
          (M i j = -3 ∧ M j i = -1)) →
        (∀ (p : ι → Prop) {i j : ι}, p i →
          (∀ i j, p i → M j i ≠ 0 → p j) → p j) →
        (∃ s : ι → ℤ, (∀ i, 0 < s i) ∧
          (Matrix.diagonal s * M).PosDef) →
        C M)
    : C (A.submatrix (Subtype.val : {i : κ // i ≠ v} → κ)
      (Subtype.val : {i : κ // i ≠ v} → κ)) := by
  apply classify
  · intro i
    exact hdiag i
  · intro i j hij
    exact hrank i j (fun h => hij (Subtype.ext h))
  · exact cartanSubmatrix_compl_leaf_closureInduction
      A d hdiag hrank hconn hpos v hdeg
  · have hdp : ∀ i, 0 < d i := by
      intro i
      have hi := hpos.diag_pos (i := i)
      simp [Matrix.diagonal_mul, hdiag] at hi
      omega
    refine ⟨fun i => d i.1, ?_, ?_⟩
    · intro i
      exact hdp i.1
    · exact diagonal_mul_submatrix_posDef A d
        (Function.Embedding.subtype fun i => i ≠ v) hpos

open Set
open Submodule (span)

section

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

/-- The standard parabolic subgroup generated by the simple reflections
indexed by `J`. -/
@[expose] public noncomputable def _root_.RootPairing.Base.parabolicSubgroup
    (J : Set b.support) : Subgroup P.weylGroup :=
  Subgroup.closure (b.simpleReflection '' J)

public theorem _root_.RootPairing.Base.wordProd_mem_parabolicSubgroup (J : Set b.support)
    (l : List b.support) (hl : ∀ j ∈ l, j ∈ J) :
    b.wordProd l ∈ b.parabolicSubgroup J := by
  induction l with
  | nil => simp [RootPairing.Base.parabolicSubgroup]
  | cons j l ih =>
      rw [b.wordProd_cons]
      apply Subgroup.mul_mem
      · exact Subgroup.subset_closure ⟨j, hl j (by simp), rfl⟩
      · exact ih fun k hk => hl k (by simp [hk])

public theorem _root_.RootPairing.Base.mem_parabolicSubgroup_iff_exists_word
    (J : Set b.support)
    (g : P.weylGroup) :
    g ∈ b.parabolicSubgroup J ↔
      ∃ l : List b.support, (∀ j ∈ l, j ∈ J) ∧ b.wordProd l = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction'' with
    | one => exact ⟨[], by simp⟩
    | mem x hx =>
        rcases hx with ⟨j, hj, rfl⟩
        exact ⟨[j], by simp [hj]⟩
    | inv_mem x hx =>
        rcases hx with ⟨j, hj, rfl⟩
        exact ⟨[j], by simp [hj]⟩
    | mul x y hx hy ihx ihy =>
        rcases ihx with ⟨l, hlJ, rfl⟩
        rcases ihy with ⟨m, hmJ, rfl⟩
        refine ⟨l ++ m, ?_, by simp⟩
        intro j hj
        rw [List.mem_append] at hj
        exact hj.elim (hlJ j) (hmJ j)
  · rintro ⟨l, hl, rfl⟩
    exact b.wordProd_mem_parabolicSubgroup J l hl

public theorem _root_.RootPairing.Base.parabolicSubgroup_union (J K : Set b.support) :
    b.parabolicSubgroup (J ∪ K) =
      b.parabolicSubgroup J ⊔ b.parabolicSubgroup K := by
  simp only [RootPairing.Base.parabolicSubgroup, image_union, Subgroup.closure_union]

end

variable {ι M N : Type*} [Fintype ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem] (b : P.Base)

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.coordinate_simpleReflection_of_ne
    (j k : b.support) (hjk : k ≠ j) (x : M) :
    b.toWeightBasis.repr (P.reflection j x) k = b.toWeightBasis.repr x k := by
  rw [P.reflection_apply, map_sub, map_smul, b.toWeightBasis_repr_root]
  simp [hjk]

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.coordinate_wordProd_of_not_mem
    (J : Set b.support) (l : List b.support) (hl : ∀ j ∈ l, j ∈ J)
    (k : b.support) (hk : k ∉ J) (x : M) :
    b.toWeightBasis.repr (b.wordProd l • x) k = b.toWeightBasis.repr x k := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [b.wordProd_cons, mul_smul]
      change b.toWeightBasis.repr (P.reflection j (b.wordProd l • x)) k = _
      rw [b.coordinate_simpleReflection_of_ne j k
        (fun h => hk (h ▸ hl j (by simp))) _]
      exact ih (fun a ha => hl a (by simp [ha]))

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.mem_span_root_image_iff_repr_support_subset
    (J : Set b.support) (x : M) :
    x ∈ span ℝ (P.root '' ((fun j : b.support => (j : ι)) '' J)) ↔
      ((b.toWeightBasis.repr x).support : Set b.support) ⊆ J := by
  rw [show P.root '' ((fun j : b.support => (j : ι)) '' J) =
      b.toWeightBasis '' J by
    ext y
    simp [b.toWeightBasis_apply]]
  exact b.toWeightBasis.mem_span_image

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.isPos_repr_nonneg
    (i : ι) (hi : b.IsPos i) (j : b.support) :
    0 ≤ b.toWeightBasis.repr (P.root i) j := by
  rw [b.isPos_iff_root_mem_closure] at hi
  have hnonneg : ∀ x : M, x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)) →
      ∀ j : b.support, 0 ≤ b.toWeightBasis.repr x j := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
        rcases hx with ⟨k, hk, rfl⟩
        intro j
        let k' : b.support := ⟨k, hk⟩
        change 0 ≤ b.toWeightBasis.repr (P.root k') j
        rw [b.toWeightBasis_repr_root]
        by_cases hkj : k' = j <;> simp [hkj]
    | zero => simp
    | add x y hx hy ihx ihy =>
        intro j
        rw [map_add]
        exact add_nonneg (ihx j) (ihy j)
  exact hnonneg _ hi j

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.closure_repr_nonneg
    (x : M) (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)))
    (j : b.support) :
    0 ≤ b.toWeightBasis.repr x j := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨k, hk, rfl⟩
      let k' : b.support := ⟨k, hk⟩
      change 0 ≤ b.toWeightBasis.repr (P.root k') j
      rw [b.toWeightBasis_repr_root]
      by_cases hkj : k' = j <;> simp [hkj]
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact add_nonneg ihx ihy

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.closure_mem_span_root_image_of_mem_span
    (J : Set b.support) (x : M)
    (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)))
    (hspan : x ∈ span ℝ
      (P.root '' ((fun j : b.support => (j : ι)) '' J))) :
    x ∈ AddSubmonoid.closure
      (P.root '' ((fun j : b.support => (j : ι)) '' J)) := by
  let q : Submodule ℝ M := span ℝ
    (P.root '' ((fun j : b.support => (j : ι)) '' J))
  have hcoord (y : M) (hy : y ∈ q) :
      ((b.toWeightBasis.repr y).support : Set b.support) ⊆ J := by
    exact (b.mem_span_root_image_iff_repr_support_subset J y).1 hy
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
      rcases hy with ⟨k, hk, rfl⟩
      let k' : b.support := ⟨k, hk⟩
      have hkJ : k' ∈ J := by
        have hs := hcoord (P.root k) hspan
        exact hs (by
          rw [show P.root k = P.root k' by rfl, b.toWeightBasis_repr_root]
          simp)
      exact AddSubmonoid.subset_closure ⟨k, ⟨k', hkJ, rfl⟩, rfl⟩
  | zero => simp
  | add y z hy hz ihy ihz =>
      have hyq : y ∈ q := by
        apply (b.mem_span_root_image_iff_repr_support_subset J y).2
        intro j hj
        by_contra hjJ
        have hsum := hcoord (y + z) (by simpa using hspan)
        have hzero : b.toWeightBasis.repr (y + z) j = 0 := by
          by_contra hne
          exact hjJ (hsum (Finsupp.mem_support_iff.mpr hne))
        rw [map_add] at hzero
        simp only [Finsupp.add_apply] at hzero
        have hyn := b.closure_repr_nonneg y hy j
        have hzn := b.closure_repr_nonneg z hz j
        have : b.toWeightBasis.repr y j = 0 := by linarith
        exact (Finsupp.mem_support_iff.mp hj) this
      have hzq : z ∈ q := by
        apply (b.mem_span_root_image_iff_repr_support_subset J z).2
        intro j hj
        by_contra hjJ
        have hsum := hcoord (y + z) (by simpa using hspan)
        have hzero : b.toWeightBasis.repr (y + z) j = 0 := by
          by_contra hne
          exact hjJ (hsum (Finsupp.mem_support_iff.mpr hne))
        rw [map_add] at hzero
        simp only [Finsupp.add_apply] at hzero
        have hyn := b.closure_repr_nonneg y hy j
        have hzn := b.closure_repr_nonneg z hz j
        have : b.toWeightBasis.repr z j = 0 := by linarith
        exact (Finsupp.mem_support_iff.mp hj) this
      exact AddSubmonoid.add_mem _ (ihy hyq) (ihz hzq)

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.isNotPos_repr_nonpos
    (i : ι) (hi : ¬ b.IsPos i) (j : b.support) :
    b.toWeightBasis.repr (P.root i) j ≤ 0 := by
  letI := P.indexNeg
  have hpos : b.IsPos (-i) := (RootPairing.Base.IsPos.neg_iff_not b i).2 hi
  have hn := b.isPos_repr_nonneg (-i) hpos j
  have hroot : P.root (-i) = -P.root i := by simp
  rw [hroot, map_neg] at hn
  exact neg_nonneg.mp hn

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.exists_pos_external_coordinate
    (J : Set b.support) (i : ι) (hi : b.IsPos i)
    (hspan : P.root i ∉ span ℝ
      (P.root '' ((fun j : b.support => (j : ι)) '' J))) :
    ∃ k : b.support, k ∉ J ∧ 0 < b.toWeightBasis.repr (P.root i) k := by
  have hs : ¬ ((b.toWeightBasis.repr (P.root i)).support : Set b.support) ⊆ J := by
    intro hs
    apply hspan
    exact (b.mem_span_root_image_iff_repr_support_subset J (P.root i)).2 hs
  obtain ⟨k, hk, hkJ⟩ := Set.not_subset.mp hs
  have hnonneg := b.isPos_repr_nonneg i hi k
  exact ⟨k, hkJ, lt_of_le_of_ne hnonneg (Ne.symm (by simpa using hk))⟩

omit [Fintype ι] in
public lemma _root_.RootPairing.Base.wordProd_root_isPos_of_external
    (J : Set b.support) (l : List b.support) (hl : ∀ j ∈ l, j ∈ J)
    (i : ι) (hi : b.IsPos i)
    (hspan : P.root i ∉ span ℝ
      (P.root '' ((fun j : b.support => (j : ι)) '' J))) :
    b.IsPos (P.weylGroupToPerm (b.wordProd l) i) := by
  letI := P.indexNeg
  obtain ⟨k, hkJ, hkpos⟩ := b.exists_pos_external_coordinate J i hi hspan
  by_contra hnot
  have hneg := b.isNotPos_repr_nonpos _ hnot k
  rw [← b.coordinate_wordProd_of_not_mem J l hl k hkJ (P.root i)] at hkpos
  rw [← P.weylGroup_apply_root] at hneg
  linarith

variable {ι M N : Type*} [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

public theorem _root_.RootPairing.Base.minimal_word_mem_parabolic_iff
    (b : P.Base) (J : Set b.support) (g : P.weylGroup)
    (hg : g ∈ b.parabolicSubgroup J)
    (l : List b.support)
    (hmin : l.length = b.wordLength g)
    (hl : b.wordProd l = g) :
    ∀ j ∈ l, j ∈ J := by
  letI := P.indexNeg
  induction l using List.reverseRecOn generalizing g with
  | nil => simp
  | append_singleton p j ih =>
      have hprod : b.wordProd (p ++ [j]) = b.wordProd p * b.simpleReflection j := by
        simp
      have hp_le : b.wordLength (b.wordProd p) ≤ p.length :=
        b.wordLength_le _ p rfl
      have hall_le := b.wordLength_mul_simpleReflection_le (b.wordProd p) j
      have hprodg : b.wordProd p * b.simpleReflection j = g := hprod.symm.trans hl
      rw [hprodg, ← hmin] at hall_le
      have hpmin : p.length = b.wordLength (b.wordProd p) := by
        simp only [List.length_append, List.length_singleton] at hall_le
        omega
      have hjpos : b.IsPos (P.weylGroupToPerm (b.wordProd p) j) := by
        by_contra hneg
        have hdec := b.wordLength_mul_simpleReflection_of_not_isPos
          (b.wordProd p) j hneg
        rw [hprodg, ← hmin, ← hpmin] at hdec
        simp at hdec
        omega
      have hjneg : ¬ b.IsPos (P.weylGroupToPerm g j) := by
        rw [← hprodg]
        change ¬ b.IsPos (P.weylGroupToPerm (b.wordProd p) (-j))
        rw [P.weylGroupToPerm_neg, RootPairing.Base.IsPos.neg_iff_not b]
        exact not_not_intro hjpos
      have hjJ : j ∈ J := by
        by_contra hjnot
        rcases (b.mem_parabolicSubgroup_iff_exists_word J g).1 hg with
          ⟨m, hmJ, hmprod⟩
        have hspan : P.root (j : ι) ∉ span ℝ
            (P.root '' ((fun k : b.support => (k : ι)) '' J)) := by
          intro hspan
          have hcoord := (b.mem_span_root_image_iff_repr_support_subset J
            (P.root (j : ι))).1 hspan
          have hself : j ∈ (b.toWeightBasis.repr (P.root (j : ι))).support := by
            simp [b.toWeightBasis_repr_root]
          exact hjnot (hcoord hself)
        have hjpres := b.wordProd_root_isPos_of_external J m hmJ
          (j : ι) (b.isPos_of_mem_support j.property) hspan
        rw [hmprod] at hjpres
        exact hjneg hjpres
      refine fun k hk => ?_
      rw [List.mem_append] at hk
      rcases hk with hk | hk
      · have hgp : b.wordProd p ∈ b.parabolicSubgroup J := by
          have hmem := (b.parabolicSubgroup J).mul_mem hg
            (Subgroup.subset_closure ⟨j, hjJ, rfl⟩)
          rw [← hprodg] at hmem
          simpa [mul_assoc, b.simpleReflection_mul_self] using hmem
        exact ih (b.wordProd p) hgp hpmin rfl k hk
      · have hkj : k = j := by simpa using hk
        rw [hkj]
        exact hjJ

variable {ι M N : Type*} [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

public theorem _root_.RootPairing.Base.parabolicSubgroup_inter
    (b : P.Base) (J K : Set b.support) :
    b.parabolicSubgroup J ⊓ b.parabolicSubgroup K =
      b.parabolicSubgroup (J ∩ K) := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    have hJ : g ∈ b.parabolicSubgroup J := hg.1
    have hK : g ∈ b.parabolicSubgroup K := hg.2
    rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
    have hlJ := b.minimal_word_mem_parabolic_iff J g hJ l hlen hprod
    have hlK := b.minimal_word_mem_parabolic_iff K g hK l hlen hprod
    apply (b.mem_parabolicSubgroup_iff_exists_word (J ∩ K) g).2
    refine ⟨l, ?_, hprod⟩
    intro j hj
    exact ⟨hlJ j hj, hlK j hj⟩
  · intro hg
    have hsubJ : b.parabolicSubgroup (J ∩ K) ≤ b.parabolicSubgroup J := by
      intro x hx
      induction hx using Subgroup.closure_induction'' with
      | one => exact (b.parabolicSubgroup J).one_mem
      | mem x hx =>
          rcases hx with ⟨j, hj, rfl⟩
          exact Subgroup.subset_closure ⟨j, hj.1, rfl⟩
      | inv_mem x hx =>
          rcases hx with ⟨j, hj, rfl⟩
          rw [show (b.simpleReflection j)⁻¹ = b.simpleReflection j by
            exact inv_eq_of_mul_eq_one_left (b.simpleReflection_mul_self j)]
          exact Subgroup.subset_closure ⟨j, hj.1, rfl⟩
      | mul x y hx hy ihx ihy => exact (b.parabolicSubgroup J).mul_mem ihx ihy
    have hsubK : b.parabolicSubgroup (J ∩ K) ≤ b.parabolicSubgroup K := by
      intro x hx
      induction hx using Subgroup.closure_induction'' with
      | one => exact (b.parabolicSubgroup K).one_mem
      | mem x hx =>
          rcases hx with ⟨j, hj, rfl⟩
          exact Subgroup.subset_closure ⟨j, hj.2, rfl⟩
      | inv_mem x hx =>
          rcases hx with ⟨j, hj, rfl⟩
          rw [show (b.simpleReflection j)⁻¹ = b.simpleReflection j by
            exact inv_eq_of_mul_eq_one_left (b.simpleReflection_mul_self j)]
          exact Subgroup.subset_closure ⟨j, hj.2, rfl⟩
      | mul x y hx hy ihx ihy => exact (b.parabolicSubgroup K).mul_mem ihx ihy
    exact ⟨hsubJ hg, hsubK hg⟩

open Set

/-- The closed chamber determined by a base, using the canonical invariant form. -/
@[expose]
public noncomputable def _root_.RootPairing.Base.dominantChamber
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} (b : P.Base) : Set M :=
  {x | ∀ j : b.support, 0 ≤ P.RootForm x (P.root j)}

/-- A set is a fundamental domain for the Weyl action if every orbit meets it
and two points of it in the same orbit coincide. -/
@[expose]
public def _root_.RootPairing.Base.IsWeylFundamentalDomain
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (_b : P.Base) (C : Set M) : Prop :=
  (∀ x, ∃ g : P.weylGroup, g.1.weightMap x ∈ C) ∧
    ∀ x, x ∈ C → ∀ g : P.weylGroup, g.1.weightMap x ∈ C → g.1.weightMap x = x

public lemma _root_.RootPairing.two_mul_rootForm_apply_root
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (i : ι) (x : M) :
    2 * P.RootForm x (P.root i) =
      P.coroot' i x * P.RootForm (P.root i) (P.root i) := by
  have h := P.rootForm_reflection_reflection_apply i x (P.root i)
  rw [P.reflection_apply, P.reflection_apply_self] at h
  simp only [map_neg, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul] at h
  linarith

public lemma _root_.RootPairing.rootForm_root_self_pos
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsCrystallographic] (i : ι) :
    0 < P.RootForm (P.root i) (P.root i) := by
  obtain ⟨s, hs, hs'⟩ := (P.posRootForm ℝ).exists_pos_eq i
  simpa using hs' ▸ hs

public noncomputable def _root_.RootPairing.Base.chamberFunctional
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] (b : P.Base) : M →ₗ[ℝ] ℝ :=
  (Finsupp.lsum ℝ fun _ : b.support => LinearMap.id).comp
    b.toWeightBasis.repr.toLinearMap

@[simp]
public lemma _root_.RootPairing.Base.chamberFunctional_root
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] (b : P.Base) (j : b.support) :
    b.chamberFunctional (P.root j) = 1 := by
  simp [RootPairing.Base.chamberFunctional]

public theorem _root_.RootPairing.Base.exists_weylGroup_mem_dominantChamber
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (x : M) :
    ∃ g : P.weylGroup, g.1.weightMap x ∈ b.dominantChamber := by
  let : Finite P.weylGroup := Theory.AlgebraicGroup.weylGroup_finite P
  letI : Fintype P.weylGroup := Fintype.ofFinite P.weylGroup
  obtain ⟨g, -, hg⟩ := Finset.exists_max_image Finset.univ
    (fun g : P.weylGroup => b.chamberFunctional (g.1.weightMap x)) Finset.univ_nonempty
  refine ⟨g, ?_⟩
  intro j
  by_contra hneg
  have hBneg : P.RootForm (g.1.weightMap x) (P.root j) < 0 := lt_of_not_ge hneg
  have hcneg : P.coroot' j (g.1.weightMap x) < 0 := by
    have hlen := RootPairing.rootForm_root_self_pos P j
    have heq := RootPairing.two_mul_rootForm_apply_root P j (g.1.weightMap x)
    nlinarith
  have hmax := hg (b.simpleReflection j * g) (by simp)
  have hcalc : b.chamberFunctional ((b.simpleReflection j * g).1.weightMap x) =
      b.chamberFunctional (g.1.weightMap x) - P.coroot' j (g.1.weightMap x) := by
    rw [show (b.simpleReflection j * g).1.weightMap x =
      P.reflection j (g.1.weightMap x) by rfl]
    rw [P.reflection_apply, map_sub, map_smul, b.chamberFunctional_root]
    simp
  rw [hcalc] at hmax
  linarith

public lemma _root_.RootPairing.Base.rootForm_nonneg_of_mem_dominantChamber_of_isPos
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {x : M} (hx : x ∈ b.dominantChamber) {i : ι} (hi : b.IsPos i) :
    0 ≤ P.RootForm x (P.root i) := by
  rw [_root_.RootPairing.Base.isPos_iff_root_mem_closure] at hi
  suffices ∀ z ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι)),
      0 ≤ P.RootForm x z from this _ hi
  intro z hz
  induction hz using AddSubmonoid.closure_induction with
  | mem y hy =>
      rcases hy with ⟨j, hj, rfl⟩
      exact hx ⟨j, hj⟩
  | zero => simp
  | add y z hy hz hy' hz' =>
      rw [map_add]
      exact add_nonneg hy' hz'

public lemma _root_.RootPairing.Base.rootForm_wordProd
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support) (x y : M) :
    P.RootForm ((b.wordProd l).1.weightMap x) ((b.wordProd l).1.weightMap y) =
      P.RootForm x y := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [b.wordProd_cons]
      change P.RootForm (P.reflection j ((b.wordProd l).1.weightMap x))
        (P.reflection j ((b.wordProd l).1.weightMap y)) = _
      rw [P.rootForm_reflection_reflection_apply, ih]

public lemma _root_.RootPairing.Base.eq_of_wordProd_mem_dominantChamber
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (l : List b.support)
    (hmin : l.length = b.wordLength (b.wordProd l))
    (x y : M) (hx : x ∈ b.dominantChamber) (hy : y ∈ b.dominantChamber)
    (hxy : (b.wordProd l).1.weightMap x = y) : x = y := by
  induction l using List.reverseRecOn generalizing x y with
  | nil => simpa using hxy
  | append_singleton p j ih =>
      have hp_le : b.wordLength (b.wordProd p) ≤ p.length := b.wordLength_le _ p rfl
      have hall_le := b.wordLength_mul_simpleReflection_le (b.wordProd p) j
      have hprod : b.wordProd (p ++ [j]) = b.wordProd p * b.simpleReflection j := by simp
      rw [← hprod, ← hmin] at hall_le
      have hpmin : p.length = b.wordLength (b.wordProd p) := by
        simp only [List.length_append, List.length_singleton] at hall_le
        omega
      have hpos : b.IsPos (P.weylGroupToPerm (b.wordProd p) j) := by
        by_contra hneg
        have hdec := b.wordLength_mul_simpleReflection_of_not_isPos (b.wordProd p) j hneg
        rw [← hprod, ← hmin, ← hpmin] at hdec
        simp at hdec
        omega
      let k := P.weylGroupToPerm (b.wordProd p) j
      have hyk : 0 ≤ P.RootForm y (P.root k) :=
        b.rootForm_nonneg_of_mem_dominantChamber_of_isPos hy hpos
      have hxj : 0 ≤ P.RootForm x (P.root j) := hx j
      have hform : P.RootForm y (P.root k) = -P.RootForm x (P.root j) := by
        rw [hprod] at hxy
        change (b.wordProd p).1.weightMap (P.reflection j x) = y at hxy
        rw [← hxy]
        rw [show P.root k = (b.wordProd p).1.weightMap (P.root j) by
          exact (P.weylGroup_apply_root (b.wordProd p) j).symm]
        rw [b.rootForm_wordProd]
        have h := P.rootForm_reflection_reflection_apply j x (P.root j)
        rw [P.reflection_apply_self, map_neg] at h
        linarith
      have hz : P.RootForm x (P.root j) = 0 := by linarith
      have hc : P.coroot' j x = 0 := by
        have hlen := RootPairing.rootForm_root_self_pos P j
        have heq := RootPairing.two_mul_rootForm_apply_root P j x
        rw [hz, mul_zero] at heq
        exact (mul_eq_zero.mp heq.symm).resolve_right hlen.ne'
      have href : P.reflection j x = x := by simp [P.reflection_apply, hc]
      apply ih hpmin x y hx hy
      rw [hprod] at hxy
      change (b.wordProd p).1.weightMap (P.reflection j x) = y at hxy
      simpa [href] using hxy

open SimpleGraph

set_option maxHeartbeats 800000 in
/-- Every bond on one distinguished arm of an exact three-arm Cartan support
is simple. The conclusion is proved by excluding the first heavy bond; it is
not stored in auxiliary branch data. -/
public lemma cartan_three_arm_distinguished_arm_entries_eq_neg_one_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c : κ) {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → κ) (f1 : Fin (n1 + 1) → κ)
    (f2 : Fin (n2 + 1) → κ)
    (hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (hdisj12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f2 j) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f0 l) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f1 l) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f2 j) (f2 l) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f2 l))
    (hdeg : (SimpleGraph.fromRel fun x y => A x y ≠ 0).degree c = 3) :
    ∀ r : Fin (n0 + 1), 0 < r.val →
      A (f0 ⟨r.val - 1, by omega⟩) (f0 r) = -1 ∧
      A (f0 r) (f0 ⟨r.val - 1, by omega⟩) = -1 := by
  let F0 : Fin (n0 + 1) ↪ κ := ⟨f0, hf0⟩
  have hedge : ∀ s : Fin n0, A (F0 s.castSucc) (F0 s.succ) ≠ 0 := by
    intro s
    have hadjPath : (pathGraph (n0 + 1)).Adj s.castSucc s.succ := by
      rw [pathGraph_adj]
      left
      simp
    have hadj := (hpath0 s.castSucc s.succ).mpr hadjPath
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hforward | hreverse
    · exact hforward
    · have hb := cartan_rankTwo_nonzero_bounds A hrank
        (hf0.ne (ne_of_lt s.castSucc_lt_succ)).symm hreverse
      exact ne_of_lt (lt_of_le_of_lt hb.2.1 (by norm_num))
  intro r hr
  let rpred : Fin (n0 + 1) := ⟨r.val - 1, by omega⟩
  have hrne : f0 rpred ≠ f0 r := by
    apply hf0.ne
    intro h
    have hv := congrArg Fin.val h
    simp [rpred] at hv
    omega
  have hrnz : A (f0 rpred) (f0 r) ≠ 0 := by
    let s : Fin n0 := ⟨r.val - 1, by omega⟩
    have hscast : s.castSucc = rpred := by
      apply Fin.ext
      rfl
    have hssucc : s.succ = r := by
      apply Fin.ext
      simp [s]
      omega
    rw [← hscast, ← hssucc]
    exact hedge s
  have noHeavy
      (hheavy : 2 ≤ A (f0 rpred) (f0 r) * A (f0 r) (f0 rpred)) : False := by
    obtain ⟨m, hmpos, hmle, hsimple, hmheavy⟩ :=
      cartan_path_exists_first_heavy_edge A hrank F0 hedge r.val hr
        (by omega) (by simpa [F0, rpred] using hheavy)
    exact not_cartan_three_arm_first_heavy_of_diagonal_mul_posDef
      A d hdiag hrank hpos c f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2
      h01 h02 hdisj12 hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
      hcross01 hcross02 hcross12 hdeg hmpos (by omega) hsimple hmheavy
  rcases hrank (f0 rpred) (f0 r) hrne with
    h0 | h11 | hb12 | hb21 | hb13 | hb31
  · exact (hrnz h0.1).elim
  · exact h11
  · exact (noHeavy (by simp [hb12.1, hb12.2])).elim
  · exact (noHeavy (by simp [hb21.1, hb21.2])).elim
  · exact (noHeavy (by simp [hb13.1, hb13.2])).elim
  · exact (noHeavy (by simp [hb31.1, hb31.2])).elim

open Set

/-- An equivalence of root pairings preserves all Cartan pairings. -/
public lemma _root_.RootPairing.Equiv.pairing_eq
    {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    (e : P.Equiv Q) (i j : ι) :
    Q.pairing (e.indexEquiv i) (e.indexEquiv j) = P.pairing i j := by
  rw [← P.root_coroot_eq_pairing, ← Q.root_coroot_eq_pairing]
  rw [← RootPairing.Hom.root_weightMap_apply P Q i e.toHom]
  have hc : e.coweightMap (Q.coroot (e.indexEquiv j)) = P.coroot j := by
    simpa using RootPairing.Hom.coroot_coweightMap_apply P Q (e.indexEquiv j) e.toHom
  rw [← hc]
  exact DFunLike.congr_fun
    (LinearMap.congr_fun e.weight_coweight_transpose (Q.coroot (e.indexEquiv j)))
    (P.root i)

/-- Transport a fundamental system along an equivalence of root pairings. -/
public noncomputable def _root_.RootPairing.Base.mapEquiv
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (e : P.Equiv Q) (b : P.Base) : Q.Base :=
  RootPairing.Base.mk' Q (e.indexEquiv '' (b.support : Set ι)) (by
    have hmap : LinearIndepOn R (e.weightMap ∘ P.root) (b.support : Set ι) :=
      b.linearIndepOn_root.map_injOn e.weightMap e.bijective_weightMap.injective.injOn
    have hcomp : LinearIndepOn R (Q.root ∘ e.indexEquiv) (b.support : Set ι) :=
      hmap.congr (fun i _ => by
        simpa [Function.comp_apply] using
          RootPairing.Hom.root_weightMap_apply P Q i e.toHom)
    exact LinearIndepOn.image_of_comp e.indexEquiv Q.root hcomp) (by
      intro i
      let k := e.indexEquiv.symm i
      have hk := b.root_mem_or_neg_mem k
      have hmap (x : M)
          (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι))) :
          e.weightMap x ∈ AddSubmonoid.closure
            (Q.root '' (e.indexEquiv '' (b.support : Set ι))) := by
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
            rcases hx with ⟨j, hj, rfl⟩
            exact AddSubmonoid.subset_closure ⟨e.indexEquiv j, ⟨j, hj, rfl⟩,
              (RootPairing.Hom.root_weightMap_apply P Q j e.toHom).symm⟩
        | zero => simp
        | add x y hx hy hx' hy' => simpa using AddSubmonoid.add_mem _ hx' hy'
      have hroot : e.weightMap (P.root k) = Q.root i := by
        simpa [k] using RootPairing.Hom.root_weightMap_apply P Q k e.toHom
      rcases hk with hk | hk
      · left
        rw [← hroot]
        exact hmap _ hk
      · right
        rw [← hroot, ← map_neg]
        exact hmap _ hk)

@[simp]
public lemma _root_.RootPairing.Base.mem_mapEquiv_support
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (e : P.Equiv Q) (b : P.Base) (i : ι₂) :
    i ∈ (RootPairing.Base.mapEquiv e b).support ↔ e.indexEquiv.symm i ∈ b.support := by
  change i ∈ (Set.toFinite (e.indexEquiv '' (b.support : Set ι))).toFinset ↔ _
  simp only [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨a, ha, hAi⟩
    rw [← hAi]
    simpa using ha
  · intro hi
    exact ⟨e.indexEquiv.symm i, hi, e.indexEquiv.apply_symm_apply i⟩

open Set Function
open Submodule (span)

section

public def _root_.RootPairing.rootIndicesInSubmodule
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (q : Submodule R M) : Set ι :=
  {i | P.root i ∈ q}

public lemma _root_.RootPairing.reflectionPerm_mem_rootIndicesInSubmodule
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (q : Submodule R M) {i j : ι}
    (hi : i ∈ P.rootIndicesInSubmodule q) (hj : j ∈ P.rootIndicesInSubmodule q) :
    P.reflectionPerm i j ∈ P.rootIndicesInSubmodule q := by
  change P.root (P.reflectionPerm i j) ∈ q
  rw [← P.reflectionPerm_root]
  exact q.sub_mem hj (q.smul_mem _ hi)

public def _root_.RootPairing.rootIndicesInAddSubgroup
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) (A : AddSubgroup M) : Set ι :=
  {i | P.root i ∈ A}

public lemma _root_.RootPairing.reflectionPerm_mem_rootIndicesInAddSubgroup
    {ι R M N : Type*} [CommRing R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic]
    (A : AddSubgroup M) {i j : ι}
    (hi : i ∈ P.rootIndicesInAddSubgroup A) (hj : j ∈ P.rootIndicesInAddSubgroup A) :
    P.reflectionPerm i j ∈ P.rootIndicesInAddSubgroup A := by
  change P.root (P.reflectionPerm i j) ∈ A
  rw [← P.reflectionPerm_root, P.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ]
  change P.root j - (P.pairingIn ℤ j i : R) • P.root i ∈ A
  rw [Int.cast_smul_eq_zsmul R]
  exact A.sub_mem hj (A.zsmul_mem hi _)

variable {ι M N : Type*} [Fintype ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [P.IsRootSystem]

public abbrev _root_.RootPairing.rootSpanOfSet (J : Set ι) : Submodule ℝ M :=
  span ℝ (P.root '' J)

@[expose] public def _root_.RootPairing.rootInSpan (J : Set ι) : J ↪ P.rootSpanOfSet J where
  toFun i := ⟨P.root i, Submodule.subset_span ⟨i, i.2, rfl⟩⟩
  inj' := fun _ _ h => Subtype.ext (P.root.injective (congrArg Subtype.val h))

@[expose] public noncomputable def _root_.RootPairing.corootInSpan
    (J : Set ι) : J ↪ P.rootSpanOfSet J where
  toFun i := (2 / P.RootForm (P.root i) (P.root i)) • P.rootInSpan J i
  inj' := by
    intro i j h
    apply Subtype.ext
    apply P.coroot.injective
    apply P.PolarizationEquiv.symm.injective
    rw [P.polarizationEquiv_symm_apply_coroot, P.polarizationEquiv_symm_apply_coroot]
    exact congrArg Subtype.val h

@[expose] public def _root_.RootPairing.rootFormOnSpan
    (J : Set ι) : LinearMap.BilinForm ℝ (P.rootSpanOfSet J) :=
  P.RootForm.restrict (P.rootSpanOfSet J)

public lemma _root_.RootPairing.rootFormOnSpan_nondegenerate (J : Set ι) :
    (P.rootFormOnSpan J).Nondegenerate := by
  refine ((P.rootFormOnSpan J).nondegenerate_iff' (fun x => P.zero_le_rootForm x)
    (P.rootForm_symmetric.domRestrict _)).mpr ?_
  intro x hx
  exact P.rootForm_pos_of_ne_zero (by simp) (Subtype.coe_ne_coe.mpr hx)

public lemma _root_.RootPairing.rootFormOnSpan_root_coroot (J : Set ι) (i j : J) :
    P.rootFormOnSpan J (P.rootInSpan J j) (P.corootInSpan J i) = P.pairing j i := by
  change P.RootForm (P.root j)
    ((2 / P.RootForm (P.root i) (P.root i)) • P.root i) = P.pairing j i
  rw [map_smul]
  change (2 / P.RootForm (P.root i) (P.root i)) *
    P.RootForm (P.root j) (P.root i) = P.coroot' i (P.root j)
  have h := RootPairing.two_mul_rootForm_apply_root P i (P.root j)
  have hn := ne_of_gt (P.rootForm_pos_of_ne_zero (by simp) (P.ne_zero i))
  field_simp [hn]
  linarith

omit [Fintype ι] [P.IsRootSystem] in
public lemma _root_.RootPairing.rootInSpan_span_eq_top (J : Set ι) :
    span ℝ (range (P.rootInSpan J)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (P.rootSpanOfSet J) _).2
  change span ℝ (range fun i : J => P.root i) = span ℝ (P.root '' J)
  congr 1
  ext x
  simp

public lemma _root_.RootPairing.mapsTo_rootInSpan (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) (i : J) :
    MapsTo (Module.preReflection (P.rootInSpan J i)
      ((P.rootFormOnSpan J).flip (P.corootInSpan J i)))
      (range (P.rootInSpan J)) (range (P.rootInSpan J)) := by
  rintro - ⟨j, rfl⟩
  let k : J := ⟨P.reflectionPerm i j, hJ i i.2 j j.2⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simp only [Module.preReflection_apply]
  change P.root (P.reflectionPerm i j) = P.root j -
    P.rootFormOnSpan J (P.rootInSpan J j) (P.corootInSpan J i) • P.root i
  rw [P.rootFormOnSpan_root_coroot]
  exact (P.reflectionPerm_root i j).symm

@[expose] public noncomputable def _root_.RootPairing.rootSubsystem (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) :
    RootPairing J ℝ (P.rootSpanOfSet J) (P.rootSpanOfSet J) := by
  let : FiniteDimensional ℝ (P.rootSpanOfSet J) :=
    FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  let B := P.rootFormOnSpan J
  let : B.IsPerfPair := LinearMap.IsPerfPair.of_injective
    (LinearMap.ker_eq_bot.mp (P.rootFormOnSpan_nondegenerate J).ker_eq_bot)
    (LinearMap.ker_eq_bot.mp (P.rootFormOnSpan_nondegenerate J).flip.ker_eq_bot)
  exact RootPairing.mk'' B (P.rootInSpan J) (P.corootInSpan J)
    (fun i => by simpa using P.rootFormOnSpan_root_coroot J i i)
    (P.mapsTo_rootInSpan J hJ) (P.rootInSpan_span_eq_top J)

@[simp] public theorem _root_.RootPairing.rootSubsystem_root (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) (i : J) :
    (P.rootSubsystem J hJ).root i = P.rootInSpan J i := rfl

@[simp] public theorem _root_.RootPairing.rootSubsystem_coroot (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) (i : J) :
    (P.rootSubsystem J hJ).coroot i = P.corootInSpan J i := rfl

@[simp] public theorem _root_.RootPairing.rootSubsystem_pairing (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) (i j : J) :
    (P.rootSubsystem J hJ).pairing i j = P.pairing i j :=
  P.rootFormOnSpan_root_coroot J j i

public instance _root_.RootPairing.rootSubsystemIsRootSystem (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) :
    (P.rootSubsystem J hJ).IsRootSystem where
  span_root_eq_top := P.rootInSpan_span_eq_top J
  span_coroot_eq_top := by
    have hle : span ℝ (range (P.rootSubsystem J hJ).root) ≤
        span ℝ (range (P.rootSubsystem J hJ).coroot) := by
      apply Submodule.span_le.mpr
      intro _ hy
      rcases hy with ⟨i, rfl⟩
      have hc : (P.rootSubsystem J hJ).coroot i ∈
          span ℝ (range (P.rootSubsystem J hJ).coroot) :=
        Submodule.subset_span (mem_range_self i)
      have hn := ne_of_gt (P.rootForm_pos_of_ne_zero (by simp) (P.ne_zero i))
      have heq : (P.rootSubsystem J hJ).root i =
          (P.RootForm (P.root i) (P.root i) / 2) •
            (P.rootSubsystem J hJ).coroot i := by
        change P.rootInSpan J i = (P.RootForm (P.root i) (P.root i) / 2) •
          ((2 / P.RootForm (P.root i) (P.root i)) • P.rootInSpan J i)
        rw [smul_smul, show (P.RootForm (P.root i) (P.root i) / 2) *
          (2 / P.RootForm (P.root i) (P.root i)) = 1 by field_simp [hn]]
        exact (one_smul ℝ (P.rootInSpan J i)).symm
      rw [heq]
      exact (span ℝ (range (P.rootSubsystem J hJ).coroot)).smul_mem _ hc
    apply eq_top_iff.mpr
    intro x _
    apply hle
    have htop : span ℝ (range (P.rootSubsystem J hJ).root) = ⊤ := by
      change span ℝ (range (P.rootInSpan J)) = ⊤
      exact P.rootInSpan_span_eq_top J
    rw [htop]
    exact Submodule.mem_top

public instance _root_.RootPairing.rootSubsystemIsReduced (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) [P.IsReduced] :
    (P.rootSubsystem J hJ).IsReduced := by
  rw [RootPairing.isReduced_iff]
  intro i j h
  have h' : ¬ LinearIndependent ℝ ![P.root i, P.root j] := by
    intro hli
    apply h
    apply LinearIndependent.of_comp (P.rootSpanOfSet J).subtype
    simp_rw [RootPairing.rootSubsystem_root]
    have hv : (P.rootSpanOfSet J).subtype ∘
        ![P.rootInSpan J i, P.rootInSpan J j] = ![P.root i, P.root j] := by
      funext k
      fin_cases k <;> rfl
    rw [hv]
    exact hli
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) i j h' with hij | hij
  · exact Or.inl (Subtype.ext hij)
  · exact Or.inr (Subtype.ext hij)

public instance _root_.RootPairing.rootSubsystemIsCrystallographic (J : Set ι)
    (hJ : ∀ i ∈ J, ∀ j ∈ J, P.reflectionPerm i j ∈ J) [P.IsCrystallographic] :
    (P.rootSubsystem J hJ).IsCrystallographic where
  exists_value i j := by
    simpa only [RootPairing.rootSubsystem_pairing] using P.exists_value i j

@[expose] public noncomputable def _root_.RootPairing.rootSubsystemInSubmodule
    (q : Submodule ℝ M) :
    RootPairing (P.rootIndicesInSubmodule q) ℝ
      (P.rootSpanOfSet (P.rootIndicesInSubmodule q))
      (P.rootSpanOfSet (P.rootIndicesInSubmodule q)) :=
  P.rootSubsystem (P.rootIndicesInSubmodule q) fun _ hi _ hj =>
    P.reflectionPerm_mem_rootIndicesInSubmodule q hi hj

public instance _root_.RootPairing.rootSubsystemInSubmoduleIsRootSystem
    (q : Submodule ℝ M) :
    (P.rootSubsystemInSubmodule q).IsRootSystem := by
  unfold RootPairing.rootSubsystemInSubmodule
  infer_instance

public instance _root_.RootPairing.rootSubsystemInSubmoduleIsReduced
    (q : Submodule ℝ M) [P.IsReduced] :
    (P.rootSubsystemInSubmodule q).IsReduced := by
  unfold RootPairing.rootSubsystemInSubmodule
  infer_instance

public instance _root_.RootPairing.rootSubsystemInSubmoduleIsCrystallographic
    (q : Submodule ℝ M) [P.IsCrystallographic] :
    (P.rootSubsystemInSubmodule q).IsCrystallographic := by
  unfold RootPairing.rootSubsystemInSubmodule
  infer_instance

@[expose] public noncomputable def _root_.RootPairing.rootSubsystemInAddSubgroup
    [P.IsCrystallographic] (A : AddSubgroup M) :
    RootPairing (P.rootIndicesInAddSubgroup A) ℝ
      (P.rootSpanOfSet (P.rootIndicesInAddSubgroup A))
      (P.rootSpanOfSet (P.rootIndicesInAddSubgroup A)) :=
  P.rootSubsystem (P.rootIndicesInAddSubgroup A) fun _ hi _ hj =>
    P.reflectionPerm_mem_rootIndicesInAddSubgroup A hi hj

public instance _root_.RootPairing.rootSubsystemInAddSubgroupIsRootSystem
    [P.IsCrystallographic] (A : AddSubgroup M) :
    (P.rootSubsystemInAddSubgroup A).IsRootSystem := by
  unfold RootPairing.rootSubsystemInAddSubgroup
  infer_instance

end

/-- Theorem 1.8.3(f): the closed chamber determined by a fundamental system
is a fundamental domain for the Weyl-group action. -/
public theorem weylGroup_dominantChamber_fundamentalDomain
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) : b.IsWeylFundamentalDomain b.dominantChamber := by
  constructor
  · exact b.exists_weylGroup_mem_dominantChamber
  · intro x hx g hgx
    rcases b.wordLength_spec g with ⟨l, hlen, hprod⟩
    have hlen' : l.length = b.wordLength (b.wordProd l) := by
      rw [hprod]
      exact hlen
    have hxy : (b.wordProd l).1.weightMap x = g.1.weightMap x := by rw [hprod]
    exact (b.eq_of_wordProd_mem_dominantChamber l hlen' x (g.1.weightMap x) hx hgx hxy).symm

open SimpleGraph

set_option maxHeartbeats 800000 in
/-- Starting at a degree-three vertex, every edge of a simple support path is
a simple Cartan bond once two other off-path neighbors are fixed. -/
public lemma cartanSupport_path_from_degree_three_entries_eq_neg_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    {c v : κ}
    {p : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Walk c v}
    (hp : p.IsPath) (hpNil : ¬p.Nil)
    {a₁ a₂ : κ} (ha12 : a₁ ≠ a₂)
    (ha₁adj : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c a₁)
    (ha₂adj : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj c a₂)
    (ha₁off : a₁ ∉ p.support) (ha₂off : a₂ ∉ p.support)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c = 3) :
    ∀ i : Fin p.length,
      A (p.getVert i.val) (p.getVert (i.val + 1)) = -1 ∧
      A (p.getVert (i.val + 1)) (p.getVert i.val) = -1 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hacyc : G.IsAcyclic := by
    exact cartanSupport_isAcyclic A d hdiag hrank hpos
  have hlen : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpNil
  let n0 := p.length - 1
  have hn0 : n0 + 1 = p.length := by
    dsimp [n0]
    omega
  let f0 : Fin (n0 + 1) → κ := fun j => p.getVert (j.val + 1)
  let f1 : Fin 1 → κ := fun _ => a₁
  let f2 : Fin 1 → κ := fun _ => a₂
  have hf0 : Function.Injective f0 := by
    intro i j hij
    apply Fin.ext
    have hget := hp.getVert_injOn
      (show i.val + 1 ≤ p.length by omega)
      (show j.val + 1 ≤ p.length by omega) hij
    omega
  have hf1 : Function.Injective f1 := fun i j _ => Subsingleton.elim i j
  have hf2 : Function.Injective f2 := fun i j _ => Subsingleton.elim i j
  have hc0 : ∀ j, c ≠ f0 j := by
    intro j hj
    have hget : p.getVert 0 = p.getVert (j.val + 1) := by
      simpa [f0] using hj
    have hindex := hp.getVert_injOn
      (show 0 ≤ p.length by omega)
      (show j.val + 1 ≤ p.length by omega) hget
    omega
  have hc1 : ∀ j, c ≠ f1 j := by
    intro j
    simpa [f1] using ha₁adj.ne
  have hc2 : ∀ j, c ≠ f2 j := by
    intro j
    simpa [f2] using ha₂adj.ne
  have h01 : ∀ j l, f0 j ≠ f1 l := by
    intro j l hjl
    apply ha₁off
    change p.getVert (j.val + 1) = a₁ at hjl
    exact hjl ▸ p.getVert_mem_support (j.val + 1)
  have h02 : ∀ j l, f0 j ≠ f2 l := by
    intro j l hjl
    apply ha₂off
    change p.getVert (j.val + 1) = a₂ at hjl
    exact hjl ▸ p.getVert_mem_support (j.val + 1)
  have hcenter0 : ∀ j, G.Adj c (f0 j) ↔ j = 0 := by
    intro j
    constructor
    · intro hadj
      by_contra hj
      have hjval : j.val ≠ 0 := by
        intro hj0
        apply hj
        apply Fin.ext
        simpa using hj0
      let i' : Fin (p.length + 1) := 0
      let j' : Fin (p.length + 1) := ⟨j.val + 1, by omega⟩
      have hadj' : G.Adj (p.getVert 0) (p.getVert (j.val + 1)) := by
        rw [p.getVert_zero]
        simpa [f0] using hadj
      have hgap : i'.val + 1 < j'.val := by
        change 0 + 1 < j.val + 1
        omega
      exact simpleGraph_isAcyclic_path_nonadjacent (G := G) hp hacyc
        (i := i') (j := j') hgap (by simpa [i', j'] using hadj')
    · intro hj
      subst j
      simpa [G, f0] using p.adj_getVert_succ (i := 0) hlen
  have hcenter1 : ∀ j, G.Adj c (f1 j) ↔ j = 0 := by
    intro j
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      simpa [G, f1] using ha₁adj
  have hcenter2 : ∀ j, G.Adj c (f2 j) ↔ j = 0 := by
    intro j
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      simpa [G, f2] using ha₂adj
  have hpath0 : ∀ j l, G.Adj (f0 j) (f0 l) ↔
      (pathGraph (n0 + 1)).Adj j l := by
    intro j l
    let j' : Fin p.length := Fin.cast hn0 j
    let l' : Fin p.length := Fin.cast hn0 l
    have htail := simpleGraph_isAcyclic_path_tail_pathGraph hp hacyc j' l'
    simpa [G, f0, j', l', pathGraph_adj] using htail
  have hpath1 : ∀ j l, G.Adj (f1 j) (f1 l) ↔
      (pathGraph 1).Adj j l := by
    intro j l
    simp [f1, pathGraph_adj]
  have hpath2 : ∀ j l, G.Adj (f2 j) (f2 l) ↔
      (pathGraph 1).Adj j l := by
    intro j l
    simp [f2, pathGraph_adj]
  have hcross01 : ∀ j l, ¬ G.Adj (f0 j) (f1 l) := by
    intro j l
    have hjbound : j.val + 1 ≤ p.length := by
      rw [← hn0]
      omega
    let jj : Fin (p.length + 1) :=
      ⟨j.val + 1, Nat.lt_succ_iff.mpr hjbound⟩
    have hjj : jj ≠ 0 := by
      apply Fin.ne_of_val_ne
      simp [jj]
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      (G := G) hp hpNil hacyc
      (by simpa [G] using ha₁adj) ha₁off
      (j := jj) hjj
    rw [G.adj_comm]
    simpa only [f0, f1, jj] using hnot
  have hcross02 : ∀ j l, ¬ G.Adj (f0 j) (f2 l) := by
    intro j l
    have hjbound : j.val + 1 ≤ p.length := by
      rw [← hn0]
      omega
    let jj : Fin (p.length + 1) :=
      ⟨j.val + 1, Nat.lt_succ_iff.mpr hjbound⟩
    have hjj : jj ≠ 0 := by
      apply Fin.ne_of_val_ne
      simp [jj]
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      (G := G) hp hpNil hacyc
      (by simpa [G] using ha₂adj) ha₂off
      (j := jj) hjj
    rw [G.adj_comm]
    simpa only [f0, f2, jj] using hnot
  have hcross12 : ∀ j l, ¬ G.Adj (f1 j) (f2 l) := by
    intro j l
    let q := ha₂adj.toWalk
    have hq : q.IsPath := Walk.IsPath.of_adj ha₂adj
    have hqNil : ¬q.Nil := by simp [q]
    have ha₁offq : a₁ ∉ q.support := by
      simp [q, ha₁adj.ne.symm, ha12]
    simpa [G, f1, f2, q] using
      (simpleGraph_isAcyclic_path_offpath_start_nonadjacent hq hqNil hacyc
        (by simpa [G] using ha₁adj) ha₁offq
        (j := (1 : Fin (q.length + 1))) (by norm_num [q]))
  have harm :=
    cartan_three_arm_distinguished_arm_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos c f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2
      h01 h02 (by simpa [f1, f2] using ha12) hcenter0 hcenter1 hcenter2
      hpath0 hpath1 hpath2 hcross01 hcross02 hcross12 (by simpa [G] using hdeg)
  intro i
  by_cases hi : i.val = 0
  · have hedge : G.Adj c (p.getVert 1) := by
      simpa [G] using p.adj_getVert_succ (i := 0) hlen
    have hs := cartanSupport_degree_three_edge_entries_eq_neg_one
      A d hdiag hrank hpos c (p.getVert 1) (by simpa [G] using hdeg) hedge
    simpa [hi] using hs
  · let r : Fin (n0 + 1) := ⟨i.val, by omega⟩
    have hr : 0 < r.val := by simpa [r] using Nat.pos_of_ne_zero hi
    have hs := harm r hr
    have hir : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)
    simpa [f0, r, hir] using hs

open SimpleGraph

/-- Every bond on all three arms of an exact three-arm positive-definite
Cartan support is `(-1,-1)`. The three conclusions remain ordinary theorem
components rather than fields of classification data. -/
public lemma cartan_three_arm_all_entries_eq_neg_one_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c : κ) {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → κ) (f1 : Fin (n1 + 1) → κ)
    (f2 : Fin (n2 + 1) → κ)
    (hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj c (f2 j) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f0 l) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f1 l) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f2 j) (f2 l) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (f1 j) (f2 l))
    (hdeg : (SimpleGraph.fromRel fun x y => A x y ≠ 0).degree c = 3) :
    (∀ r : Fin (n0 + 1), 0 < r.val →
      A (f0 ⟨r.val - 1, by omega⟩) (f0 r) = -1 ∧
      A (f0 r) (f0 ⟨r.val - 1, by omega⟩) = -1) ∧
    (∀ r : Fin (n1 + 1), 0 < r.val →
      A (f1 ⟨r.val - 1, by omega⟩) (f1 r) = -1 ∧
      A (f1 r) (f1 ⟨r.val - 1, by omega⟩) = -1) ∧
    (∀ r : Fin (n2 + 1), 0 < r.val →
      A (f2 ⟨r.val - 1, by omega⟩) (f2 r) = -1 ∧
      A (f2 r) (f2 ⟨r.val - 1, by omega⟩) = -1) := by
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  have h10 : ∀ j l, f1 j ≠ f0 l := fun j l h => h01 l j h.symm
  have h20 : ∀ j l, f2 j ≠ f0 l := fun j l h => h02 l j h.symm
  have h21 : ∀ j l, f2 j ≠ f1 l := fun j l h => h12 l j h.symm
  have hcross10 : ∀ j l, ¬ G.Adj (f1 j) (f0 l) := by
    intro j l
    rw [G.adj_comm]
    exact hcross01 l j
  have hcross20 : ∀ j l, ¬ G.Adj (f2 j) (f0 l) := by
    intro j l
    rw [G.adj_comm]
    exact hcross02 l j
  have hcross21 : ∀ j l, ¬ G.Adj (f2 j) (f1 l) := by
    intro j l
    rw [G.adj_comm]
    exact hcross12 l j
  refine ⟨?_, ?_, ?_⟩
  · exact cartan_three_arm_distinguished_arm_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos c f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2
      h01 h02 h12 hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
      hcross01 hcross02 hcross12 hdeg
  · exact cartan_three_arm_distinguished_arm_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos c f1 f0 f2 hf1 hf0 hf2 hc1 hc0 hc2
      h10 h12 h02 hcenter1 hcenter0 hcenter2 hpath1 hpath0 hpath2
      hcross10 hcross12 hcross02 hdeg
  · exact cartan_three_arm_distinguished_arm_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos c f2 f0 f1 hf2 hf0 hf1 hc2 hc0 hc1
      h20 h21 h01 hcenter2 hcenter0 hcenter1 hpath2 hpath0 hpath1
      hcross20 hcross21 hcross01 hdeg

/-- The forward implication of Theorem 1.8.7: a root-system equivalence
identifies the Dynkin diagrams of a base and its transported base. -/
public lemma dynkinDiagramIso_of_rootPairingEquiv
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced]
    (e : P.Equiv Q) (b : P.Base) :
    Nonempty
      (P.DynkinDiagramIso b.support Q (RootPairing.Base.mapEquiv e b).support) := by
  let vertexEquiv : b.support ≃ (RootPairing.Base.mapEquiv e b).support :=
    Equiv.subtypeEquiv e.indexEquiv (fun i => by
      rw [RootPairing.Base.mem_mapEquiv_support]
      simp)
  refine ⟨⟨vertexEquiv, ?_⟩⟩
  intro i j
  apply FaithfulSMul.algebraMap_injective ℤ R
  simp only [RootPairing.dynkinDiagramOn, RootPairing.algebraMap_pairingIn]
  exact e.pairing_eq i j

open Set
open Submodule (span)

section

variable {ι M N : Type*} [Fintype ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]

/-- The real span of the simple roots indexed by `J`. -/
@[expose] public def _root_.RootPairing.Base.parabolicRootSpan
    (b : P.Base) (J : Set b.support) :
    Submodule ℝ M :=
  span ℝ (P.root '' ((fun j : b.support => (j : ι)) '' J))

/-- The roots of `P` lying in the real span of `J`. -/
@[expose] public def _root_.RootPairing.Base.parabolicRootIndices
    (b : P.Base) (J : Set b.support) : Set ι :=
  {i | P.root i ∈ b.parabolicRootSpan J}

/-- A simple root in `J`, regarded as a root of the subsystem in `span J`. -/
@[expose] public def _root_.RootPairing.Base.parabolicSimpleIndex
    (b : P.Base) (J : Set b.support) (j : J) :
    b.parabolicRootIndices J := by
  refine ⟨(j.1 : ι), ?_⟩
  apply Submodule.subset_span
  show P.root (j.1 : ι) ∈ P.root '' ((fun k : b.support => (k : ι)) '' J)
  exact ⟨(j.1 : ι), ⟨j.1, j.2, rfl⟩, rfl⟩

/-- The root system `Σ ∩ span ℝ J`. -/
@[expose] public noncomputable def _root_.RootPairing.Base.parabolicRootSubsystem
    (b : P.Base) (J : Set b.support) :
    RootPairing (b.parabolicRootIndices J) ℝ
      (P.rootSpanOfSet (b.parabolicRootIndices J))
      (P.rootSpanOfSet (b.parabolicRootIndices J)) :=
  P.rootSubsystem (b.parabolicRootIndices J) fun i hi j hj => by
    change P.root (P.reflectionPerm i j) ∈ b.parabolicRootSpan J
    rw [← P.reflectionPerm_root]
    exact (b.parabolicRootSpan J).sub_mem hj
      ((b.parabolicRootSpan J).smul_mem _ hi)

public instance _root_.RootPairing.Base.parabolicRootSubsystemIsRootSystem
    (b : P.Base) (J : Set b.support) :
    (b.parabolicRootSubsystem J).IsRootSystem := by
  unfold RootPairing.Base.parabolicRootSubsystem
  infer_instance

public instance _root_.RootPairing.Base.parabolicRootSubsystemIsReduced
    (b : P.Base) (J : Set b.support) :
    (b.parabolicRootSubsystem J).IsReduced := by
  unfold RootPairing.Base.parabolicRootSubsystem
  infer_instance

public instance _root_.RootPairing.Base.parabolicRootSubsystemIsCrystallographic
    (b : P.Base) (J : Set b.support) :
    (b.parabolicRootSubsystem J).IsCrystallographic := by
  unfold RootPairing.Base.parabolicRootSubsystem
  infer_instance

omit [P.IsCrystallographic] [P.IsReduced] in
@[simp] public theorem _root_.RootPairing.Base.parabolicRootSubsystem_pairing
    (b : P.Base) (J : Set b.support) (i k : b.parabolicRootIndices J) :
    (b.parabolicRootSubsystem J).pairing i k = P.pairing (i : ι) (k : ι) := by
  unfold RootPairing.Base.parabolicRootSubsystem
  exact P.rootSubsystem_pairing (b.parabolicRootIndices J) _ i k

omit [P.IsCrystallographic] [P.IsReduced] in
public lemma _root_.RootPairing.Base.parabolicSimpleRoots_linearIndepOn
    (b : P.Base) (J : Set b.support) :
    LinearIndepOn ℝ (b.parabolicRootSubsystem J).root
      (Set.range (b.parabolicSimpleIndex J)) := by
  apply LinearIndepOn.of_comp (P.rootSpanOfSet (b.parabolicRootIndices J)).subtype
  rw [linearIndepOn_range_iff]
  · change LinearIndependent ℝ (fun j : J => P.root (j.1 : ι))
    exact b.linearIndepOn_root.comp (fun j : J => (j.1 : b.support))
      Subtype.val_injective
  · intro j k h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : b.parabolicRootIndices J => (x : ι)) h

omit [P.IsCrystallographic] [P.IsReduced] in
public lemma _root_.RootPairing.Base.mem_closure_parabolicSimpleRoots
    (b : P.Base) (J : Set b.support)
    (x : P.rootSpanOfSet (b.parabolicRootIndices J))
    (hx : (x : M) ∈ AddSubmonoid.closure
      (P.root '' ((fun j : b.support => (j : ι)) '' J))) :
    x ∈ AddSubmonoid.closure
      ((b.parabolicRootSubsystem J).root ''
        Set.range (b.parabolicSimpleIndex J)) := by
  let A := AddSubmonoid.closure
    ((b.parabolicRootSubsystem J).root ''
      Set.range (b.parabolicSimpleIndex J))
  have hsub : AddSubmonoid.closure
      (P.root '' ((fun j : b.support => (j : ι)) '' J)) ≤ A.map
        (P.rootSpanOfSet (b.parabolicRootIndices J)).subtype := by
    rw [AddSubmonoid.closure_le]
    rintro y ⟨i, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨(b.parabolicRootSubsystem J).root
      (b.parabolicSimpleIndex J ⟨j, hj⟩), ?_, ?_⟩
    · exact AddSubmonoid.subset_closure ⟨_, ⟨⟨j, hj⟩, rfl⟩, rfl⟩
    · rfl
  rcases hsub hx with ⟨y, hy, hyeq⟩
  have hxy : y = x := by
    apply Subtype.ext
    exact hyeq
  simpa [hxy] using hy

/-- The subset `J` is a fundamental system for the root subsystem in `span J`. -/
@[expose] public noncomputable def _root_.RootPairing.Base.parabolicSubsystemBase
    (b : P.Base) (J : Set b.support) :
    (b.parabolicRootSubsystem J).Base :=
  RootPairing.Base.mk' _ (Set.range (b.parabolicSimpleIndex J))
    (b.parabolicSimpleRoots_linearIndepOn J) (by
      intro x
      letI := P.indexNeg
      rcases b.root_mem_or_neg_mem (x : ι) with hx | hx
      · exact Or.inl (b.mem_closure_parabolicSimpleRoots J _
          (b.closure_mem_span_root_image_of_mem_span J _ hx (by
            change P.root (x : ι) ∈ b.parabolicRootSpan J
            exact x.2)))
      · exact Or.inr (b.mem_closure_parabolicSimpleRoots J _
          (b.closure_mem_span_root_image_of_mem_span J _ hx (by
            change -P.root (x : ι) ∈ b.parabolicRootSpan J
            exact (b.parabolicRootSpan J).neg_mem x.2))))

@[simp] public theorem _root_.RootPairing.Base.parabolicSimpleIndex_mem_support
    (b : P.Base) (J : Set b.support) (j : J) :
    b.parabolicSimpleIndex J j ∈ (b.parabolicSubsystemBase J).support := by
  change b.parabolicSimpleIndex J j ∈
    (Set.toFinite (Set.range (b.parabolicSimpleIndex J))).toFinset
  simp

public lemma _root_.RootPairing.Base.mem_parabolicSubsystemBase_support_iff
    (b : P.Base) (J : Set b.support) (i : b.parabolicRootIndices J) :
    i ∈ (b.parabolicSubsystemBase J).support ↔
      ∃ j : J, i = b.parabolicSimpleIndex J j := by
  change i ∈ (Set.toFinite (Set.range (b.parabolicSimpleIndex J))).toFinset ↔ _
  simp [eq_comm]

public lemma _root_.RootPairing.Base.exists_parabolicSimpleIndex_eq_of_mem_support
    (b : P.Base) (J : Set b.support)
    (k : (b.parabolicSubsystemBase J).support) :
    ∃ j : J, (k : b.parabolicRootIndices J) =
      b.parabolicSimpleIndex J j := by
  exact (b.mem_parabolicSubsystemBase_support_iff J k).1 k.property

private noncomputable def parabolicSupportEquiv
    (b : P.Base) (J : Set b.support) :
    J ≃ (b.parabolicSubsystemBase J).support where
  toFun j := ⟨b.parabolicSimpleIndex J j, b.parabolicSimpleIndex_mem_support J j⟩
  invFun k := Classical.choose (b.exists_parabolicSimpleIndex_eq_of_mem_support J k)
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    have h := Classical.choose_spec (b.exists_parabolicSimpleIndex_eq_of_mem_support J
      ⟨b.parabolicSimpleIndex J j, b.parabolicSimpleIndex_mem_support J j⟩)
    exact (congrArg (fun x : b.parabolicRootIndices J => (x : ι)) h).symm
  right_inv k := by
    apply Subtype.ext
    exact (Classical.choose_spec (b.exists_parabolicSimpleIndex_eq_of_mem_support J k)).symm

private lemma parabolicSubsystemSimpleReflection_smul
    (b : P.Base) (J : Set b.support) (j : J)
    (x : P.rootSpanOfSet (b.parabolicRootIndices J)) :
    (((((b.parabolicSubsystemBase J).simpleReflection
      (parabolicSupportEquiv b J j)) • x :
        P.rootSpanOfSet (b.parabolicRootIndices J)) : M)) =
      b.simpleReflection j.1 • (x : M) := by
  change ((((b.parabolicRootSubsystem J).reflection
    (b.parabolicSimpleIndex J j)) x :
      P.rootSpanOfSet (b.parabolicRootIndices J)) : M) =
    P.reflection (j.1 : ι) x
  rw [RootPairing.reflection_apply, RootPairing.reflection_apply]
  change (x : M) -
      (b.parabolicRootSubsystem J).toLinearMap x
        ((b.parabolicRootSubsystem J).coroot (b.parabolicSimpleIndex J j)) •
          P.root (j.1 : ι) =
    (x : M) - P.toLinearMap x (P.coroot (j.1 : ι)) • P.root (j.1 : ι)
  have hp : (b.parabolicRootSubsystem J).toLinearMap x
      ((b.parabolicRootSubsystem J).coroot (b.parabolicSimpleIndex J j)) =
      P.toLinearMap x (P.coroot (j.1 : ι)) := by
    let f : Module.Dual ℝ (P.rootSpanOfSet (b.parabolicRootIndices J)) :=
      (b.parabolicRootSubsystem J).toLinearMap.flip
        ((b.parabolicRootSubsystem J).coroot (b.parabolicSimpleIndex J j))
    let g : Module.Dual ℝ (P.rootSpanOfSet (b.parabolicRootIndices J)) :=
      (P.toLinearMap.flip (P.coroot (j.1 : ι))).comp
        (P.rootSpanOfSet (b.parabolicRootIndices J)).subtype
    have hfg : f = g := by
      apply LinearMap.ext_on (P.rootInSpan_span_eq_top (b.parabolicRootIndices J))
      intro y hy
      rcases hy with ⟨k, rfl⟩
      dsimp [f, g]
      change (b.parabolicRootSubsystem J).pairing k
          (b.parabolicSimpleIndex J j) = P.pairing (k : ι) (j.1 : ι)
      simp [RootPairing.Base.parabolicSimpleIndex]
    exact LinearMap.congr_fun hfg x
  rw [hp]

private lemma parabolicSubsystem_wordProd_smul
    (b : P.Base) (J : Set b.support)
    (l : List (b.parabolicSubsystemBase J).support)
    (x : P.rootSpanOfSet (b.parabolicRootIndices J)) :
    (((((b.parabolicSubsystemBase J).wordProd l) • x :
      P.rootSpanOfSet (b.parabolicRootIndices J)) : M)) =
    b.wordProd (l.map fun k => ((parabolicSupportEquiv b J).symm k).1) • (x : M) := by
  induction l generalizing x with
  | nil => simp
  | cons k l ih =>
      rw [List.map_cons, (b.parabolicSubsystemBase J).wordProd_cons,
        b.wordProd_cons, mul_smul, mul_smul]
      have hk := parabolicSubsystemSimpleReflection_smul b J
        ((parabolicSupportEquiv b J).symm k)
        ((b.parabolicSubsystemBase J).wordProd l • x)
      simp only [Equiv.apply_symm_apply] at hk
      rw [hk, ih]

/-- Every Weyl-group action of the subsystem `Σ ∩ span ℝ J` is the restriction
of an element of the standard parabolic subgroup `W_J`. -/
public theorem _root_.RootPairing.Base.exists_parabolicSubgroup_action_eq_subsystemWeylGroup
    (b : P.Base) (J : Set b.support)
    (h : (b.parabolicRootSubsystem J).weylGroup) :
    ∃ g : P.weylGroup, g ∈ b.parabolicSubgroup J ∧
      ∀ x : P.rootSpanOfSet (b.parabolicRootIndices J),
        g • (x : M) =
          (((h • x : P.rootSpanOfSet (b.parabolicRootIndices J)) : M)) := by
  rcases (b.parabolicSubsystemBase J).wordLength_spec h with ⟨l, -, hl⟩
  let m : List b.support := l.map fun k => ((parabolicSupportEquiv b J).symm k).1
  refine ⟨b.wordProd m, ?_, ?_⟩
  · apply b.wordProd_mem_parabolicSubgroup J
    intro j hj
    simp only [m, List.mem_map] at hj
    rcases hj with ⟨k, -, rfl⟩
    exact ((parabolicSupportEquiv b J).symm k).2
  · intro x
    rw [← hl]
    exact (parabolicSubsystem_wordProd_smul b J l x).symm

/-- Every element of `W_J` restricts to a Weyl-group action of the subsystem
`Σ ∩ span ℝ J`. -/
public theorem _root_.RootPairing.Base.exists_subsystemWeylGroup_action_eq_parabolicSubgroup
    (b : P.Base) (J : Set b.support) (g : P.weylGroup)
    (hg : g ∈ b.parabolicSubgroup J) :
    ∃ h : (b.parabolicRootSubsystem J).weylGroup,
      ∀ x : P.rootSpanOfSet (b.parabolicRootIndices J),
        (((h • x : P.rootSpanOfSet (b.parabolicRootIndices J)) : M)) =
          g • (x : M) := by
  induction hg using Subgroup.closure_induction'' with
  | one => exact ⟨1, by simp⟩
  | mem g hg =>
      rcases hg with ⟨j, hj, rfl⟩
      let jJ : J := ⟨j, hj⟩
      refine ⟨(b.parabolicSubsystemBase J).simpleReflection
        (parabolicSupportEquiv b J jJ), ?_⟩
      exact parabolicSubsystemSimpleReflection_smul b J jJ
  | inv_mem g hg =>
      rcases hg with ⟨j, hj, rfl⟩
      let jJ : J := ⟨j, hj⟩
      refine ⟨(b.parabolicSubsystemBase J).simpleReflection
        (parabolicSupportEquiv b J jJ), ?_⟩
      intro x
      rw [b.simpleReflection_inv]
      exact parabolicSubsystemSimpleReflection_smul b J jJ x
  | mul g h hg hh ihg ihh =>
      rcases ihg with ⟨g', hg'⟩
      rcases ihh with ⟨h', hh'⟩
      refine ⟨g' * h', ?_⟩
      intro x
      rw [mul_smul, mul_smul]
      rw [hg', hh']

end

open Set Function

/-! GLS3, Theorem 1.8.5. -/

open Set

section

@[expose]
public def IsFundamentalRootSubset
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (roots base : Set ι) : Prop :=
  base ⊆ roots ∧
    LinearIndependent ℝ (fun α : base => P.root α) ∧
    ∀ i ∈ roots,
      (∃ coefficients : base →₀ ℝ,
        P.root i = coefficients.sum (fun α c => c • P.root α) ∧
          ∀ α ∈ coefficients.support, 0 ≤ coefficients α) ∨
      ∃ coefficients : base →₀ ℝ,
        P.root i = coefficients.sum (fun α c => c • P.root α) ∧
          ∀ α ∈ coefficients.support, coefficients α ≤ 0

private def rootNonorthogonalityGraph
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => ¬ P.IsOrthogonal i j

private lemma rootNonorthogonalityGraph_adj_iff
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {i j : ι} :
    (rootNonorthogonalityGraph P).Adj i j ↔ i ≠ j ∧ ¬ P.IsOrthogonal i j := by
  unfold rootNonorthogonalityGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, fun hij => h hij.symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

private lemma component_isIrreducibleSet
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N}
    (C : (rootNonorthogonalityGraph P).ConnectedComponent) :
    P.IsIrreducibleSet C.supp := by
  refine ⟨C.nonempty_supp, ?_⟩
  intro a b ha hb hab hdisjoint
  by_contra hcross
  push Not at hcross
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hiC : i ∈ C.supp := by rw [← hab]; exact Or.inl hi
  have hjC : j ∈ C.supp := by rw [← hab]; exact Or.inr hj
  have hreach := C.reachable_of_mem_supp hiC hjC
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have stay : ∀ {u v}, Relation.ReflTransGen (rootNonorthogonalityGraph P).Adj u v →
      u ∈ a → v ∈ a := by
    intro u v huv
    induction huv using Relation.ReflTransGen.trans_induction_on with
    | refl x => exact fun hx => hx
    | single hxy =>
        rename_i x y
        intro hxA
        have hxC : x ∈ C.supp := by rw [← hab]; exact Or.inl hxA
        have hyC := C.mem_supp_of_adj_mem_supp hxC hxy
        have hyAB : y ∈ a ∨ y ∈ b := by
          change y ∈ a ∪ b
          exact hab.symm ▸ hyC
        rcases hyAB with hyA | hyB
        · exact hyA
        · exact False.elim ((rootNonorthogonalityGraph_adj_iff.mp hxy).2
            (hcross x hxA y hyB))
    | trans hxy hyz ihxy ihyz =>
        intro hxA
        exact ihyz (ihxy hxA)
  have hjA : j ∈ a := stay hreach hi
  exact Set.disjoint_left.mp hdisjoint hjA hj

private def canonicalOrthogonalDecomposition
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) : P.OrthogonalDecomposition where
  parts := Set.range fun C : (rootNonorthogonalityGraph P).ConnectedComponent => C.supp
  nonempty_parts := by
    rintro s ⟨C, rfl⟩
    exact C.nonempty_supp
  cover := by
    rw [Set.sUnion_range]
    exact SimpleGraph.iUnion_connectedComponentSupp (rootNonorthogonalityGraph P)
  pairwise_disjoint := by
    rintro _ ⟨C, rfl⟩ _ ⟨D, rfl⟩ hne
    apply SimpleGraph.pairwise_disjoint_supp_connectedComponent
    intro hCD
    exact hne (congrArg SimpleGraph.ConnectedComponent.supp hCD)
  orthogonal := by
    rintro _ ⟨C, rfl⟩ _ ⟨D, rfl⟩ hCD i hi j hj
    by_contra horth
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hCD (congrArg SimpleGraph.ConnectedComponent.supp
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex hi hj))
    have hadj : (rootNonorthogonalityGraph P).Adj i j :=
      rootNonorthogonalityGraph_adj_iff.mpr ⟨hij, horth⟩
    have hcomponents := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hi hj
    rw [hi, hj] at hcomponents
    exact hCD (congrArg SimpleGraph.ConnectedComponent.supp hcomponents)

private lemma canonicalOrthogonalDecomposition_isIrreducible
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) :
    _root_.RootPairing.OrthogonalDecomposition.IsIrreducible
      (canonicalOrthogonalDecomposition P) := by
  change ∀ s ∈ (canonicalOrthogonalDecomposition P).parts, P.IsIrreducibleSet s
  rintro _ ⟨C, rfl⟩
  exact component_isIrreducibleSet C

private lemma reachable_stays_in_orthogonalPart
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (e : P.OrthogonalDecomposition)
    {s : Set ι} (hs : s ∈ e.parts) {i j : ι} (hi : i ∈ s)
    (hreach : (rootNonorthogonalityGraph P).Reachable i j) : j ∈ s := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach using Relation.ReflTransGen.trans_induction_on with
  | refl x => exact hi
  | single hxy =>
      rename_i x y
      obtain ⟨t, htparts, hyt⟩ : ∃ t ∈ e.parts, y ∈ t := by
        have hyUnion : y ∈ ⋃₀ e.parts := by rw [e.cover]; trivial
        exact Set.mem_sUnion.mp hyUnion
      by_cases hts : t = s
      · exact hts ▸ hyt
      · have horth := e.orthogonal s hs t htparts (Ne.symm hts) x hi y hyt
        exact False.elim ((rootNonorthogonalityGraph_adj_iff.mp hxy).2 horth)
  | trans hxy hyz ihxy ihyz =>
      exact ihyz (ihxy hi)

private lemma irreduciblePart_eq_componentSupp
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (e : P.OrthogonalDecomposition)
    (hirr : _root_.RootPairing.OrthogonalDecomposition.IsIrreducible e)
    {s : Set ι} (hs : s ∈ e.parts)
    {i : ι} (hi : i ∈ s) :
    s = ((rootNonorthogonalityGraph P).connectedComponentMk i).supp := by
  change (∀ t ∈ e.parts, P.IsIrreducibleSet t) at hirr
  let C := (rootNonorthogonalityGraph P).connectedComponentMk i
  apply Set.Subset.antisymm
  · intro j hj
    by_contra hjC
    let a : Set ι := s ∩ C.supp
    let b : Set ι := s \ C.supp
    have ha : a.Nonempty := ⟨i, hi, by simp [C]⟩
    have hb : b.Nonempty := ⟨j, hj, hjC⟩
    have hab : a ∪ b = s := by
      ext x
      simp only [a, b, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    have hdisjoint : Disjoint a b := by
      rw [Set.disjoint_left]
      intro x hxa hxb
      exact hxb.2 hxa.2
    obtain ⟨x, hxa, y, hyb, hnot⟩ := (hirr s hs).2 a b ha hb hab hdisjoint
    have hxy : x ≠ y := by
      intro hxy
      subst y
      exact hyb.2 hxa.2
    have hadj : (rootNonorthogonalityGraph P).Adj x y :=
      rootNonorthogonalityGraph_adj_iff.mpr ⟨hxy, hnot⟩
    have hyC := C.mem_supp_of_adj_mem_supp hxa.2 hadj
    exact hyb.2 hyC
  · intro j hj
    exact reachable_stays_in_orthogonalPart e hs hi
      (((rootNonorthogonalityGraph P).connectedComponentMk i).reachable_of_mem_supp
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem hj)

private lemma irreducibleOrthogonalDecomposition_parts_eq_canonical
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} (e : P.OrthogonalDecomposition)
    (hirr : _root_.RootPairing.OrthogonalDecomposition.IsIrreducible e) :
    e.parts = (canonicalOrthogonalDecomposition P).parts := by
  apply Set.Subset.antisymm
  · intro s hs
    obtain ⟨i, hi⟩ := e.nonempty_parts s hs
    refine ⟨(rootNonorthogonalityGraph P).connectedComponentMk i, ?_⟩
    exact (irreduciblePart_eq_componentSupp e hirr hs hi).symm
  · rintro s ⟨C, rfl⟩
    obtain ⟨i, hiC⟩ := C.nonempty_supp
    obtain ⟨t, htparts, hit⟩ : ∃ t ∈ e.parts, i ∈ t := by
      have hiUnion : i ∈ ⋃₀ e.parts := by rw [e.cover]; trivial
      exact Set.mem_sUnion.mp hiUnion
    have ht := irreduciblePart_eq_componentSupp e hirr htparts hit
    have hcomponent : (rootNonorthogonalityGraph P).connectedComponentMk i = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp hiC
    rw [hcomponent] at ht
    rw [ht] at htparts
    exact htparts

/-- Every root pairing has a unique partition into irreducible orthogonal
parts, where uniqueness refers to the set of parts.

This is the decomposition clause of GLS3, Theorem 1.8.5(a). -/
public theorem exists_unique_irreducibleOrthogonalDecomposition_parts
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) :
    ∃ d : P.OrthogonalDecomposition,
      _root_.RootPairing.OrthogonalDecomposition.IsIrreducible d ∧
        ∀ e : P.OrthogonalDecomposition,
          _root_.RootPairing.OrthogonalDecomposition.IsIrreducible e → e.parts = d.parts := by
  refine ⟨canonicalOrthogonalDecomposition P,
    canonicalOrthogonalDecomposition_isIrreducible P, ?_⟩
  intro e he
  exact irreducibleOrthogonalDecomposition_parts_eq_canonical e he

private lemma rootForm_root_eq_zero_of_isOrthogonal
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {i j : ι} (hij : P.IsOrthogonal i j) :
    P.RootForm (P.root i) (P.root j) = 0 := by
  have hcox : P.coxeterWeight i j = 0 :=
    RootPairing.coxeterWeight_zero_iff_isOrthogonal.mpr hij
  have h := P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  rw [hcox, zero_smul] at h
  norm_num [nsmul_eq_mul] at h ⊢
  nlinarith

private lemma rootForm_eq_zero_of_mem_componentSpans
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {s t : Set ι}
    (horth : ∀ i ∈ s, ∀ j ∈ t, P.IsOrthogonal i j)
    {x y : M} (hx : x ∈ Submodule.span ℝ (P.root '' s))
    (hy : y ∈ Submodule.span ℝ (P.root '' t)) :
    P.RootForm x y = 0 := by
  have hroot (i : ι) (hi : i ∈ s) : P.RootForm (P.root i) y = 0 := by
    refine Submodule.span_induction (p := fun y _ => P.RootForm (P.root i) y = 0)
      ?_ (by simp) ?_ ?_ hy
    · rintro _ ⟨j, hj, rfl⟩
      exact rootForm_root_eq_zero_of_isOrthogonal P (horth i hi j hj)
    · intro y z _ _ hyz hzz
      simp [map_add, hyz, hzz]
    · intro a y _ hy0
      simp [map_smul, hy0]
  refine Submodule.span_induction (p := fun x _ => P.RootForm x y = 0)
    ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    exact hroot i hi
  · intro x z _ _ hx0 hz0
    simp [map_add, hx0, hz0]
  · intro a x _ hx0
    simp [map_smul, hx0]

private lemma componentSpans_disjoint
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) {s t : Set ι}
    (horth : ∀ i ∈ s, ∀ j ∈ t, P.IsOrthogonal i j) :
    Disjoint (Submodule.span ℝ (P.root '' s)) (Submodule.span ℝ (P.root '' t)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  apply P.eq_zero_of_mem_rootSpan_of_rootForm_self_eq_zero
  · apply Submodule.span_mono _ hx
    rintro _ ⟨i, hi, rfl⟩
    exact Set.mem_range_self i
  · exact rootForm_eq_zero_of_mem_componentSpans P horth hx hy

private lemma filtered_sum_mem_componentSpan
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (base s : Set ι) (c : base →₀ ℝ)
    (p : base → Prop) [DecidablePred p]
    (hp : ∀ α, p α → (α : ι) ∈ s) :
    (c.filter p).sum (fun α a => a • P.root α) ∈
      Submodule.span ℝ (P.root '' s) := by
  classical
  simp only [Finsupp.sum]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨α, hp α ?_, rfl⟩
  exact (Finset.mem_filter.mp hα).2

private lemma coefficients_support_subset_orthogonalPart
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (d : P.OrthogonalDecomposition)
    {s base : Set ι} (hs : s ∈ d.parts)
    (hli : LinearIndependent ℝ (fun α : base => P.root α))
    {i : ι} (hi : i ∈ s) (c : base →₀ ℝ)
    (hc : P.root i = c.sum (fun α a => a • P.root α)) :
    ∀ α ∈ c.support, (α : ι) ∈ s := by
  classical
  let inside := c.filter fun α : base => (α : ι) ∈ s
  let outside := c.filter fun α : base => (α : ι) ∉ s
  let combination : (base →₀ ℝ) →ₗ[ℝ] M :=
    Finsupp.linearCombination ℝ (fun α : base => P.root α)
  have hsplit : inside + outside = c := Finsupp.filter_add_filter_not c _
  have hins : combination inside ∈ Submodule.span ℝ (P.root '' s) := by
    exact filtered_sum_mem_componentSpan P base s c _ (fun α hα => hα)
  have hout_compl : combination outside ∈ Submodule.span ℝ (P.root '' sᶜ) := by
    simpa only [combination, Finsupp.linearCombination_apply, inside, outside,
      Set.mem_compl_iff] using filtered_sum_mem_componentSpan P base sᶜ c _ (fun α hα => hα)
  have hroot : P.root i ∈ Submodule.span ℝ (P.root '' s) :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have hout : combination outside ∈ Submodule.span ℝ (P.root '' s) := by
    have hsum : combination inside + combination outside = P.root i := by
      rw [← map_add, hsplit]
      simpa only [combination, Finsupp.linearCombination_apply] using hc.symm
    rw [← hsum] at hroot
    exact (Submodule.add_mem_iff_right _ hins).mp hroot
  have horth : ∀ x ∈ s, ∀ y ∈ sᶜ, P.IsOrthogonal x y := by
    intro x hx y hy
    obtain ⟨t, ht, hyt⟩ : ∃ t ∈ d.parts, y ∈ t := by
      have : y ∈ ⋃₀ d.parts := by rw [d.cover]; trivial
      exact Set.mem_sUnion.mp this
    have hts : s ≠ t := by
      intro hst
      subst t
      exact hy hyt
    exact d.orthogonal s hs t ht hts x hx y hyt
  have hout0 : combination outside = 0 :=
    Submodule.disjoint_def.mp (componentSpans_disjoint P horth) _ hout hout_compl
  have outside0 : outside = 0 := by
    apply hli.finsuppLinearCombination_injective
    simpa only [map_zero] using hout0
  intro α hα
  by_contra hαs
  have hne : c α ≠ 0 := Finsupp.mem_support_iff.mp hα
  have : outside α = c α := Finsupp.filter_apply_pos _ _ hαs
  rw [outside0] at this
  exact hne this.symm

private lemma fundamentalRootSubset_restrict_orthogonalPart
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (d : P.OrthogonalDecomposition)
    {base s : Set ι} (hbase : IsFundamentalRootSubset P Set.univ base)
    (hs : s ∈ d.parts) :
    IsFundamentalRootSubset P s (base ∩ s) := by
  classical
  rcases hbase with ⟨_, hli, hexp⟩
  refine ⟨Set.inter_subset_right, ?_, ?_⟩
  · let inclusion : ↥(base ∩ s) ↪ base :=
      ⟨fun α => ⟨α, α.property.1⟩, fun α β h => Subtype.ext (congrArg (fun z : base => (z : ι)) h)⟩
    convert hli.comp inclusion inclusion.injective using 1
    funext α
    rfl
  · intro i hi
    rcases hexp i trivial with hpos | hneg
    · obtain ⟨c, hc, hcpos⟩ := hpos
      have hsupp : ∀ α ∈ c.support, (α : ι) ∈ s :=
        coefficients_support_subset_orthogonalPart P d hs hli hi c hc
      let inclusion : ↥(base ∩ s) ↪ base :=
        ⟨fun α => ⟨α, α.property.1⟩, fun α β h => Subtype.ext (congrArg (fun z : base => (z : ι)) h)⟩
      let c' : ↥(base ∩ s) →₀ ℝ :=
        c.comapDomain inclusion inclusion.injective.injOn
      refine Or.inl ⟨c', ?_, ?_⟩
      · have hrange : (c.support : Set base) ⊆ Set.range inclusion := by
          intro α hα
          exact ⟨⟨α, α.property, hsupp α hα⟩, rfl⟩
        have hemb : c'.embDomain inclusion = c := Finsupp.embDomain_comapDomain hrange
        rw [← hemb, Finsupp.sum_embDomain] at hc
        calc
          P.root i = c'.sum (fun α a => a • P.root (inclusion α)) := hc
          _ = c'.sum (fun α a => a • P.root α) := by
            apply Finsupp.sum_congr
            intro α hα
            rfl
      · intro α hα
        apply hcpos (inclusion α)
        rw [Finsupp.mem_support_iff] at hα ⊢
        simpa only [c', Finsupp.comapDomain_apply] using hα
    · obtain ⟨c, hc, hcneg⟩ := hneg
      have hsupp : ∀ α ∈ c.support, (α : ι) ∈ s :=
        coefficients_support_subset_orthogonalPart P d hs hli hi c hc
      let inclusion : ↥(base ∩ s) ↪ base :=
        ⟨fun α => ⟨α, α.property.1⟩, fun α β h => Subtype.ext (congrArg (fun z : base => (z : ι)) h)⟩
      let c' : ↥(base ∩ s) →₀ ℝ :=
        c.comapDomain inclusion inclusion.injective.injOn
      refine Or.inr ⟨c', ?_, ?_⟩
      · have hrange : (c.support : Set base) ⊆ Set.range inclusion := by
          intro α hα
          exact ⟨⟨α, α.property, hsupp α hα⟩, rfl⟩
        have hemb : c'.embDomain inclusion = c := Finsupp.embDomain_comapDomain hrange
        rw [← hemb, Finsupp.sum_embDomain] at hc
        calc
          P.root i = c'.sum (fun α a => a • P.root (inclusion α)) := hc
          _ = c'.sum (fun α a => a • P.root α) := by
            apply Finsupp.sum_congr
            intro α hα
            rfl
      · intro α hα
        apply hcneg (inclusion α)
        rw [Finsupp.mem_support_iff] at hα ⊢
        simpa only [c', Finsupp.comapDomain_apply] using hα

private lemma localFundamentalRoots_linearIndependent
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (d : P.OrthogonalDecomposition)
    {base : Set ι}
    (hlocal : ∀ s ∈ d.parts, IsFundamentalRootSubset P s (base ∩ s)) :
    LinearIndependent ℝ (fun α : base => P.root α) := by
  classical
  let pieces : d.parts → Set M := fun s => P.root '' (base ∩ (s : Set ι))
  have hpiece : ∀ s, LinearIndepOn ℝ id (pieces s) := by
    intro s
    have hli := (hlocal s s.property).2.1
    have hli' : LinearIndepOn ℝ P.root (base ∩ (s : Set ι)) := hli
    simpa only [pieces] using
      (linearIndepOn_iff_image P.root.injective.injOn).mp hli'
  have hdisjoint : ∀ i, ∀ t : Set d.parts, t.Finite → i ∉ t →
      Disjoint (Submodule.span ℝ (pieces i))
        (⨆ j ∈ t, Submodule.span ℝ (pieces j)) := by
    intro i t ht hit
    let roots : Set ι := ⋃ j ∈ t, (j : Set ι)
    have horth : ∀ x ∈ (i : Set ι), ∀ y ∈ roots, P.IsOrthogonal x y := by
      intro x hx y hy
      simp only [roots, Set.mem_iUnion] at hy
      obtain ⟨j, hy⟩ := hy
      obtain ⟨hjt, hyj⟩ := hy
      have hij : (i : Set ι) ≠ (j : Set ι) := by
        intro hij
        apply hit
        have : i = j := Subtype.ext hij
        exact this ▸ hjt
      exact d.orthogonal i i.property j j.property hij x hx y hyj
    have hbig := componentSpans_disjoint P horth
    apply hbig.mono
    · apply Submodule.span_mono
      exact Set.image_mono Set.inter_subset_right
    · rw [← Submodule.span_iUnion₂]
      apply Submodule.span_mono
      rintro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hx⟩ := hx
      obtain ⟨hjt, hxj⟩ := hx
      obtain ⟨α, hα, rfl⟩ := hxj
      refine ⟨α, ?_, rfl⟩
      exact Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem hjt hα.2)
  have hallPieces : LinearIndepOn ℝ id (⋃ s, pieces s) :=
    linearIndepOn_id_iUnion_finite hpiece hdisjoint
  have himage : P.root '' base = ⋃ s, pieces s := by
    ext x
    constructor
    · rintro ⟨α, hα, rfl⟩
      obtain ⟨s, hs, hαs⟩ : ∃ s ∈ d.parts, α ∈ s := by
        have : α ∈ ⋃₀ d.parts := by rw [d.cover]; trivial
        exact Set.mem_sUnion.mp this
      exact Set.mem_iUnion_of_mem ⟨s, hs⟩ ⟨α, ⟨hα, hαs⟩, rfl⟩
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨s, α, hα, rfl⟩ := hx
      exact ⟨α, hα.1, rfl⟩
  have hroot : LinearIndepOn ℝ P.root base :=
    (linearIndepOn_iff_image P.root.injective.injOn).mpr (himage ▸ hallPieces)
  exact linearIndependent_comp_subtype_iff.mpr hroot

private lemma fundamentalRootSubset_of_restrict_orthogonalParts
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (d : P.OrthogonalDecomposition)
    {base : Set ι}
    (hlocal : ∀ s ∈ d.parts, IsFundamentalRootSubset P s (base ∩ s)) :
    IsFundamentalRootSubset P Set.univ base := by
  classical
  refine ⟨Set.subset_univ base,
    localFundamentalRoots_linearIndependent P d hlocal, ?_⟩
  intro i hi
  obtain ⟨s, hs, his⟩ : ∃ s ∈ d.parts, i ∈ s := by
    have : i ∈ ⋃₀ d.parts := by rw [d.cover]; trivial
    exact Set.mem_sUnion.mp this
  rcases (hlocal s hs).2.2 i his with hpos | hneg
  · obtain ⟨c, hc, hcpos⟩ := hpos
    let inclusion : ↥(base ∩ s) ↪ base :=
      ⟨fun α => ⟨α, α.property.1⟩,
        fun α β h => Subtype.ext (congrArg (fun z : base => (z : ι)) h)⟩
    let c' : base →₀ ℝ := c.embDomain inclusion
    refine Or.inl ⟨c', ?_, ?_⟩
    · rw [Finsupp.sum_embDomain]
      calc
        P.root i = c.sum (fun α a => a • P.root α) := hc
        _ = c.sum (fun α a => a • P.root (inclusion α)) := by
          apply Finsupp.sum_congr
          intro α hα
          rfl
    · intro α hα
      simp only [c', Finsupp.support_embDomain] at hα
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.mp hα
      simpa only [c', Finsupp.embDomain_apply_self] using hcpos β hβ
  · obtain ⟨c, hc, hcneg⟩ := hneg
    let inclusion : ↥(base ∩ s) ↪ base :=
      ⟨fun α => ⟨α, α.property.1⟩,
        fun α β h => Subtype.ext (congrArg (fun z : base => (z : ι)) h)⟩
    let c' : base →₀ ℝ := c.embDomain inclusion
    refine Or.inr ⟨c', ?_, ?_⟩
    · rw [Finsupp.sum_embDomain]
      calc
        P.root i = c.sum (fun α a => a • P.root α) := hc
        _ = c.sum (fun α a => a • P.root (inclusion α)) := by
          apply Finsupp.sum_congr
          intro α hα
          rfl
    · intro α hα
      simp only [c', Finsupp.support_embDomain] at hα
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_map.mp hα
      simpa only [c', Finsupp.embDomain_apply_self] using hcneg β hβ

/-- A set of roots is fundamental globally exactly when its intersections
with the parts of an orthogonal decomposition are fundamental in those parts.

This is the local criterion in GLS3, Theorem 1.8.5(a). -/
public theorem fundamentalRootSubset_iff_restrict_orthogonalParts
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) (d : P.OrthogonalDecomposition)
    (base : Set ι) :
    IsFundamentalRootSubset P Set.univ base ↔
      ∀ s ∈ d.parts, IsFundamentalRootSubset P s (base ∩ s) := by
  letI := Fintype.ofFinite ι
  constructor
  · intro hbase s hs
    exact fundamentalRootSubset_restrict_orthogonalPart P d hbase hs
  · exact fundamentalRootSubset_of_restrict_orthogonalParts P d

@[expose]
public def IsScaledIsometryOnRoots
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) (Q : RootPairing ι₂ ℝ M₂ N₂)
    (base : Set ι) (base₂ : Set ι₂) : Prop :=
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite ι₂
  ∃ e : M ≃ₗ[ℝ] M₂, ∃ c : ℝ, 0 < c ∧
      (∀ x y, Q.RootForm (e x) (e y) = c * P.RootForm x y) ∧
      e '' (P.root '' base) = Q.root '' base₂

private lemma equiv_coroot'_weightEquiv
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    (e : P.Equiv Q) (i : ι) (x : M) :
    Q.coroot' (e.indexEquiv i) (RootPairing.Equiv.weightEquiv P Q e x) = P.coroot' i x := by
  change Q.flip.toLinearMap (Q.coroot (e.indexEquiv i))
      (RootPairing.Equiv.weightEquiv P Q e x) =
    P.flip.toLinearMap (P.coroot i) x
  rw [RootPairing.Equiv.weightEquiv_apply]
  have htranspose := RootPairing.Hom.weight_coweight_transpose_apply
    P Q (Q.coroot (e.indexEquiv i)) e.toHom
  have hcoroot : e.coweightMap (Q.coroot (e.indexEquiv i)) = P.coroot i := by
    simpa using RootPairing.Hom.coroot_coweightMap_apply
      P Q (e.indexEquiv i) e.toHom
  have happ := DFunLike.congr_fun htranspose x
  simpa only [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply,
    RootPairing.Equiv.weightEquiv_apply, hcoroot] using happ

private lemma equiv_rootForm
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    (e : P.Equiv Q) (x y : M) :
    Q.RootForm (RootPairing.Equiv.weightEquiv P Q e x) (RootPairing.Equiv.weightEquiv P Q e y) = P.RootForm x y := by
  rw [Q.rootForm_apply_apply, P.rootForm_apply_apply]
  symm
  exact Fintype.sum_equiv e.indexEquiv
    (fun i => P.coroot' i x * P.coroot' i y)
    (fun j => Q.coroot' j (RootPairing.Equiv.weightEquiv P Q e x) *
      Q.coroot' j (RootPairing.Equiv.weightEquiv P Q e y))
    (fun i => by rw [equiv_coroot'_weightEquiv e, equiv_coroot'_weightEquiv e])

private lemma equiv_implies_scaledIsometryOnRoots
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι₂ ℝ M₂ N₂) [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) (base₂ : Q.Base) (e : P.Equiv Q) :
    IsScaledIsometryOnRoots P Q base.support base₂.support := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite ι₂
  let : MulAction.IsPretransitive Q.weylGroup Q.Base :=
    weylGroup_action_on_bases_transitive Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q.weylGroup
    (RootPairing.Base.mapEquiv e base) base₂
  let e' : P.Equiv Q := RootPairing.Equiv.comp g.1 e
  refine ⟨RootPairing.Equiv.weightEquiv P Q e', 1, by norm_num, ?_, ?_⟩
  · intro x y
    simpa using equiv_rootForm e' x y
  · have hsupp : e'.indexEquiv '' (base.support : Set ι) =
        (base₂.support : Set ι₂) := by
      ext j
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [← hg]
        change e'.indexEquiv i ∈
          (RootPairing.Base.mapAut g.1 (RootPairing.Base.mapEquiv e base)).support
        rw [_root_.RootPairing.Base.mem_mapAut_support,
          RootPairing.Base.mem_mapEquiv_support]
        simpa [e', RootPairing.Equiv.comp, RootPairing.Hom.comp] using hi
      · intro hj
        let i := e'.indexEquiv.symm j
        refine ⟨i, ?_, e'.indexEquiv.apply_symm_apply j⟩
        rw [← hg] at hj
        change j ∈ (RootPairing.Base.mapAut g.1
          (RootPairing.Base.mapEquiv e base)).support at hj
        rw [_root_.RootPairing.Base.mem_mapAut_support,
          RootPairing.Base.mem_mapEquiv_support] at hj
        simpa [i, e', RootPairing.Equiv.comp, RootPairing.Hom.comp] using hj
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨e'.indexEquiv i, hsupp ▸ ⟨i, hi, rfl⟩, ?_⟩
      simpa only [RootPairing.Equiv.weightEquiv_apply] using
        (RootPairing.Hom.root_weightMap_apply P Q i e'.toHom).symm
    · rintro ⟨j, hj, rfl⟩
      rw [← hsupp] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      refine ⟨P.root i, ⟨i, hi, rfl⟩, ?_⟩
      simpa only [RootPairing.Equiv.weightEquiv_apply] using
        RootPairing.Hom.root_weightMap_apply P Q i e'.toHom

private noncomputable def baseSupportEquivOfLinearEquivImage
    {ι ι₂ M M₂ : Type*}
    {P : ι → M} {Q : ι₂ → M₂} (hP : Function.Injective P) (hQ : Function.Injective Q)
    (base : Set ι) (base₂ : Set ι₂) (H : M ≃ M₂)
    (himage : H '' (P '' base) = Q '' base₂) : base ≃ base₂ :=
  (Equiv.Set.image P base hP).trans <|
    (Equiv.Set.image H (P '' base) H.injective).trans <|
      (Equiv.setCongr himage).trans (Equiv.Set.image Q base₂ hQ).symm

private lemma baseSupportEquivOfLinearEquivImage_spec
    {ι ι₂ M M₂ : Type*}
    {P : ι → M} {Q : ι₂ → M₂} (hP : Function.Injective P) (hQ : Function.Injective Q)
    (base : Set ι) (base₂ : Set ι₂) (H : M ≃ M₂)
    (himage : H '' (P '' base) = Q '' base₂) (i : base) :
    H (P i) = Q (baseSupportEquivOfLinearEquivImage hP hQ base base₂ H himage i) := by
  let rootP := Equiv.Set.image P base hP
  let mapH := Equiv.Set.image H (P '' base) H.injective
  let cast := Equiv.setCongr himage
  let rootQ := Equiv.Set.image Q base₂ hQ
  let z : Q '' base₂ := cast (mapH (rootP i))
  change H (P i) = Q (rootQ.symm z)
  have hz := congrArg Subtype.val (rootQ.apply_symm_apply z)
  change Q (rootQ.symm z) = H (P i) at hz
  exact hz.symm

private lemma scaledIsometryOnRoots_implies_equiv
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι₂ ℝ M₂ N₂) [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) (base₂ : Q.Base)
    (hscaled : IsScaledIsometryOnRoots P Q base.support base₂.support) :
    Nonempty (P.Equiv Q) := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite ι₂
  rcases hscaled with ⟨H, c, hc, hform, himage⟩
  let eBase : base.support ≃ base₂.support :=
    baseSupportEquivOfLinearEquivImage P.root.injective Q.root.injective
      (base.support : Set ι) (base₂.support : Set ι₂) H.toEquiv himage
  have heRoot (i : base.support) : H (P.root i) = Q.root (eBase i) := by
    exact baseSupportEquivOfLinearEquivImage_spec P.root.injective Q.root.injective
      (base.support : Set ι) (base₂.support : Set ι₂) H.toEquiv himage i
  refine ⟨base.equivOfCartanMatrixEq base₂ eBase ?_⟩
  intro i j
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  simp only [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def]
  change algebraMap ℤ ℝ (Q.pairingIn ℤ (eBase i) (eBase j)) =
    algebraMap ℤ ℝ (P.pairingIn ℤ i j)
  rw [Q.algebraMap_pairingIn, P.algebraMap_pairingIn]
  have hP := _root_.RootPairing.two_mul_rootForm_apply_root P j (P.root i)
  have hQ := _root_.RootPairing.two_mul_rootForm_apply_root Q (eBase j) (Q.root (eBase i))
  rw [← heRoot i, ← heRoot j, hform, hform] at hQ
  rw [heRoot i] at hQ
  have hnorm : 0 < P.RootForm (P.root j) (P.root j) :=
    P.rootForm_pos_of_ne_zero (by simp) (P.ne_zero j)
  change 2 * P.RootForm (P.root i) (P.root j) =
    P.pairing i j * P.RootForm (P.root j) (P.root j) at hP
  change 2 * (c * P.RootForm (P.root i) (P.root j)) =
    Q.pairing (eBase i) (eBase j) *
      (c * P.RootForm (P.root j) (P.root j)) at hQ
  have hnonzero : c * P.RootForm (P.root j) (P.root j) ≠ 0 :=
    mul_ne_zero (ne_of_gt hc) (ne_of_gt hnorm)
  apply mul_right_cancel₀ hnonzero
  calc
    Q.pairing (eBase i) (eBase j) *
        (c * P.RootForm (P.root j) (P.root j)) =
      2 * (c * P.RootForm (P.root i) (P.root j)) := hQ.symm
    _ = c * (2 * P.RootForm (P.root i) (P.root j)) := by ring
    _ = c * (P.pairing i j * P.RootForm (P.root j) (P.root j)) := by rw [hP]
    _ = P.pairing i j *
        (c * P.RootForm (P.root j) (P.root j)) := by ring

/-- For finite reduced crystallographic root systems, equivalence is equivalent
to a scaled isometry carrying one specified base to the other.

This is GLS3, Theorem 1.8.5(b). -/
public theorem nonempty_equiv_iff_isScaledIsometryOnRoots
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι₂ ℝ M₂ N₂) [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) (base₂ : Q.Base) :
    Nonempty (P.Equiv Q) ↔
      IsScaledIsometryOnRoots P Q base.support base₂.support := by
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite ι₂
  constructor
  · rintro ⟨e⟩
    exact equiv_implies_scaledIsometryOnRoots P Q base base₂ e
  · exact scaledIsometryOnRoots_implies_equiv P Q base base₂

@[expose]
public def PreservesRootPairingStructure
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) (Q : RootPairing ι₂ ℝ M₂ N₂)
    (f : ι ≃ ι₂) : Prop :=
  (∀ α, f (P.reflectionPerm α α) = Q.reflectionPerm (f α) (f α)) ∧
    ∀ α β γ, P.root γ = P.root α + P.root β ↔
      Q.root (f γ) = Q.root (f α) + Q.root (f β)

@[expose]
public def PreservesRootAddition
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) (Q : RootPairing ι₂ ℝ M₂ N₂)
    (f : ι ≃ ι₂) : Prop :=
  ∀ α β γ, P.root γ = P.root α + P.root β ↔
    Q.root (f γ) = Q.root (f α) + Q.root (f β)

/-- An equivalence of root pairings preserves all additive relations among
roots. This is the forward implication in the additive characterization from
Theorem 1.8.5. -/
public theorem PreservesRootPairingStructure.of_equiv
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    (e : P.Equiv Q) : PreservesRootPairingStructure P Q e.toHom.indexEquiv := by
  constructor
  · intro α
    apply Q.root.injective
    rw [← RootPairing.Hom.root_weightMap_apply P Q (P.reflectionPerm α α) e.toHom]
    simp only [P.root_reflectionPerm, P.reflection_apply_self, map_neg,
      RootPairing.Hom.root_weightMap_apply]
    simp
  · intro α β γ
    constructor
    · intro h
      have hmap := congrArg e.weightEquiv h
      simpa only [RootPairing.Equiv.weightEquiv_apply,
        RootPairing.Hom.root_weightMap_apply, map_add] using hmap
    · intro h
      apply e.weightEquiv.injective
      simpa only [RootPairing.Equiv.weightEquiv_apply,
        RootPairing.Hom.root_weightMap_apply, map_add] using h

/-- The existence of a root-pairing equivalence inducing a prescribed index
bijection implies preservation of all additive relations among roots. -/
public theorem PreservesRootPairingStructure.of_exists_equiv
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    {f : ι ≃ ι₂} (h : ∃ e : P.Equiv Q, e.toHom.indexEquiv = f) :
    PreservesRootPairingStructure P Q f := by
  obtain ⟨e, rfl⟩ := h
  exact PreservesRootPairingStructure.of_equiv e

public theorem PreservesRootAddition.of_equiv
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    (e : P.Equiv Q) : PreservesRootAddition P Q e.toHom.indexEquiv := by
  exact (PreservesRootPairingStructure.of_equiv e).2

public theorem PreservesRootAddition.of_exists_equiv
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    {f : ι ≃ ι₂} (h : ∃ e : P.Equiv Q, e.toHom.indexEquiv = f) :
    PreservesRootAddition P Q f := by
  exact (PreservesRootPairingStructure.of_exists_equiv h).2

private lemma preservesRootPairingStructure_symm
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) :
    PreservesRootPairingStructure Q P f.symm := by
  constructor
  · intro α
    apply f.injective
    rw [f.apply_symm_apply]
    rw [hf.1 (f.symm α)]
    simp
  · intro α β γ
    simpa using (hf.2 (f.symm α) (f.symm β) (f.symm γ)).symm

private lemma preservesRootAddition_linearIndependent_pair_iff
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) (i j : ι) :
    LinearIndependent ℝ ![P.root i, P.root j] ↔
      LinearIndependent ℝ ![Q.root (f i), Q.root (f j)] := by
  letI := P.indexNeg
  letI := Q.indexNeg
  rw [RootPairing.IsReduced.linearIndependent_iff P,
    RootPairing.IsReduced.linearIndependent_iff Q]
  constructor
  · rintro ⟨hij, hineg⟩
    refine ⟨fun h => hij (f.injective h), ?_⟩
    intro hroot
    have hidx : f i = -(f j) := by
      apply Q.root.injective
      simpa using hroot
    change f i = Q.reflectionPerm (f j) (f j) at hidx
    rw [← hf.1 j] at hidx
    apply hineg
    have := congrArg P.root (f.injective hidx)
    simpa using this
  · rintro ⟨hij, hineg⟩
    refine ⟨fun h => hij (congrArg f h), ?_⟩
    intro hroot
    have hidx : i = P.reflectionPerm j j := by
      apply P.root.injective
      simpa using hroot
    apply hineg
    have := congrArg Q.root (congrArg f hidx)
    rw [hf.1 j] at this
    simpa using this

private lemma preservesRootAddition_map_root_add_nsmul
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    {Q : RootPairing ι₂ ℝ M₂ N₂}
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    {i j k : ι} (hlin : LinearIndependent ℝ ![P.root i, P.root j])
    {n : ℕ} (hk : P.root k = P.root j + n • P.root i) :
    Q.root (f k) = Q.root (f j) + n • Q.root (f i) := by
  induction n using Nat.rec generalizing k with
  | zero => simpa using congrArg (fun x => Q.root (f x)) (P.root.injective (by simpa using hk))
  | succ n ih =>
      have hmem : P.root j + n • P.root i ∈ range P.root := by
        rw [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
        have htop : n + 1 ≤ P.chainTopCoeff i j := by
          rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
          exact ⟨k, by simpa [Nat.succ_eq_add_one] using hk⟩
        omega
      obtain ⟨l, hl⟩ := hmem
      have hsum : P.root k = P.root l + P.root i := by
        rw [hk, hl]
        simp [Nat.succ_eq_add_one, add_nsmul]
        abel
      rw [(hf.2 l i k).mp hsum, ih hl]
      simp [Nat.succ_eq_add_one, add_nsmul]
      abel

private lemma preservesRootAddition_root_add_nsmul_mem_range_iff
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsCrystallographic] [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    {i j : ι} (hlin : LinearIndependent ℝ ![P.root i, P.root j]) (n : ℕ) :
    P.root j + n • P.root i ∈ range P.root ↔
      Q.root (f j) + n • Q.root (f i) ∈ range Q.root := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨f k, ?_⟩
    exact preservesRootAddition_map_root_add_nsmul hf hlin hk
  · rintro ⟨k, hk⟩
    have hlinQ := (preservesRootAddition_linearIndependent_pair_iff hf i j).mp hlin
    have hmap := preservesRootAddition_map_root_add_nsmul (preservesRootPairingStructure_symm hf) hlinQ hk
    refine ⟨f.symm k, ?_⟩
    simpa using hmap

private lemma preservesRootAddition_root_sub_nsmul_mem_range_iff
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsCrystallographic] [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    {i j : ι} (hlin : LinearIndependent ℝ ![P.root i, P.root j]) (n : ℕ) :
    P.root j - n • P.root i ∈ range P.root ↔
      Q.root (f j) - n • Q.root (f i) ∈ range Q.root := by
  have hlinNeg : LinearIndependent ℝ
      ![P.root (P.reflectionPerm i i), P.root j] := by
    simpa using hlin
  have h := preservesRootAddition_root_add_nsmul_mem_range_iff hf hlinNeg n
  have hfneg : Q.root (f (P.reflectionPerm i i)) = -Q.root (f i) := by
    rw [hf.1 i]
    simp
  rw [show P.root (P.reflectionPerm i i) = -P.root i by simp, hfneg] at h
  simpa [sub_eq_add_neg] using h

private lemma preservesRootAddition_chain_coeff_eq
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsCrystallographic] [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    {i j : ι} (hlin : LinearIndependent ℝ ![P.root i, P.root j]) :
    P.chainTopCoeff i j = Q.chainTopCoeff (f i) (f j) ∧
      P.chainBotCoeff i j = Q.chainBotCoeff (f i) (f j) := by
  have hlinQ := (preservesRootAddition_linearIndependent_pair_iff hf i j).mp hlin
  constructor
  · apply le_antisymm
    · rw [← Q.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinQ]
      rw [← preservesRootAddition_root_add_nsmul_mem_range_iff hf hlin]
      exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mpr le_rfl
    · rw [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin]
      rw [preservesRootAddition_root_add_nsmul_mem_range_iff hf hlin]
      exact (Q.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlinQ).mpr le_rfl
  · apply le_antisymm
    · rw [← Q.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinQ]
      rw [← preservesRootAddition_root_sub_nsmul_mem_range_iff hf hlin]
      exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).mpr le_rfl
    · rw [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin]
      rw [preservesRootAddition_root_sub_nsmul_mem_range_iff hf hlin]
      exact (Q.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlinQ).mpr le_rfl

private lemma preservesRootAddition_pairingIn_eq
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsCrystallographic] [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) (i j : ι) :
    Q.pairingIn ℤ (f i) (f j) = P.pairingIn ℤ i j := by
  letI := P.indexNeg
  letI := Q.indexNeg
  by_cases hlin : LinearIndependent ℝ ![P.root j, P.root i]
  · have hlinQ := (preservesRootAddition_linearIndependent_pair_iff hf j i).mp hlin
    obtain ⟨htop, hbot⟩ := preservesRootAddition_chain_coeff_eq hf hlin
    rw [← P.chainBotCoeff_sub_chainTopCoeff hlin,
      ← Q.chainBotCoeff_sub_chainTopCoeff hlinQ, htop, hbot]
  · rw [RootPairing.IsReduced.linearIndependent_iff P] at hlin
    by_cases hij : j = i
    · subst j
      simp
    · have hineg : P.root j = -P.root i := by
        apply not_ne_iff.mp
        intro hne
        exact hlin ⟨hij, hne⟩
      have hji : j = P.reflectionPerm i i := by
        rw [P.root_eq_neg_iff] at hineg
        exact hineg
      subst j
      rw [hf.1 i]
      simp

private lemma preservesRootAddition_pairing_eq
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsCrystallographic] [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) (i j : ι) :
    Q.pairing (f i) (f j) = P.pairing i j := by
  rw [← Q.algebraMap_pairingIn ℤ, ← P.algebraMap_pairingIn ℤ,
    preservesRootAddition_pairingIn_eq hf]

private lemma preservesRootAddition_image_base_linearIndependent
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) :
    LinearIndependent ℝ (fun i : base.support => Q.root (f i)) := by
  classical
  let L : M₂ →ₗ[ℝ] (base.support → ℝ) :=
    LinearMap.pi fun j : base.support => Q.coroot' (f j)
  apply LinearIndependent.of_comp L
  have hrows : LinearIndependent ℝ
      (fun i : base.support => fun j : base.support => P.pairing i j) := by
    have hcartan : LinearIndependent ℝ
        (fun i => (base.cartanMatrixIn ℝ) i) := by
      apply Matrix.linearIndependent_rows_of_det_ne_zero
      rw [← Matrix.nondegenerate_iff_det_ne_zero]
      exact base.cartanMatrixIn_nondegenerate ℝ
    convert hcartan using 1
    ext i j
    simpa [RootPairing.Base.cartanMatrixIn_def] using
      (P.algebraMap_pairingIn ℝ i j).symm
  convert hrows using 1
  ext i j
  change Q.coroot' (f j) (Q.root (f i)) = P.pairing i j
  rw [Q.root_coroot'_eq_pairing, preservesRootAddition_pairing_eq hf]

private lemma preservesRootAddition_isPos_image_mem_closure
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    {Q : RootPairing ι₂ ℝ M₂ N₂}
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    {i : ι} (hi : base.IsPos i) :
    Q.root (f i) ∈ AddSubmonoid.closure
      (Q.root '' (f '' (base.support : Set ι))) := by
  apply hi.induction_on_add
  · intro j hj
    exact AddSubmonoid.subset_closure ⟨f j, ⟨j, hj, rfl⟩, rfl⟩
  · intro j l k hk hj hl
    rw [(hf.2 j l k).mp hk]
    exact AddSubmonoid.add_mem _ hj
      (AddSubmonoid.subset_closure ⟨f l, ⟨l, hl, rfl⟩, rfl⟩)

private lemma preservesRootAddition_image_root_mem_or_neg_mem_closure
    {ι ι₂ M N M₂ N₂ : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    {Q : RootPairing ι₂ ℝ M₂ N₂}
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    (i : ι₂) :
    Q.root i ∈ AddSubmonoid.closure
        (Q.root '' (f '' (base.support : Set ι))) ∨
      -Q.root i ∈ AddSubmonoid.closure
        (Q.root '' (f '' (base.support : Set ι))) := by
  letI := P.indexNeg
  letI := Q.indexNeg
  let j := f.symm i
  rcases RootPairing.Base.IsPos.or_neg base j with hj | hj
  · left
    simpa [j] using preservesRootAddition_isPos_image_mem_closure base hf hj
  · right
    have hmem := preservesRootAddition_isPos_image_mem_closure base hf hj
    have hfneg : Q.root (f (-j)) = -Q.root (f j) := by
      change Q.root (f (P.reflectionPerm j j)) = -Q.root (f j)
      rw [hf.1 j]
      simp
    rw [hfneg] at hmem
    simpa [j] using hmem

private noncomputable def preservesRootAdditionImageBase
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) : Q.Base :=
  RootPairing.Base.mk' Q (f '' (base.support : Set ι))
    (LinearIndepOn.image_of_comp f Q.root
      (preservesRootAddition_image_base_linearIndependent base hf))
    (fun i => preservesRootAddition_image_root_mem_or_neg_mem_closure base hf i)

private lemma preservesRootAdditionImageBase_support
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) :
    ((preservesRootAdditionImageBase base hf).support : Set ι₂) =
      f '' (base.support : Set ι) := by
  ext i
  change i ∈ (Set.toFinite (f '' (base.support : Set ι))).toFinset ↔ _
  simp only [Set.Finite.mem_toFinset]

private noncomputable def preservesRootAdditionImageBaseSupportEquiv
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) :
    base.support ≃ (preservesRootAdditionImageBase base hf).support :=
  (Equiv.Set.image f (base.support : Set ι) f.injective).trans
    (Equiv.setCongr (preservesRootAdditionImageBase_support base hf).symm)

private lemma preservesRootAdditionImageBaseSupportEquiv_val
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f)
    (i : base.support) :
    (preservesRootAdditionImageBaseSupportEquiv base hf i : ι₂) = f i := by
  rfl

public theorem PreservesRootPairingStructure.exists_equiv
    {ι ι₂ M N M₂ N₂ : Type*} [Fintype ι] [Fintype ι₂]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (Q : RootPairing ι₂ ℝ M₂ N₂) [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]
    (base : P.Base) (f : ι ≃ ι₂) (hf : PreservesRootPairingStructure P Q f) :
    ∃ e : P.Equiv Q, e.toHom.indexEquiv = f := by
  let base₂ : Q.Base := preservesRootAdditionImageBase base hf
  let eBase : base.support ≃ base₂.support := preservesRootAdditionImageBaseSupportEquiv base hf
  have hcartan : ∀ i j, base₂.cartanMatrix (eBase i) (eBase j) =
      base.cartanMatrix i j := by
    intro i j
    simp only [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def]
    change Q.pairingIn ℤ (f i) (f j) = P.pairingIn ℤ i j
    exact preservesRootAddition_pairingIn_eq hf i j
  let e : P.Equiv Q := base.equivOfCartanMatrixEq base₂ eBase hcartan
  have heBase (i : base.support) : e.toHom.indexEquiv i = eBase i := by
    apply Q.root.injective
    rw [← RootPairing.Hom.root_weightMap_apply P Q i e.toHom]
    change (base.toWeightBasis.equiv base₂.toWeightBasis eBase) (P.root i) =
      Q.root (eBase i)
    simp [Module.Basis.equiv]
  refine ⟨e, ?_⟩
  apply Equiv.ext
  intro i
  apply base₂.injective_pairingIn
  funext k
  let j : base.support := eBase.symm k
  have hj : eBase j = k := eBase.apply_symm_apply k
  have hk : (k : ι₂) = f j := by
    rw [← hj]
    exact preservesRootAdditionImageBaseSupportEquiv_val base hf j
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  change algebraMap ℤ ℝ (Q.pairingIn ℤ (e.toHom.indexEquiv i) k) =
    algebraMap ℤ ℝ (Q.pairingIn ℤ (f i) k)
  rw [Q.algebraMap_pairingIn, Q.algebraMap_pairingIn, hk]
  have heBaseF : e.toHom.indexEquiv j = f j :=
    (heBase j).trans (preservesRootAdditionImageBaseSupportEquiv_val base hf j)
  rw [← heBaseF]
  calc
    Q.pairing (e.toHom.indexEquiv i) (e.toHom.indexEquiv j) =
        P.pairing i j := RootPairing.Equiv.pairing_eq e i j
    _ = Q.pairing (f i) (f j) := (preservesRootAddition_pairing_eq hf i j).symm
    _ = Q.pairing (f i) (e.toHom.indexEquiv j) := by rw [heBaseF]

private lemma heightMaximum_isPos
    {ι M N : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} (base : P.Base) {highest : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest) : base.IsPos highest := by
  let : Nonempty ι := ⟨highest⟩
  obtain ⟨j, hj⟩ := base.support_nonempty
  rw [base.isPos_iff]
  have := hmax j
  rw [base.height_one_of_mem_support hj] at this
  omega

private lemma heightMaximum_pairingIn_nonneg
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    (base : P.Base) {highest : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest)
    {j : ι} (hj : j ∈ base.support) :
    0 ≤ P.pairingIn ℤ highest j := by
  have hpos := heightMaximum_isPos base hmax
  by_contra hneg
  have hroot_ne : P.root highest ≠ -P.root j := by
    intro heq
    have hindex : highest = P.reflectionPerm j j := P.root_eq_neg_iff.mp heq
    have hnegheight := base.height_reflectionPerm_self j
    change base.height (P.reflectionPerm j j) = -base.height j at hnegheight
    rw [hindex, base.isPos_iff, hnegheight,
      base.height_one_of_mem_support hj] at hpos
    omega
  obtain ⟨k, hk⟩ :=
    P.root_add_root_mem_of_pairingIn_neg (lt_of_not_ge hneg) hroot_ne
  have hkheight := base.height_add hk
  have := hmax k
  rw [hkheight, base.height_one_of_mem_support hj] at this
  omega

private lemma heightMaximum_coefficients_pos
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) {highest : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest) :
    ∃ coefficients : ι → ℤ, coefficients.support ⊆ base.support ∧
      (∀ j ∈ base.support, 0 < coefficients j) ∧
      P.root highest =
        ∑ j ∈ base.support, coefficients j • P.root j := by
  have hpos := heightMaximum_isPos base hmax
  obtain ⟨coefficients, hsupport, hsign, hroot⟩ :=
    base.exists_root_eq_sum_int highest
  have hcoefficients_pos : 0 < coefficients := hsign.resolve_right (fun hnegative => by
    have hheight_negative : base.height highest < 0 := by
      rw [base.height_eq_sum hroot]
      apply Finset.sum_neg'
      · intro j hj
        exact hnegative.le j
      · obtain ⟨j, hj⟩ := (Pi.lt_def.mp hnegative).2
        have hj_support : j ∈ coefficients.support := Function.mem_support.mpr hj.ne
        exact ⟨j, hsupport hj_support, hj⟩
    exact (not_lt_of_ge (base.isPos_iff.mp hpos).le) hheight_negative)
  obtain ⟨i, hi⟩ := (Pi.lt_def.mp hcoefficients_pos).2
  have hi_support : i ∈ coefficients.support := Function.mem_support.mpr hi.ne'
  let initial : base.support := ⟨i, hsupport hi_support⟩
  have hall (j : base.support) : 0 < coefficients j := by
    apply base.induction_on_cartanMatrix
      (p := fun k => 0 < coefficients k) (i := initial)
    · exact hi
    · intro k l hk hcart
      by_cases hfl : 0 < coefficients l
      · exact hfl
      have hfl_nonneg : 0 ≤ coefficients l := hcoefficients_pos.le l
      have hfl_zero : coefficients l = 0 := le_antisymm (not_lt.mp hfl) hfl_nonneg
      have hkl : k ≠ l := by
        intro hkl
        exact hfl (hkl ▸ hk)
      have hpair_eq :
          P.pairingIn ℤ highest l =
            ∑ m ∈ base.support, coefficients m * P.pairingIn ℤ m l := by
        apply FaithfulSMul.algebraMap_injective ℤ ℝ
        simp_rw [P.algebraMap_pairingIn ℤ, map_sum, map_mul,
          P.algebraMap_pairingIn ℤ, ← P.root_coroot'_eq_pairing]
        simp [hroot]
      have hsum_negative :
          (∑ m ∈ base.support, coefficients m * P.pairingIn ℤ m l) < 0 := by
        apply Finset.sum_neg'
        · intro m hm
          by_cases hml : m = l
          · subst m
            simp [hfl_zero]
          · have hsub : (⟨m, hm⟩ : base.support) ≠ l := by
              intro heq
              exact hml (congrArg Subtype.val heq)
            exact mul_nonpos_of_nonneg_of_nonpos (hcoefficients_pos.le m)
              (base.cartanMatrix_le_zero_of_ne ⟨m, hm⟩ l hsub)
        · refine ⟨k, k.property, ?_⟩
          have hcart' : base.cartanMatrix k l ≠ 0 := by
            intro hz
            exact hcart (base.cartanMatrix_apply_eq_zero_iff_symm.mp hz)
          have hcart_le := base.cartanMatrix_le_zero_of_ne k l hkl
          have hcart_negative : base.cartanMatrix k l < 0 :=
            lt_of_le_of_ne hcart_le hcart'
          exact mul_neg_of_pos_of_neg hk hcart_negative
      have hpair_negative : P.pairingIn ℤ highest l < 0 :=
        hpair_eq ▸ hsum_negative
      exact False.elim
        ((not_lt_of_ge (heightMaximum_pairingIn_nonneg base hmax l.property))
          hpair_negative)
  exact ⟨coefficients, hsupport, fun j hj => hall ⟨j, hj⟩, hroot⟩

private lemma simplePairing_heightMaximum_nonneg
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    (base : P.Base) {highest : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest)
    {j : ι} (hj : j ∈ base.support) :
    0 ≤ P.pairingIn ℤ j highest := by
  have hhj := heightMaximum_pairingIn_nonneg base hmax hj
  by_cases hjh : P.pairingIn ℤ j highest = 0
  · simp [hjh]
  have hhjne : P.pairingIn ℤ highest j ≠ 0 := by
    intro hhjzero
    exact hjh (P.pairingIn_eq_zero_iff.mp hhjzero)
  have hhjpos : 0 < P.pairingIn ℤ highest j :=
    lt_of_le_of_ne hhj hhjne.symm
  exact (P.zero_lt_pairingIn_iff' ℤ).mp hhjpos |>.le

private lemma heightMaximum_unique
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) {highest highest' : ι}
    (hmax : ∀ α, base.height α ≤ base.height highest)
    (hmax' : ∀ α, base.height α ≤ base.height highest') :
    highest' = highest := by
  by_contra hne
  obtain ⟨coefficients, _, hcoefficients_pos, hroot⟩ :=
    heightMaximum_coefficients_pos base hmax'
  have hpair_eq :
      P.pairingIn ℤ highest' highest =
        ∑ j ∈ base.support, coefficients j * P.pairingIn ℤ j highest := by
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    simp_rw [P.algebraMap_pairingIn ℤ, map_sum, map_mul,
      P.algebraMap_pairingIn ℤ, ← P.root_coroot'_eq_pairing]
    simp [hroot]
  have hpair_pos : 0 < P.pairingIn ℤ highest' highest := by
    rw [hpair_eq]
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hcoefficients_pos j hj).le
        (simplePairing_heightMaximum_nonneg base hmax hj)
    · obtain ⟨j, hj, hjne⟩ :=
        base.exists_mem_support_pos_pairingIn_ne_zero highest
      have hjnonneg := simplePairing_heightMaximum_nonneg base hmax hj
      refine ⟨j, hj, mul_pos (hcoefficients_pos j hj) ?_⟩
      exact lt_of_le_of_ne hjnonneg hjne.symm
  obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair_pos hne
  have hkheight := base.height_sub hk
  have heqheight : base.height highest' = base.height highest :=
    le_antisymm (hmax highest') (hmax' highest)
  exact base.height_ne_zero k (by rw [hkheight, heqheight, sub_self])

private lemma rootIndex_nonempty_of_isRootSystem_isIrreducible
    {ι M N : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsIrreducible] :
    Nonempty ι := by
  have : Nontrivial M := RootPairing.IsIrreducible.nontrivial P
  by_contra hnonempty
  have hrange : Set.range P.root = ∅ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (hnonempty ⟨i⟩).elim
    · simp
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hxspan : x ∈ Submodule.span ℝ (Set.range P.root) := by
    rw [RootPairing.IsRootSystem.span_root_eq_top (P := P)]
    exact Submodule.mem_top
  rw [hrange, Submodule.span_empty] at hxspan
  exact hx hxspan

private lemma heightMinimum_unique
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible]
    (base : P.Base) {lowest lowest' : ι}
    (hmin : ∀ α, base.height lowest ≤ base.height α)
    (hmin' : ∀ α, base.height lowest' ≤ base.height α) :
    lowest' = lowest := by
  letI := P.indexNeg
  have hmax : ∀ α, base.height α ≤ base.height (-lowest) := by
    intro α
    have h := hmin (-α)
    have hnegα := base.height_reflectionPerm_self α
    have hneglow := base.height_reflectionPerm_self lowest
    change base.height (-α) = -base.height α at hnegα
    change base.height (-lowest) = -base.height lowest at hneglow
    omega
  have hmax' : ∀ α, base.height α ≤ base.height (-lowest') := by
    intro α
    have h := hmin' (-α)
    have hnegα := base.height_reflectionPerm_self α
    have hneglow := base.height_reflectionPerm_self lowest'
    change base.height (-α) = -base.height α at hnegα
    change base.height (-lowest') = -base.height lowest' at hneglow
    omega
  have hneg : -lowest' = -lowest := heightMaximum_unique base hmax hmax'
  exact neg_injective hneg

/-- In a finite irreducible reduced crystallographic root system, the height
relative to any base is maximized and minimized at unique roots. This is the
uniqueness part of GLS3, Theorem 1.8.5(d). -/
private lemma RootPairing.Base.heightMaximum_unique_existence
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) :
    ∃! highest : ι, ∀ α, base.height α ≤ base.height highest := by
  letI := Fintype.ofFinite ι
  let : Nonempty ι := rootIndex_nonempty_of_isRootSystem_isIrreducible (P := P)
  obtain ⟨highest, hhighest⟩ := Finite.exists_max base.height
  exact ⟨highest, hhighest, fun y hy => heightMaximum_unique base hhighest hy⟩

private lemma RootPairing.Base.heightMinimum_unique_existence
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] (base : P.Base) :
    ∃! lowest : ι, ∀ α, base.height lowest ≤ base.height α := by
  letI := Fintype.ofFinite ι
  let : Nonempty ι := rootIndex_nonempty_of_isRootSystem_isIrreducible (P := P)
  obtain ⟨lowest, hlowest⟩ := Finite.exists_min base.height
  exact ⟨lowest, hlowest, fun y hy => heightMinimum_unique base hlowest hy⟩

end

open SimpleGraph

set_option maxHeartbeats 800000 in
/-- A connected positive-definite Cartan support has at most one vertex of
degree three.  The affine-`D` row contradiction is derived from the ordinary
support graph; no row predicate or classification certificate is assumed. -/
public lemma cartanSupport_degree_three_unique_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef) :
    ∀ c₁ c₂,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c₁ = 3 →
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c₂ = 3 →
      c₁ = c₂ := by
  classical
  intro c₁ c₂ hdeg₁ hdeg₂
  by_contra hneq
  apply not_cartan_support_two_degree_three_vertices_of_diagonal_mul_posDef
    A d hdiag hrank hconn hpos c₁ c₂ hneq hdeg₁ hdeg₂
  intro p hp a₁ a₂ b₁ b₂ ha₁₂ hb₁₂ hab₁ hab₂ ha₂b₁ ha₂b₂
    ha₁adj ha₂adj hb₁adj hb₂adj ha₁off ha₂off hb₁off hb₂off
    e hepath hea₁ hea₂ heb₁ heb₂
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hpNil : ¬p.Nil := by
    intro hnil
    exact hneq (hp.nil_iff_eq.mp hnil)
  have hm : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpNil
  have hacyc : G.IsAcyclic := by
    exact cartanSupport_isAcyclic A d hdiag hrank hpos
  have hepath' : ∀ i : Fin (p.length + 1),
      e ⟨i.val, by omega⟩ = p.getVert i.val := by
    intro i
    have hidx : Fin.castAdd 4 i = (⟨i.val, by omega⟩ : Fin (p.length + 5)) :=
      Fin.ext rfl
    rw [← hidx]
    exact hepath i
  have hea₁' : e ⟨p.length + 1, by omega⟩ = a₁ := by
    have hidx : Fin.natAdd (p.length + 1) (0 : Fin 4) =
        (⟨p.length + 1, by omega⟩ : Fin (p.length + 5)) := Fin.ext (by simp)
    rw [← hidx]
    exact hea₁
  have hea₂' : e ⟨p.length + 2, by omega⟩ = a₂ := by
    have hidx : Fin.natAdd (p.length + 1) (1 : Fin 4) =
        (⟨p.length + 2, by omega⟩ : Fin (p.length + 5)) := Fin.ext (by simp)
    rw [← hidx]
    exact hea₂
  have heb₁' : e ⟨p.length + 3, by omega⟩ = b₁ := by
    have hidx : Fin.natAdd (p.length + 1) (2 : Fin 4) =
        (⟨p.length + 3, by omega⟩ : Fin (p.length + 5)) := Fin.ext (by simp)
    rw [← hidx]
    exact heb₁
  have heb₂' : e ⟨p.length + 4, by omega⟩ = b₂ := by
    have hidx : Fin.natAdd (p.length + 1) (3 : Fin 4) =
        (⟨p.length + 4, by omega⟩ : Fin (p.length + 5)) := Fin.ext (by simp)
    rw [← hidx]
    exact heb₂
  have he0 : e 0 = c₁ := by
    have h := hepath' (0 : Fin (p.length + 1))
    simpa using h
  have hem : e ⟨p.length, by omega⟩ = c₂ := by
    have h := hepath' (⟨p.length, by omega⟩ : Fin (p.length + 1))
    simpa using h
  have hsupport := simpleGraph_central_path_plus_four_offpath_support
    p hp hpNil hacyc ha₁₂ hb₁₂ hab₁ hab₂ ha₂b₁ ha₂b₂
      ha₁adj ha₂adj hb₁adj hb₂adj ha₁off ha₂off hb₁off hb₂off
      e hepath' hea₁' hea₂' heb₁' heb₂'
  have hsimple := cartanSupport_path_from_degree_three_entries_eq_neg_one
    A d hdiag hrank hpos hp hpNil ha₁₂ ha₁adj ha₂adj ha₁off ha₂off hdeg₁
  have hleafA₁ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₁ a₁ hdeg₁ ha₁adj
  have hleafA₂ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₁ a₂ hdeg₁ ha₂adj
  have hleafB₁ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₂ b₁ hdeg₂ hb₁adj
  have hleafB₂ := cartanSupport_degree_three_edge_entries_eq_neg_one
    A d hdiag hrank hpos c₂ b₂ hdeg₂ hb₂adj
  have hleft₁ : A (e 0) (e 1) = -1 := by
    have he1 : e (1 : Fin (p.length + 5)) = p.getVert 1 := by
      have hidx : (1 : Fin (p.length + 5)) =
          (⟨1, by omega⟩ : Fin (p.length + 5)) := Fin.ext (by simp)
      rw [hidx]
      exact hepath' (⟨1, by omega⟩ : Fin (p.length + 1))
    have hs : A c₁ (p.getVert 1) = -1 := by
      simpa only [p.getVert_zero] using (hsimple (⟨0, hm⟩ : Fin p.length)).1
    calc
      A (e 0) (e 1) = A c₁ (p.getVert 1) := congrArg₂ A he0 he1
      _ = -1 := hs
  have hright₁ :
      A (e ⟨p.length, by omega⟩) (e ⟨p.length - 1, by omega⟩) = -1 := by
    have heprev : e ⟨p.length - 1, by omega⟩ = p.getVert (p.length - 1) :=
      hepath' (⟨p.length - 1, by omega⟩ : Fin (p.length + 1))
    have hs : A c₂ (p.getVert (p.length - 1)) = -1 := by
      have h := (hsimple (⟨p.length - 1, by omega⟩ : Fin p.length)).2
      rw [Nat.sub_add_cancel (by omega), p.getVert_length] at h
      exact h
    calc
      A (e ⟨p.length, by omega⟩) (e ⟨p.length - 1, by omega⟩) =
          A c₂ (p.getVert (p.length - 1)) := congrArg₂ A hem heprev
      _ = -1 := hs
  have ha₁ : A (e 0) (e ⟨p.length + 1, by omega⟩) = -1 := by
    rw [he0, hea₁']
    exact hleafA₁.1
  have ha₂ : A (e 0) (e ⟨p.length + 2, by omega⟩) = -1 := by
    rw [he0, hea₂']
    exact hleafA₂.1
  have hā₁ : A (e ⟨p.length + 1, by omega⟩) (e 0) = -1 := by
    rw [hea₁', he0]
    exact hleafA₁.2
  have hā₂ : A (e ⟨p.length + 2, by omega⟩) (e 0) = -1 := by
    rw [hea₂', he0]
    exact hleafA₂.2
  have hb₁ :
      A (e ⟨p.length, by omega⟩) (e ⟨p.length + 3, by omega⟩) = -1 := by
    rw [hem, heb₁']
    exact hleafB₁.1
  have hb₂ :
      A (e ⟨p.length, by omega⟩) (e ⟨p.length + 4, by omega⟩) = -1 := by
    rw [hem, heb₂']
    exact hleafB₂.1
  have hback₁ :
      A (e ⟨p.length + 3, by omega⟩) (e ⟨p.length, by omega⟩) = -1 := by
    rw [heb₁', hem]
    exact hleafB₁.2
  have hback₂ :
      A (e ⟨p.length + 4, by omega⟩) (e ⟨p.length, by omega⟩) = -1 := by
    rw [heb₂', hem]
    exact hleafB₂.2
  have hpath₁ : ∀ i : Fin (p.length + 5), ∀ hi : i.val < p.length,
      A (e i) (e ⟨i.val + 1, by omega⟩) = -1 := by
    intro i hi
    rw [hepath' (⟨i.val, by omega⟩ : Fin (p.length + 1)),
      hepath' (⟨i.val + 1, by omega⟩ : Fin (p.length + 1))]
    exact (hsimple ⟨i.val, hi⟩).1
  have hpath₂ : ∀ i : Fin (p.length + 5), ∀ hi : i.val < p.length,
      A (e ⟨i.val + 1, by omega⟩) (e i) = -1 := by
    intro i hi
    rw [hepath' (⟨i.val + 1, by omega⟩ : Fin (p.length + 1)),
      hepath' (⟨i.val, by omega⟩ : Fin (p.length + 1))]
    exact (hsimple ⟨i.val, hi⟩).2
  have hzero : ∀ i j : Fin (p.length + 5), i ≠ j →
      (¬((i.val + 1 = j.val ∧ j.val ≤ p.length) ∨
        (j.val + 1 = i.val ∧ i.val ≤ p.length) ∨
        (i.val = 0 ∧ j.val = p.length + 1) ∨
        (i.val = p.length + 1 ∧ j.val = 0) ∨
        (i.val = 0 ∧ j.val = p.length + 2) ∨
        (i.val = p.length + 2 ∧ j.val = 0) ∨
        (i.val = p.length ∧ j.val = p.length + 3) ∨
        (i.val = p.length + 3 ∧ j.val = p.length) ∨
        (i.val = p.length ∧ j.val = p.length + 4) ∨
        (i.val = p.length + 4 ∧ j.val = p.length))) →
      A (e i) (e j) = 0 := by
    intro i j hij hnot
    by_contra hne
    apply hnot
    apply (hsupport i j).mp
    rw [SimpleGraph.fromRel_adj]
    exact ⟨e.injective.ne hij, Or.inl hne⟩
  have hzero₀ : ∀ j, j ≠ 0 → j ≠ 1 →
      j ≠ ⟨p.length + 1, by omega⟩ →
      j ≠ ⟨p.length + 2, by omega⟩ → A (e 0) (e j) = 0 := by
    intro j hj0 hj1 hja₁ hja₂
    apply hzero 0 j hj0.symm
    intro h
    have hj0v : j.val ≠ 0 := by
      intro hv; apply hj0; apply Fin.ext; simpa using hv
    have hj1v : j.val ≠ 1 := by
      intro hv; apply hj1; apply Fin.ext; simpa using hv
    have hja₁v : j.val ≠ p.length + 1 := by
      intro hv; apply hja₁; apply Fin.ext; simpa using hv
    have hja₂v : j.val ≠ p.length + 2 := by
      intro hv; apply hja₂; apply Fin.ext; simpa using hv
    simp only [Fin.val_zero] at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroₘ : ∀ j, j ≠ ⟨p.length, by omega⟩ →
      j ≠ ⟨p.length - 1, by omega⟩ →
      j ≠ ⟨p.length + 3, by omega⟩ →
      j ≠ ⟨p.length + 4, by omega⟩ →
      A (e ⟨p.length, by omega⟩) (e j) = 0 := by
    intro j hjm hjp hjb₁ hjb₂
    apply hzero ⟨p.length, by omega⟩ j hjm.symm
    intro h
    have hjmv : j.val ≠ p.length := by
      intro hv; apply hjm; apply Fin.ext; simpa using hv
    have hjpv : j.val ≠ p.length - 1 := by
      intro hv; apply hjp; apply Fin.ext; simpa using hv
    have hjb₁v : j.val ≠ p.length + 3 := by
      intro hv; apply hjb₁; apply Fin.ext; simpa using hv
    have hjb₂v : j.val ≠ p.length + 4 := by
      intro hv; apply hjb₂; apply Fin.ext; simpa using hv
    simp only at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroPath : ∀ i j, 0 < i.val → i.val < p.length → i ≠ j →
      j.val + 1 ≠ i.val → i.val + 1 ≠ j.val → A (e i) (e j) = 0 := by
    intro i j hi0 him hij hji hij'
    apply hzero i j hij
    intro h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroA₁ : ∀ j, j ≠ ⟨p.length + 1, by omega⟩ → j ≠ 0 →
      A (e ⟨p.length + 1, by omega⟩) (e j) = 0 := by
    intro j hjself hj0
    apply hzero ⟨p.length + 1, by omega⟩ j hjself.symm
    intro h
    have hj0v : j.val ≠ 0 := by
      intro hv; apply hj0; apply Fin.ext; simpa using hv
    simp only at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroA₂ : ∀ j, j ≠ ⟨p.length + 2, by omega⟩ → j ≠ 0 →
      A (e ⟨p.length + 2, by omega⟩) (e j) = 0 := by
    intro j hjself hj0
    apply hzero ⟨p.length + 2, by omega⟩ j hjself.symm
    intro h
    have hj0v : j.val ≠ 0 := by
      intro hv; apply hj0; apply Fin.ext; simpa using hv
    simp only at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroB₁ : ∀ j, j ≠ ⟨p.length + 3, by omega⟩ →
      j ≠ ⟨p.length, by omega⟩ →
      A (e ⟨p.length + 3, by omega⟩) (e j) = 0 := by
    intro j hjself hjm
    apply hzero ⟨p.length + 3, by omega⟩ j hjself.symm
    intro h
    have hjmv : j.val ≠ p.length := by
      intro hv; apply hjm; apply Fin.ext; simpa using hv
    simp only at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  have hzeroB₂ : ∀ j, j ≠ ⟨p.length + 4, by omega⟩ →
      j ≠ ⟨p.length, by omega⟩ →
      A (e ⟨p.length + 4, by omega⟩) (e j) = 0 := by
    intro j hjself hjm
    apply hzero ⟨p.length + 4, by omega⟩ j hjself.symm
    intro h
    have hjmv : j.val ≠ p.length := by
      intro hv; apply hjm; apply Fin.ext; simpa using hv
    simp only at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> omega
  exact ⟨hleft₁, hright₁, ha₁, ha₂, hā₁, hā₂, hb₁, hb₂, hback₁, hback₂,
    hpath₁, hpath₂, hzero₀, hzeroₘ, hzeroPath, hzeroA₁, hzeroA₂,
    hzeroB₁, hzeroB₂⟩

open SimpleGraph

/-- Between two distinct degree-three vertices of a positive-definite Cartan
support tree, the unique path has simple entries in both directions. -/
public lemma cartanSupport_exists_path_entries_eq_neg_one_between_degree_three
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hconn : ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c₁ c₂ : κ) (hneq : c₁ ≠ c₂)
    (hdeg₁ : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c₁ = 3)
    (hdeg₂ : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree c₂ = 3) :
    ∃ p : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Walk c₁ c₂,
      p.IsPath ∧ ∀ r : Fin p.length,
        A (p.getVert r.val) (p.getVert (r.val + 1)) = -1 ∧
        A (p.getVert (r.val + 1)) (p.getVert r.val) = -1 := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have htree : G.IsTree := cartanSupport_isTree A d hdiag hrank hconn hpos
  obtain ⟨p, hp, a₁, a₂, b₁, b₂, ha₁₂, hb₁₂, hab₁, hab₂, hac₁, hac₂,
      ha₁adj, ha₂adj, hb₁adj, hb₂adj, ha₁off, ha₂off, hb₁off, hb₂off⟩ :=
    simpleGraph_two_degree_three_vertices_offPath_neighbors
      G htree c₁ c₂ hneq hdeg₁ hdeg₂
  have hpNil : ¬p.Nil := by
    intro hnil
    exact hneq (hp.nil_iff_eq.mp hnil)
  have hm : 0 < p.length := Walk.not_nil_iff_lt_length.mp hpNil
  let n₀ := p.length - 1
  let f₀ : Fin (n₀ + 1) → κ := fun r => p.getVert (r.val + 1)
  let f₁ : Fin 1 → κ := fun _ => a₁
  let f₂ : Fin 1 → κ := fun _ => a₂
  have hn₀ : n₀ + 1 = p.length := by
    simp [n₀]
    omega
  have hf₀ : Function.Injective f₀ := by
    intro r s hrs
    apply Fin.ext
    have hval := hp.getVert_injOn
      (show r.val + 1 ≤ p.length by omega)
      (show s.val + 1 ≤ p.length by omega)
      (by simpa [f₀] using hrs)
    omega
  have hf₁ : Function.Injective f₁ := fun r s _ => Subsingleton.elim r s
  have hf₂ : Function.Injective f₂ := fun r s _ => Subsingleton.elim r s
  have hc₀ : ∀ r, c₁ ≠ f₀ r := by
    intro r h
    have hval := hp.getVert_injOn
      (show 0 ≤ p.length by omega)
      (show r.val + 1 ≤ p.length by omega)
      (by simpa [f₀] using h)
    omega
  have hc₁ : ∀ r, c₁ ≠ f₁ r := by
    intro r
    simpa [f₁] using ha₁adj.ne
  have hc₂ : ∀ r, c₁ ≠ f₂ r := by
    intro r
    simpa [f₂] using ha₂adj.ne
  have h₀₁ : ∀ r s, f₀ r ≠ f₁ s := by
    intro r s hrs
    apply ha₁off
    have hrs' : f₀ r = a₁ := by simpa [f₁] using hrs
    rw [← hrs']
    exact p.getVert_mem_support _
  have h₀₂ : ∀ r s, f₀ r ≠ f₂ s := by
    intro r s hrs
    apply ha₂off
    have hrs' : f₀ r = a₂ := by simpa [f₂] using hrs
    rw [← hrs']
    exact p.getVert_mem_support _
  have h₁₂ : ∀ r s, f₁ r ≠ f₂ s := by
    intro r s
    simpa [f₁, f₂] using ha₁₂
  have hcenter₀ : ∀ r, G.Adj c₁ (f₀ r) ↔ r = 0 := by
    intro r
    constructor
    · intro hadj
      by_contra hr
      have hrpos : 0 < r.val := by
        exact Fin.pos_iff_ne_zero.mpr hr
      have hnot := simpleGraph_isAcyclic_path_nonadjacent hp htree.isAcyclic
        (i := (0 : Fin (p.length + 1)))
        (j := ⟨r.val + 1, by omega⟩) (by
          change 0 + 1 < r.val + 1
          omega)
      exact hnot (by simpa [f₀] using hadj)
    · intro hr
      subst r
      simpa [f₀] using p.adj_getVert_succ (i := 0) hm
  have hcenter₁ : ∀ r, G.Adj c₁ (f₁ r) ↔ r = 0 := by
    intro r
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      simpa [f₁] using ha₁adj
  have hcenter₂ : ∀ r, G.Adj c₁ (f₂ r) ↔ r = 0 := by
    intro r
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      simpa [f₂] using ha₂adj
  have hpath₀ : ∀ r s, G.Adj (f₀ r) (f₀ s) ↔
      (pathGraph (n₀ + 1)).Adj r s := by
    intro r s
    rw [pathGraph_adj]
    constructor
    · intro hadj
      by_contra hconsec
      push Not at hconsec
      have hrsne : r.val ≠ s.val := by
        intro hrs
        have hfin : r = s := Fin.ext hrs
        subst s
        exact G.irrefl hadj
      rcases lt_or_gt_of_ne hrsne with hrs | hsr
      · have hnot := simpleGraph_isAcyclic_path_nonadjacent hp htree.isAcyclic
          (i := ⟨r.val + 1, by omega⟩) (j := ⟨s.val + 1, by omega⟩)
          (by
            change r.val + 1 + 1 < s.val + 1
            omega)
        exact hnot (by simpa [f₀] using hadj)
      · have hnot := simpleGraph_isAcyclic_path_nonadjacent hp htree.isAcyclic
          (i := ⟨s.val + 1, by omega⟩) (j := ⟨r.val + 1, by omega⟩)
          (by
            change s.val + 1 + 1 < r.val + 1
            omega)
        exact hnot (by simpa [f₀, G.adj_comm] using hadj)
    · intro hconsec
      rcases hconsec with hrs | hsr
      · have hadj := p.adj_getVert_succ (i := r.val + 1) (by omega)
        simpa [f₀, hrs] using hadj
      · have hadj := p.adj_getVert_succ (i := s.val + 1) (by omega)
        simpa [f₀, hsr, G.adj_comm] using hadj
  have hpath₁ : ∀ r s, G.Adj (f₁ r) (f₁ s) ↔
      (pathGraph 1).Adj r s := by
    intro r s
    simp [f₁, pathGraph_adj]
  have hpath₂ : ∀ r s, G.Adj (f₂ r) (f₂ s) ↔
      (pathGraph 1).Adj r s := by
    intro r s
    simp [f₂, pathGraph_adj]
  have hcross₀₁ : ∀ r s, ¬ G.Adj (f₀ r) (f₁ s) := by
    intro r s
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      hp hpNil htree.isAcyclic ha₁adj ha₁off
      (j := ⟨r.val + 1, by omega⟩) (by
        intro h
        have hv := congrArg Fin.val h
        simp at hv)
    simpa [f₀, f₁, G.adj_comm] using hnot
  have hcross₀₂ : ∀ r s, ¬ G.Adj (f₀ r) (f₂ s) := by
    intro r s
    have hnot := simpleGraph_isAcyclic_path_offpath_start_nonadjacent
      hp hpNil htree.isAcyclic ha₂adj ha₂off
      (j := ⟨r.val + 1, by omega⟩) (by
        intro h
        have hv := congrArg Fin.val h
        simp at hv)
    simpa [f₀, f₂, G.adj_comm] using hnot
  have hcross₁₂ : ∀ r s, ¬ G.Adj (f₁ r) (f₂ s) := by
    intro r s hadj
    let q : G.Walk a₁ a₂ := Walk.cons ha₁adj.symm (Walk.cons ha₂adj Walk.nil)
    have hqpath : q.IsPath := by
      apply (Walk.cons_isPath_iff _ _).2
      refine ⟨?_, ?_⟩
      · apply (Walk.cons_isPath_iff _ _).2
        exact ⟨Walk.IsPath.nil, by simpa using ha₂adj.ne⟩
      · intro hmem
        simp at hmem
        rcases hmem with hmem | hmem
        · exact ha₁adj.ne hmem.symm
        · exact ha₁₂ hmem
    have hnot := simpleGraph_isAcyclic_path_nonadjacent hqpath htree.isAcyclic
      (i := (0 : Fin (q.length + 1))) (j := ⟨2, by simp [q]⟩) (by simp [q])
    apply hnot
    simpa [q, f₁, f₂] using hadj
  have hsimple :=
    cartan_three_arm_all_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos c₁ f₀ f₁ f₂ hf₀ hf₁ hf₂ hc₀ hc₁ hc₂
      h₀₁ h₀₂ h₁₂ hcenter₀ hcenter₁ hcenter₂ hpath₀ hpath₁ hpath₂
      hcross₀₁ hcross₀₂ hcross₁₂ hdeg₁
  refine ⟨p, hp, ?_⟩
  intro r
  by_cases hr : r.val = 0
  · have hadj : G.Adj c₁ (p.getVert 1) := by
      simpa using p.adj_getVert_succ (i := 0) hm
    have hs := cartanSupport_degree_three_edge_entries_eq_neg_one
      A d hdiag hrank hpos c₁ (p.getVert 1) hdeg₁ hadj
    simpa [hr] using hs
  · let s : Fin (n₀ + 1) := ⟨r.val, by omega⟩
    have hs := hsimple.1 s (by simp [s]; omega)
    have hrpred : r.val - 1 + 1 = r.val := Nat.sub_add_cancel (by omega)
    simpa [f₀, s, hrpred] using hs

section

/-- An index bijection preserving the positive root-addition relations also
preserves all four choices of signs. Negated roots are represented by the
reduced root-pairing involution `reflectionPerm i i`. This is the signed form
of GLS3, Theorem 1.8.5(c). -/
public theorem preservesRootAddition_signed_iff
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem] [P.IsCrystallographic]
    [P.IsReduced]
    {Q : RootPairing ι₂ ℝ M₂ N₂} [Q.IsRootSystem] [Q.IsCrystallographic]
    [Q.IsReduced]
    {f : ι ≃ ι₂} (hf : PreservesRootPairingStructure P Q f) :
    (∀ i j k, P.root k = P.root i + P.root j ↔
      Q.root (f k) = Q.root (f i) + Q.root (f j)) ∧
    (∀ i j k, P.root k = -P.root i + P.root j ↔
      Q.root (f k) = -Q.root (f i) + Q.root (f j)) ∧
    (∀ i j k, P.root k = P.root i + -P.root j ↔
      Q.root (f k) = Q.root (f i) + -Q.root (f j)) ∧
    (∀ i j k, P.root k = -P.root i + -P.root j ↔
      Q.root (f k) = -Q.root (f i) + -Q.root (f j)) := by
  letI := P.indexNeg
  letI := Q.indexNeg
  have hnegP : ∀ i : ι, P.root (P.reflectionPerm i i) = -P.root i := by
    intro i
    simp
  have hnegQ : ∀ i : ι₂, Q.root (Q.reflectionPerm i i) = -Q.root i := by
    intro i
    simp
  have hmapNeg : ∀ i : ι, f (P.reflectionPerm i i) =
      Q.reflectionPerm (f i) (f i) := hf.1
  have hcase_neg_left : ∀ i j k,
      P.root k = -P.root i + P.root j ↔
        Q.root (f k) = -Q.root (f i) + Q.root (f j) := by
    intro i j k
    have h := hf.2 (P.reflectionPerm i i) j k
    rw [hnegP i] at h
    rw [hmapNeg i, hnegQ (f i)] at h
    simpa using h
  have hcase_neg_right : ∀ i j k,
      P.root k = P.root i + -P.root j ↔
        Q.root (f k) = Q.root (f i) + -Q.root (f j) := by
    intro i j k
    have h := hf.2 i (P.reflectionPerm j j) k
    rw [hnegP j] at h
    rw [hmapNeg j, hnegQ (f j)] at h
    simpa using h
  have hcase_neg_both : ∀ i j k,
      P.root k = -P.root i + -P.root j ↔
        Q.root (f k) = -Q.root (f i) + -Q.root (f j) := by
    intro i j k
    have h := hf.2 (P.reflectionPerm i i) (P.reflectionPerm j j) k
    rw [hnegP i, hnegP j] at h
    rw [hmapNeg i, hmapNeg j, hnegQ (f i), hnegQ (f j)] at h
    simpa using h
  exact ⟨hf.2, hcase_neg_left, hcase_neg_right, hcase_neg_both⟩

end

/-! Root-set transport for the linear equivalence in Theorem 1.8.5(b). -/

section

/-- The weight-space linear equivalence underlying a root-pairing equivalence
carries the complete indexed root set onto the target indexed root set. This
is the root-set transport used in GLS3, Theorem 1.8.5(b). -/
public lemma RootPairing.Equiv.weightEquiv_image_root
    {ι ι₂ M N M₂ N₂ : Type*}
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    [AddCommGroup M₂] [Module ℝ M₂] [AddCommGroup N₂] [Module ℝ N₂]
    {P : RootPairing ι ℝ M N} {Q : RootPairing ι₂ ℝ M₂ N₂}
    (e : P.Equiv Q) :
    e.weightEquiv '' Set.range P.root = Set.range Q.root := by
  ext y
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨e.indexEquiv i,
      (RootPairing.Hom.root_weightMap_apply P Q i e.toHom).symm⟩
  · rintro ⟨j, rfl⟩
    let i : ι := e.indexEquiv.symm j
    refine ⟨P.root i, ⟨i, rfl⟩, ?_⟩
    rw [RootPairing.Equiv.weightEquiv_apply,
      RootPairing.Hom.root_weightMap_apply]
    simp [i]

end

/-- Theorem 1.8.7: reduced crystallographic root systems are equivalent if
and only if they possess isomorphic Dynkin diagrams. -/
public theorem rootPairing_equiv_iff_dynkinDiagramIso
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {Q : RootPairing ι₂ R M₂ N₂} [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced] :
    Nonempty (P.Equiv Q) ↔
      ∃ b : P.Base, ∃ b₂ : Q.Base,
        Nonempty (P.DynkinDiagramIso b.support Q b₂.support) := by
  constructor
  · rintro ⟨e⟩
    let b : P.Base := Classical.choice (RootPairing.nonempty_base (P := P))
    exact ⟨b, RootPairing.Base.mapEquiv e b,
      dynkinDiagramIso_of_rootPairingEquiv e b⟩
  · rintro ⟨b, b₂, ⟨d⟩⟩
    exact rootPairing_equiv_of_dynkinDiagramIso b b₂ d

end Theory.AlgebraicGroup
