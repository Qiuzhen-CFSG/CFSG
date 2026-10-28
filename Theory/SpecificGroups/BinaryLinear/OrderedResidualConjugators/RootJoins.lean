module

public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators

/-!
# Adjacent conjugators for explicit binary root joins

The previous node's radical supplies the upper simple transvection at the
next node. Combining it with that next node's cubic actor gives the lower
simple transvection and then the adjacent swap. The swap therefore belongs
to the enlarged root join. Conversely, conjugating the incident roots of
the previous nodes recovers every generator at the new node. This proves
the successive-join identity in arbitrary dimension, with right conjugation.

The final theorem applies this calculation to the intrinsic residuals under
one explicit upper-bound premise. The reverse bound is already proved in
the imported module. The residual recognition premise must be discharged
before using this as the source residual identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

@[simp] theorem root_inv {m : ℕ} (b : Basis m) (r s : Fin (m + 1)) (hrs : r ≠ s) :
    (root b r s hrs)⁻¹ = root b r s hrs := by
  rw [root, ← map_inv, CubicPairNormalizers.CoreAbsorption.root_inv]

theorem adjacentSwap_conj_root {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) :
    (MulAut.conj ((adjacentSwap b i)⁻¹)) (root b r s hrs) =
      root b (Equiv.swap i.castSucc i.succ r) (Equiv.swap i.castSucc i.succ s)
        (fun h => hrs ((Equiv.swap i.castSucc i.succ).injective h)) := by
  rw [adjacentSwap_inv]
  apply b.ext'
  intro k
  change adjacentSwap b i (root b r s hrs ((adjacentSwap b i)⁻¹ (b k))) = _
  rw [adjacentSwap_inv, adjacentSwap_basis, root_basis, root_basis]
  split_ifs with h hs hs
  · simp only [map_add, adjacentSwap_basis, Equiv.swap_apply_self]
  · exact (hs (Equiv.swap_apply_eq_iff.mp h)).elim
  · exact (h (Equiv.swap_apply_eq_iff.mpr hs)).elim
  · simp only [adjacentSwap_basis, Equiv.swap_apply_self]

theorem adjacentSwap_eq_roots {m : ℕ} (b : Basis m) (i : Fin m)
    (hi : i.castSucc ≠ i.succ) :
    adjacentSwap b i = root b i.castSucc i.succ hi *
      root b i.succ i.castSucc hi.symm * root b i.castSucc i.succ hi := by
  apply b.ext'
  intro k
  change adjacentSwap b i (b k) =
    root b i.castSucc i.succ hi
      (root b i.succ i.castSucc hi.symm (root b i.castSucc i.succ hi (b k)))
  by_cases hk : k = i.castSucc
  · subst k
    simp only [adjacentSwap_basis, Equiv.swap_apply_left, root_basis,
      hi, ↓reduceIte, map_add]
    ext t
    change b i.succ t = b i.castSucc t + (b i.succ t + b i.castSucc t)
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add]
  · by_cases hks : k = i.succ
    · subst k
      simp only [adjacentSwap_basis, Equiv.swap_apply_right, root_basis,
        hi, hi.symm, ↓reduceIte, map_add]
      ext t
      change b i.castSucc t = (b i.succ t + b i.castSucc t) +
        (b i.castSucc t + (b i.succ t + b i.castSucc t))
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
        mul_zero, mul_one, zero_add]
    · simp only [adjacentSwap_basis, Equiv.swap_apply_of_ne_of_ne hk hks, root_basis,
        hk, hks, ↓reduceIte]

private theorem cubic_mem_rootNode {m : ℕ} (b : Basis m) (i : Fin m) :
    cubic b i.castSucc i.succ (by simp [Fin.ext_iff]) ∈ rootNode b i :=
  subset_closure (Or.inl rfl)

private theorem root_mem_rootNode {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m + 1)) (hrs : r ≠ s) (h : Incident i r s) :
    root b r s hrs ∈ rootNode b i :=
  subset_closure (Or.inr ⟨r, s, hrs, h, rfl⟩)

private theorem rootNode_le_initial {m : ℕ} (b : Basis m) (i : Fin m) (r : ℕ)
    (hi : i.val < r) : rootNode b i ≤ initialRootNodes b r :=
  le_iSup_of_le i (le_iSup_of_le hi le_rfl)

private theorem initialRootNodes_mono {m : ℕ} (b : Basis m) {r s : ℕ} (h : r ≤ s) :
    initialRootNodes b r ≤ initialRootNodes b s := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  exact rootNode_le_initial b i s (lt_of_lt_of_le hi h)

/-- Every root from an earlier coordinate to a coordinate strictly beyond
the initial block is already in an initial node. -/
private theorem outgoing_mem_initial {m : ℕ} (b : Basis m) (r : ℕ) (hr : r < m)
    (a c : Fin (m + 1)) (hac : a ≠ c) (ha : a.val < r) (hc : r < c.val) :
    root b a c hac ∈ initialRootNodes b r := by
  let i : Fin m := ⟨a.val, by omega⟩
  apply rootNode_le_initial b i r ha
  apply root_mem_rootNode b i a c hac
  exact Or.inr ⟨Or.inl (Fin.ext rfl), by change a.val + 1 < c.val; omega⟩

/-- The last row of the initial block uses the preceding node's radical. -/
private theorem last_outgoing_mem_initial {m : ℕ} (b : Basis m) (r : ℕ)
    (hpos : 1 ≤ r) (hr : r < m) (c : Fin (m + 1)) (hc : r < c.val) :
    root b (⟨r, by omega⟩ : Fin (m + 1)) c (by intro h; have hh := congrArg Fin.val h; change r = c.val at hh; omega) ∈
      initialRootNodes b r := by
  let i : Fin m := ⟨r - 1, by omega⟩
  apply rootNode_le_initial b i r (by dsimp [i]; omega)
  apply root_mem_rootNode b i
  exact Or.inr ⟨Or.inr (Fin.ext (by dsimp [i]; omega)), by dsimp [i]; omega⟩

/-- The next adjacent swap is already generated by two consecutive root nodes.
Its two simple transvections are recovered using the previous radical and
then the next cubic actor. -/
theorem adjacentSwap_mem_initialRootNodes {m : ℕ} (b : Basis m) (r : ℕ)
    (hpos : 1 ≤ r) (hr : r < m) :
    adjacentSwap b ⟨r, hr⟩ ∈ initialRootNodes b (r + 1) := by
  let i : Fin m := ⟨r, hr⟩
  have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  have hu : root b i.castSucc i.succ hi ∈ initialRootNodes b (r + 1) :=
    initialRootNodes_mono b (Nat.le_succ r)
      (last_outgoing_mem_initial b r hpos hr i.succ (by simp [i]))
  have hc : cubic b i.castSucc i.succ hi ∈ initialRootNodes b (r + 1) :=
    rootNode_le_initial b i (r + 1) (by simp [i]) (cubic_mem_rootNode b i)
  have hl : root b i.succ i.castSucc hi.symm ∈ initialRootNodes b (r + 1) := by
    simpa only [cubic, inv_mul_cancel_left] using
      (initialRootNodes b (r + 1)).mul_mem ((initialRootNodes b (r + 1)).inv_mem hu) hc
  rw [adjacentSwap_eq_roots b _ hi]
  exact (initialRootNodes b (r + 1)).mul_mem
    ((initialRootNodes b (r + 1)).mul_mem hu hl) hu

/-- Successive joins of the explicit cubic and incident-root subgroups are
obtained by right conjugation with the next adjacent basis swap. This is
an identity of generated subgroups, independent of residual recognition. -/
theorem initialRootNodes_successor {m : ℕ} (b : Basis m) (r : ℕ)
    (hpos : 1 ≤ r) (hr : r < m) :
    initialRootNodes b (r + 1) = initialRootNodes b r ⊔
      (initialRootNodes b r).map (MulAut.conj ((adjacentSwap b ⟨r, hr⟩)⁻¹)).toMonoidHom := by
  let i : Fin m := ⟨r, hr⟩
  let D := initialRootNodes b r
  let H := D ⊔ D.map (MulAut.conj ((adjacentSwap b i)⁻¹)).toMonoidHom
  have hin (g : LinearGroup (m + 1)) (hg : g ∈ D) : g ∈ H := (le_sup_left : D ≤ H) hg
  have hconj (g : LinearGroup (m + 1)) (hg : g ∈ D) :
      (MulAut.conj ((adjacentSwap b i)⁻¹)) g ∈ H :=
    (le_sup_right : D.map (MulAut.conj ((adjacentSwap b i)⁻¹)).toMonoidHom ≤ H)
      (mem_map_of_mem _ hg)
  have hroot (a c : Fin (m + 1)) (hac : a ≠ c) (h : Incident i a c) :
      root b a c hac ∈ H := by
    rcases h with ⟨hai, rfl | rfl⟩ | ⟨rfl | rfl, hic⟩
    · have has : a ≠ i.succ := by intro he; have := congrArg Fin.val he; dsimp [i] at *; omega
      have ha0 : a ≠ i.castSucc := by intro he; have := congrArg Fin.val he; dsimp [i] at *; omega
      have hh := hconj _ (outgoing_mem_initial b r hr a i.succ has hai (by simp [i]))
      simpa only [adjacentSwap_conj_root, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne ha0 has] using hh
    · exact hin _ (outgoing_mem_initial b r hr a i.succ hac hai (by simp [i]))
    · exact hin _ (last_outgoing_mem_initial b r hpos hr c (by dsimp [i] at hic; omega))
    · have hc0 : c ≠ i.castSucc := by intro he; have := congrArg Fin.val he; dsimp [i] at *; omega
      have hc1 : c ≠ i.succ := by intro he; have := congrArg Fin.val he; dsimp [i] at *; omega
      have hu : root b i.castSucc c hc0.symm ∈ D :=
        last_outgoing_mem_initial b r hpos hr c (by dsimp [i] at hic; omega)
      have hh := hconj _ hu
      simpa only [adjacentSwap_conj_root, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hc0 hc1] using hh
  have hnode : rootNode b i ≤ H := by
    apply (closure_le _).mpr
    rintro g (hg | ⟨a, c, hac, h, rfl⟩)
    · have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
      have hu : root b i.castSucc i.succ hi ∈ D :=
        last_outgoing_mem_initial b r hpos hr i.succ (by simp [i])
      have hl : root b i.succ i.castSucc hi.symm ∈ H := by
        simpa only [adjacentSwap_conj_root, Equiv.swap_apply_left,
          Equiv.swap_apply_right] using hconj _ hu
      rw [Set.mem_singleton_iff] at hg
      rw [hg, cubic]
      exact H.mul_mem (hin _ hu) hl
    · exact hroot a c hac h
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    by_cases hjr : j.val < r
    · exact (rootNode_le_initial b j r hjr).trans le_sup_left
    · have he : j = i := Fin.ext (by dsimp [i]; omega)
      simpa only [he] using hnode
  · have hD : D ≤ initialRootNodes b (r + 1) := initialRootNodes_mono b (Nat.le_succ r)
    apply sup_le hD
    apply map_le_iff_le_comap.mpr
    intro g hg
    have hs := adjacentSwap_mem_initialRootNodes b r hpos hr
    change (adjacentSwap b i)⁻¹ * g * ((adjacentSwap b i)⁻¹)⁻¹ ∈
      initialRootNodes b (r + 1)
    rw [inv_inv]
    exact (initialRootNodes b (r + 1)).mul_mem
      ((initialRootNodes b (r + 1)).mul_mem ((initialRootNodes b (r + 1)).inv_mem hs)
        (hD hg)) hs

/-- Residual recognition is the only extra input needed to turn the explicit
root identity into the identity for the intrinsic two-residuals. -/
theorem initialResiduals_successor_of_nodeResidual_le {m : ℕ} (b : Basis m)
    (hres : ∀ i : Fin m, nodeResidual b i ≤ rootNode b i)
    (r : ℕ) (hpos : 1 ≤ r) (hr : r < m) :
    initialResiduals b (r + 1) = initialResiduals b r ⊔
      (initialResiduals b r).map (MulAut.conj ((adjacentSwap b ⟨r, hr⟩)⁻¹)).toMonoidHom := by
  have he (k : ℕ) : initialResiduals b k = initialRootNodes b k := by
    apply iSup_congr
    intro i
    apply iSup_congr
    intro _
    exact le_antisymm (hres i) (rootNode_le_nodeResidual b i)
  rw [he, he]
  exact initialRootNodes_successor b r hpos hr

end BinaryLinear.OrderedResidualConjugators
