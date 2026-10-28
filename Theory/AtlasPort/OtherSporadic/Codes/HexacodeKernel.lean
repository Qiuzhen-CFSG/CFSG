/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeGenerators

/-!
# HexacodeKernel

A hexacode automorphism fixing every coordinate is one of the three powers of the
explicit scalar. Relations imposed by the systematic encoder determine all local letter
maps from one of them.

Source: `Atlas/Codes/HexacodeKernel.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

/-- Coefficient comparison in the systematic graph bounds the full coordinate kernel. -/
theorem hex_kernel_relations (g : HexAutomorphisms) (hp : hexCoordinateHom g = 1) :
    let L := fun i : Fin 6 => g.val.localMap (hexPos i)
    L 2 = L 0 ∧ L 4 = L 0 ∧ L 1 = L 3 ∧
    (∀ u, L 3 (localU u) = localU (L 0 u)) ∧
    (∀ u, L 5 (localW u) = localW (L 0 u)) ∧
    L 0 * localKappa = localKappa * L 0 := by
  dsimp only
  let L := fun i : Fin 6 => g.val.localMap (hexPos i)
  have hp' : g.val.perm = 1 := hp
  have ha (w : HexWord) (i : HexIndex) : Monomial.act g.val w i = g.val.localMap i (w i) := by
    change g.val.localMap i (w (g.val.perm.symm i)) = _
    rw [hp']; rfl
  have hs (x : Fin 3 → K) := (hexacode_systematic (Monomial.act g.val (systematicEncoder x))).mp
    ((g.prop _).mp (systematic_mem x))
  simp only [ha, systematic_pos0, systematic_pos1, systematic_pos2,
    systematic_pos3, systematic_pos4, systematic_pos5] at hs
  have h30 (u : K) : L 3 (localU u) = localU (L 0 u) := by
    have h := (hs ![u,0,0]).1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h31 (u : K) : L 3 u = L 1 u := by
    have h := (hs ![0,u,0]).1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h32 (u : K) : L 3 (localU u) = localU (L 2 u) := by
    have h := (hs ![0,0,u]).1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h40 (u : K) : L 4 (localKappa⁻¹ u) = localKappa⁻¹ (L 0 u) := by
    have h := (hs ![u,0,0]).2.1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h42 (u : K) : L 4 u = L 2 u := by
    have h := (hs ![0,0,u]).2.1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h50 (u : K) : L 5 (localW u) = localW (L 0 u) := by
    have h := (hs ![u,0,0]).2.2
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero, zero_add] using h
  have h20 : L 2 = L 0 := by
    apply LinearEquiv.ext
    intro u
    exact localU.injective ((h32 u).symm.trans (h30 u))
  have h40' : L 4 = L 0 := (LinearEquiv.ext h42).trans h20
  refine ⟨h20,h40',(LinearEquiv.ext h31).symm,h30,h50,?_⟩
  apply LinearEquiv.ext
  intro u
  have hh := congrArg localKappa (h40 (localKappa u))
  simpa only [h40', k_inv_apply_apply, k_apply_inv_apply,
    LinearEquiv.mul_apply] using hh.symm

theorem hex_kernel_trichotomy (g : HexAutomorphisms) (hp : hexCoordinateHom g = 1) :
    g = 1 ∨ g = hexZ ∨ g = hexZ ^ 2 := by
  obtain ⟨h20,h40,h13,h30,h50,hc⟩ := hex_kernel_relations g hp
  dsimp only at h20 h40 h13 h30 h50 hc
  have h0 := kIsometry_centralizer _ hc
  have determine (v : HexAutomorphisms) (hv : hexCoordinateHom v = 1)
      (h0 : g.val.localMap (hexPos 0) = v.val.localMap (hexPos 0)) : g = v := by
    obtain ⟨v20,v40,v13,v30,v50,_⟩ := hex_kernel_relations v hv
    dsimp only at v20 v40 v13 v30 v50
    apply Subtype.ext
    apply Monomial.ext
    · exact hp.trans hv.symm
    · funext i
      obtain ⟨k,rfl⟩ := hexIndexEquiv.symm.surjective i
      change g.val.localMap (hexPos k) = v.val.localMap (hexPos k)
      have h3 : g.val.localMap (hexPos 3) = v.val.localMap (hexPos 3) := by
        apply LinearEquiv.ext
        intro u
        obtain ⟨w,rfl⟩ := localU.surjective u
        rw [h30,v30,h0]
      fin_cases k
      · exact h0
      · exact h13.trans (h3.trans v13.symm)
      · exact h20.trans (h0.trans v20.symm)
      · exact h3
      · exact h40.trans (h0.trans v40.symm)
      · apply LinearEquiv.ext
        intro u
        obtain ⟨w,rfl⟩ := localW.surjective u
        change g.val.localMap (hexPos 5) (localW w) = v.val.localMap (hexPos 5) (localW w)
        rw [h50,v50,h0]
  rcases h0 with h0 | h0 | h0
  · exact Or.inl (determine 1 (map_one _) h0)
  · exact Or.inr (Or.inl (determine hexZ hexZ_coordinate h0))
  · right; right
    apply determine (hexZ ^ 2) (by simp)
    rw [h0]
    apply LinearEquiv.ext
    intro u
    revert u
    decide

theorem hex_kernel_iff (g : HexAutomorphisms) : hexCoordinateHom g = 1 ↔
    g = 1 ∨ g = hexZ ∨ g = hexZ ^ 2 := by
  constructor
  · exact hex_kernel_trichotomy g
  · rintro (rfl | rfl | rfl) <;> simp

end Atlas.Codes
