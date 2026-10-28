/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeSystematic

/-!
# HexacodeFaithful

The monomial automorphism action on the hexacode is faithful. Surjectivity of projection
onto two coordinates separates coordinate positions and local letter maps, forcing an
automorphism acting trivially to be the identity.

Source: `Atlas/Codes/HexacodeFaithful.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes

theorem hex_two_values (i j : HexIndex) (hij : i ≠ j) (u v : K) :
    ∃ w : hexacode, w.val i = u ∧ w.val j = v := by
  have ht : ∀ i j : HexIndex, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := ht i j
  let e : Fin 3 ↪ HexIndex :=
    ⟨![i,j,k], by
      intro x y h
      fin_cases x <;> fin_cases y <;>
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]⟩
  obtain ⟨w,hw⟩ := (hexProjection_bijective e).2 ![u,v,0]
  exact ⟨w, congrFun hw 0, congrFun hw 1⟩

theorem hexAction_eq_one (g : HexAutomorphisms) (hg : hexAction g = 1) : g = 1 := by
  have ha (w : hexacode) (i : HexIndex) : g.val.localMap i (w.val (g.val.perm.symm i)) = w.val i :=
    congrArg (fun v : hexacode => v.val i) (LinearEquiv.congr_fun hg w)
  have hp (i : HexIndex) : g.val.perm.symm i = i := by
    by_contra hi
    obtain ⟨w,hw0,hwa⟩ := hex_two_values (g.val.perm.symm i) i hi 0 a
    have hh := ha w i
    rw [hw0,hwa,map_zero] at hh
    exact (by decide : (0 : K) ≠ a) hh
  apply Subtype.ext
  apply Monomial.ext
  · apply Equiv.ext
    intro i
    have hh := congrArg g.val.perm (hp i)
    exact (g.val.perm.apply_symm_apply i).symm.trans hh |>.symm
  · funext i
    apply LinearEquiv.ext
    intro u
    obtain ⟨w,hw⟩ := hexCoordinate_surjective i u
    have hh := ha w i
    rw [hp i] at hh
    change w.val i = u at hw
    rw [hw] at hh
    exact hh

theorem hexAction_injective : Function.Injective hexAction := by
  apply (hexAction.ker_eq_bot_iff).mp
  apply le_antisymm _ bot_le
  intro g hg
  exact Subgroup.mem_bot.mpr (hexAction_eq_one g hg)

end Atlas.Codes
