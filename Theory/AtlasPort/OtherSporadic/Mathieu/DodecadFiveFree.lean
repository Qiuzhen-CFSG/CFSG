/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadFifthFixed
public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAction

/-!
# DodecadFiveFree

A dodecad stabilizer fixing five distinct interior coordinates is trivial. Transport the
first four coordinates to a standard tetrad and apply the local fifth-point fixation
theorem to the conjugated element.

Source: `Atlas/Mathieu/DodecadFiveFree.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem dodecad_five_fixed (D : Dodecad) (e : Fin 5 ↪ Omega)
    (he : ∀ k, e k ∈ D.val) (g : Mathieu24CodeModel)
    (hD : permuteBlock g.val D.val = D.val) (hg : ∀ k, g.val (e k) = e k) : g = 1 := by
  let i : HexIndex := (0,0)
  let f : Fin 4 ↪ Omega := (Fin.castSuccEmb (n := 4)).trans e
  obtain ⟨a,ha⟩ := orderedFour_to_tetrad f i
  let E : Dodecad := ⟨permuteBlock a.val D.val,codePreserving_dodecad_forward _ a.prop _ D.prop⟩
  have hT : tetrad i ⊆ E.val := by
    intro p hp
    have hi := (mem_tetrad p i).mp hp
    exact Finset.mem_image.mpr ⟨f p.2,he p.2.castSucc,(ha p.2).trans (Prod.ext hi.symm rfl)⟩
  obtain ⟨p,hp⟩ := (dodecadParametersSupport_bijective i).2 ⟨E,hT⟩
  have hsupport : support (c0Encoder (p.1.val.val,p.2.val)) = E.val :=
    congrArg (fun E : DodecadsThroughTetrad i => E.val.val) hp
  let c : Mathieu24CodeModel := a*g*a⁻¹
  have hcT : c ∈ TetradPointStabilizer i := by
    apply (tetradPointStabilizer_mem i c).mpr
    intro k
    change a.val (g.val (a.val⁻¹ (i,k))) = (i,k)
    rw [← ha k,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    change a.val (g.val (e k.castSucc)) = a.val (e k.castSucc)
    rw [hg]
  let cT : TetradPointStabilizer i := ⟨c,hcT⟩
  have hcD : permuteBlock c.val E.val = E.val := by
    change permuteBlock (a.val*g.val*a.val⁻¹) (permuteBlock a.val D.val) = permuteBlock a.val D.val
    rw [permuteBlock_mul,permuteBlock_mul,← permuteBlock_mul a.val⁻¹ a.val,
      inv_mul_cancel,permuteBlock_one,hD]
  let z : Omega := a.val (e 4)
  have hz : z ∈ E.val := Finset.mem_image.mpr ⟨e 4,he 4,rfl⟩
  have hzi : z.1 ≠ i := by
    intro hi
    have hz' : a.val (e 4) = a.val (f z.2) := by
      rw [ha]
      exact Prod.ext hi rfl
    have he' : (4 : Fin 5) = z.2.castSucc := e.injective (a.val.injective hz')
    have hn := congrArg Fin.val he'
    have hb := z.2.isLt
    simp only [Fin.val_castSucc] at hn
    omega
  have hcz : c.val z = z := by
    change a.val (g.val (a.val⁻¹ (a.val (e 4)))) = a.val (e 4)
    rw [Equiv.Perm.inv_def,Equiv.symm_apply_apply,hg]
  have hc1 := dodecad_tetrad_fifth_fixed i p cT
    (by change permuteBlock c.val _ = _; rw [hsupport]; exact hcD)
    z (hsupport.symm ▸ hz) hzi hcz
  have hc : a*g*a⁻¹ = 1 := congrArg (fun x : TetradPointStabilizer i => x.val) hc1
  have hh := congrArg (fun x : Mathieu24CodeModel => a⁻¹*x*a) hc
  simpa [mul_assoc] using hh

end Atlas.Codes
