module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Uses the root coordinates of the existing CFSG ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: the longest Weyl element and the opposite-Borel intersection bound.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicCells

/-!
# Opposite G₂ Borels intersect in the split torus

The longest Weyl word reverses the eight octonion coordinates and inverts
the split torus. An element of the unipotent radical lying in the opposite
Borel fixes the last singular line and its incident plane; their coordinates
force all six root parameters to vanish. The Borel factorization then gives
the intersection bound used for the native seven-path stabilizer.

Source application: Aschbacher–Smith F.4.6(1), printed pp.276–277.
-/

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
@[expose] public noncomputable section
namespace Atlas.G2.ParabolicApartment
variable {F : Type*} [Field F]

def longest : Model F := ((weylR : Model F) * weylS)^3
private theorem one_apply (x : Carrier F) : (1 : Model F).val x = x := rfl
private theorem mul_apply (g h : Model F) (x : Carrier F) :
    (g*h).val x = g.val (h.val x) := rfl
private theorem r0 (x : Carrier F) : (weylR : Model F).val x 0 = -x 0 := rfl
private theorem r1 (x : Carrier F) : (weylR : Model F).val x 1 = -x 2 := rfl
private theorem r2 (x : Carrier F) : (weylR : Model F).val x 2 = -x 1 := rfl
private theorem r3 (x : Carrier F) : (weylR : Model F).val x 3 = x 3 := rfl
private theorem r4 (x : Carrier F) : (weylR : Model F).val x 4 = x 4 := rfl
private theorem r5 (x : Carrier F) : (weylR : Model F).val x 5 = -x 6 := rfl
private theorem r6 (x : Carrier F) : (weylR : Model F).val x 6 = -x 5 := rfl
private theorem r7 (x : Carrier F) : (weylR : Model F).val x 7 = -x 7 := rfl
private theorem s0 (x : Carrier F) : (weylS : Model F).val x 0 = -x 1 := rfl
private theorem s1 (x : Carrier F) : (weylS : Model F).val x 1 = -x 0 := rfl
private theorem s2 (x : Carrier F) : (weylS : Model F).val x 2 = -x 5 := rfl
private theorem s3 (x : Carrier F) : (weylS : Model F).val x 3 = x 4 := rfl
private theorem s4 (x : Carrier F) : (weylS : Model F).val x 4 = x 3 := rfl
private theorem s5 (x : Carrier F) : (weylS : Model F).val x 5 = -x 2 := rfl
private theorem s6 (x : Carrier F) : (weylS : Model F).val x 6 = -x 7 := rfl
private theorem s7 (x : Carrier F) : (weylS : Model F).val x 7 = -x 6 := rfl
theorem longest_apply (x : Carrier F) :
    (longest : Model F).val x = ![x 7,x 6,x 5,x 4,x 3,x 2,x 1,x 0] := by
  simp only [longest,pow_succ,pow_zero,mul_apply,one_apply]
  ext i
  fin_cases i <;> simp only [Fin.reduceFinMk,r0,r1,r2,r3,r4,r5,r6,r7,s0,s1,s2,s3,s4,s5,s6,s7,neg_neg,Matrix.cons_val]

theorem longest_inv : (longest : Model F)⁻¹ = longest := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change longest.val (longest.val x) = x
  rw [longest_apply,longest_apply]
  ext i
  fin_cases i <;> rfl

private theorem longest_twice (x : Carrier F) :
    (longest : Model F).val (longest.val x) = x := by
  have hw : (longest : Model F) * longest = 1 := by
    nth_rw 1 [←longest_inv]
    exact inv_mul_cancel _
  rw [←mul_apply,hw,one_apply]

private theorem rootA_apply (a : F) (x : Carrier F) :
    (rootA a).val x = rootAApply a x := rfl
private theorem rootB_apply (a : F) (x : Carrier F) :
    (rootB a).val x = rootBApply a x := rfl
private theorem rootC_apply (a : F) (x : Carrier F) :
    (rootC a).val x = rootCApply a x := rfl
private theorem rootD_apply (a : F) (x : Carrier F) :
    (rootD a).val x = rootDApply a x := rfl
private theorem rootE_apply (a : F) (x : Carrier F) :
    (rootE a).val x = rootEApply a x := rfl
private theorem rootF_apply (a : F) (x : Carrier F) :
    (rootF a).val x = rootFApply a x := rfl
private theorem unipotent_apply (v : Fin 6 → F) (x : Carrier F) :
    (unipotentProduct v).val x =
      rootAApply (v 0) (rootBApply (v 1) (rootCApply (v 2)
        (rootDApply (v 3) (rootEApply (v 4) (rootFApply (v 5) x))))) := by
  simp only [unipotentProduct,mul_apply,rootA_apply,rootB_apply,rootC_apply,
    rootD_apply,rootE_apply,rootF_apply]

private theorem unipotent_opposite (v : Fin 6 → F) (a : F)
    (h : (unipotentProduct v).val (basisVector 7) = a • basisVector 7)
    (h6 : (unipotentProduct v).val (basisVector 6) 5 = 0) : v = 0 := by
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have hf := congrFun h 6
  simp [unipotent_apply,basisVector,
    rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply] at h1 h2 h4 h5 hf h6
  have hd : v 3 = 0 := by simpa [hf] using h5
  have hc : v 2 = 0 := by simpa [hf] using h4
  have hb : v 1 = 0 := by simpa [hf] using h2
  have ha : v 0 = 0 := by simpa [hf,hc] using h1
  have he : v 4 = 0 := by simpa using h6
  ext i
  fin_cases i <;> assumption

private theorem opposite_conditions (g : Model F)
    (h : longest * g * longest ∈ borel) :
    (∃ a : F, g.val (basisVector 7) = a • basisVector 7) ∧
      g.val (basisVector 6) 5 = 0 := by
  have hp := parabolic_le_pointStabilizer (borel_le_parabolic₂ h)
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp hp
  have hw0 : (longest : Model F).val (basisVector 0) = basisVector 7 := by
    rw [longest_apply]; ext i; fin_cases i <;> simp [basisVector]
  have hw1 : (longest : Model F).val (basisVector 1) = basisVector 6 := by
    rw [longest_apply]; ext i; fin_cases i <;> simp [basisVector]
  have h7 : g.val (basisVector 7) = (a : F) • basisVector 7 := by
    have he := congrArg (fun x => (longest : Model F).val x) ha
    change longest.val (longest.val (g.val
      (longest.val (basisVector 0)))) = _ at he
    rw [hw0,Units.smul_def,map_smul,hw0] at he
    simpa only [longest_twice,Units.smul_def] using he
  have h6 : g.val (basisVector 6) 5 = 0 := by
    have hh := (borel_le_shortPlaneStabilizer h).1 (basisVector 1)
      (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
    change longest.val (g.val (longest.val (basisVector 1))) 2 = 0 at hh
    rw [hw1,longest_apply] at hh
    exact hh
  exact ⟨⟨a,h7⟩,h6⟩

private theorem unipotent_mem_opposite (v : Fin 6 → F)
    (h : longest * unipotentProduct v * longest ∈ borel) : v = 0 := by
  obtain ⟨⟨a,ha⟩,h6⟩ := opposite_conditions _ h
  exact unipotent_opposite v a ha h6

private theorem torus_apply (l m : Fˣ) (x : Carrier F) (i : Fin 8) :
    (torus l m).val x i = (torusWeights l m i : F) * x i := rfl

private theorem w0 (x : Carrier F) : (longest : Model F).val x 0 = x 7 := congrFun (longest_apply x) 0
private theorem w1 (x : Carrier F) : (longest : Model F).val x 1 = x 6 := congrFun (longest_apply x) 1
private theorem w2 (x : Carrier F) : (longest : Model F).val x 2 = x 5 := congrFun (longest_apply x) 2
private theorem w3 (x : Carrier F) : (longest : Model F).val x 3 = x 4 := congrFun (longest_apply x) 3
private theorem w4 (x : Carrier F) : (longest : Model F).val x 4 = x 3 := congrFun (longest_apply x) 4
private theorem w5 (x : Carrier F) : (longest : Model F).val x 5 = x 2 := congrFun (longest_apply x) 5
private theorem w6 (x : Carrier F) : (longest : Model F).val x 6 = x 1 := congrFun (longest_apply x) 6
private theorem w7 (x : Carrier F) : (longest : Model F).val x 7 = x 0 := congrFun (longest_apply x) 7

theorem longest_torus (l m : Fˣ) :
    (longest : Model F) * torus l m * longest = torus l⁻¹ m⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (longest : Model F).val ((torus l m).val (longest.val x)) =
    (torus l⁻¹ m⁻¹).val x
  ext i
  fin_cases i <;> simp only [Fin.reduceFinMk,w0,w1,w2,w3,w4,w5,w6,w7,torus_apply,
    torusWeights,Matrix.cons_val,Units.val_one,one_mul,inv_inv,mul_comm]

private theorem conjugate_torus_mem {t : Model F} (ht : t ∈ splitTorus) :
    MulAut.conj (longest : Model F) t ∈ borel := by
  obtain ⟨⟨l,m⟩,rfl⟩ := ht
  change longest * torus l m * longest⁻¹ ∈ borel
  rw [longest_inv,longest_torus]
  exact mem_sup_right ⟨(l⁻¹,m⁻¹),rfl⟩

/-- The two opposite flag stabilizers intersect in the actual split torus. -/
theorem opposite_borel_le_torus :
    borel (K := F) ⊓ borel.comap (MulAut.conj (longest : Model F)).toMonoidHom ≤
      splitTorus := by
  rintro g ⟨hg,hopp⟩
  obtain ⟨⟨u,t⟩,hp⟩ := (borelProductEquiv (K := F)).surjective ⟨g,hg⟩
  have hp' : u.val * t.val = g := congrArg Subtype.val hp
  have ht := conjugate_torus_mem t.property
  have hu : MulAut.conj (longest : Model F) u.val ∈ borel := by
    apply (borel.mul_mem_cancel_right ht).mp
    rw [←map_mul,hp']
    exact hopp
  obtain ⟨u,huU⟩ := u
  rw [unipotent_eq_range] at huU
  obtain ⟨v,rfl⟩ := huU
  change longest * unipotentProduct v * longest⁻¹ ∈ borel at hu
  rw [longest_inv] at hu
  have hv := unipotent_mem_opposite v hu
  change unipotentProduct v * t.val = g at hp'
  rw [hv,unipotentProduct_zero,one_mul] at hp'
  exact hp' ▸ t.property
end Atlas.G2.ParabolicApartment
