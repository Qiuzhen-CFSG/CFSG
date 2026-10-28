module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The octonion, root and torus formulas use the existing ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: ternary torus conjugation, neighbor movement and centralizer calculations.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicCells
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration

/-!
# The split torus over the field of three elements

The two diagonal involutions generate the split torus. Their explicit
Weyl conjugates and moved neighbors determine the local fixed graph.
Centralizing both involutions kills each unipotent coordinate, so their
centralizer in the Borel is the torus. Its exponent is two, and no
nonidentity torus element centralizes both Weyl reflections.

These are the precise model calculations used in the ternary completion
proof of Aschbacher–Smith F.4.26, printed p.288.
-/

@[expose] public section

noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
namespace Atlas.G2.TernaryTorus
abbrev MG := Model (ZMod 3)

def a : MG := torus (-1) 1
def b : MG := torus 1 (-1)

theorem a_sq : a^2=1 := by
  rw [pow_two]
  change torus (-1 : (ZMod 3)ˣ) 1 * torus (-1) 1 = 1
  rw [torus_product]
  norm_num
  exact torusHom.map_one

theorem b_sq : b^2=1 := by
  rw [pow_two]
  change torus (1 : (ZMod 3)ˣ) (-1) * torus 1 (-1) = 1
  rw [torus_product]
  norm_num
  exact torusHom.map_one

theorem ab_commute : Commute a b := by
  change torus (-1 : (ZMod 3)ˣ) 1 * torus 1 (-1) =
    torus 1 (-1) * torus (-1) 1
  simp only [torus_product,one_mul,mul_one]

theorem weylS_a : (weylS : MG)*a*weylS=b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [-ZMod.inv_coe_unit,a,b,torus,torusEquiv,torusLinear,torusWeights,
    weylS,weylSEquiv,weylSLinear,weylSApply]
theorem weylS_b : (weylS : MG)*b*weylS=a := by
  have hSS : (weylS : MG)*weylS=1 := by rw [←pow_two,weylS_sq]
  rw [←weylS_a]
  calc
    _ = (weylS*weylS)*a*(weylS*weylS) := by group
    _ = a := by rw [hSS,one_mul,mul_one]
theorem weylR_a : (weylR : MG)*a*weylR=a*b := by
  change (weylR : MG)*torus (-1) 1*weylR=torus (-1) 1*torus 1 (-1)
  rw [torus_product]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [-ZMod.inv_coe_unit,torus,torusEquiv,torusLinear,torusWeights,
    weylR,weylREquiv,weylRLinear,weylRApply]
theorem weylR_b : (weylR : MG)*b*weylR=b := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [-ZMod.inv_coe_unit,b,torus,torusEquiv,torusLinear,torusWeights,
    weylR,weylREquiv,weylRLinear,weylRApply]

end Atlas.G2.TernaryTorus

namespace Atlas.G2.TernaryTorus
open Atlas.G2.ParabolicCells

def shortMover : parabolic₁ (F := ZMod 3) :=
  ⟨rootF 1*weylS,parabolic₁.mul_mem
    (borel_le_parabolic₁ (mem_sup_left (subset_closure (by simp))))
    (mem_sup_right (subset_closure (by simp)))⟩
def longMover : parabolic₂ (F := ZMod 3) :=
  ⟨rootE 1*weylR,parabolic₂.mul_mem
    (borel_le_parabolic₂ (mem_sup_left (subset_closure (by simp)))) weylR_mem_parabolic⟩

private theorem rootF_inv : (rootF (1 : ZMod 3))⁻¹=rootF (-1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [Atlas.G2.rootF_add,add_neg_cancel]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [rootF,rootFEquiv,rootFLinear,rootFApply]
private theorem rootE_inv : (rootE (1 : ZMod 3))⁻¹=rootE (-1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [Atlas.G2.rootE_add,add_neg_cancel]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [rootE,rootEEquiv,rootELinear,rootEApply]

/-- A torus involution moves a neighbor at the short endpoint. -/
theorem shortMover_not_fixed : shortMover.val⁻¹*a*shortMover.val∉borel := by
  intro h
  have hp := parabolic_le_pointStabilizer (borel_le_parabolic₂ h)
  obtain ⟨z,hz⟩ := (mem_pointStabilizer_iff _).mp hp
  have hh := congrFun hz 1
  simp only [shortMover,mul_inv_rev,rootF_inv,weylS_inverse] at hh
  change (-1 : ZMod 3)=(z : ZMod 3)*0 at hh
  norm_num at hh
/-- The same torus involution moves a neighbor at the long endpoint. -/
theorem longMover_not_fixed : longMover.val⁻¹*a*longMover.val∉borel := by
  intro h
  have hh := (borel_le_shortPlaneStabilizer h).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  simp only [longMover,mul_inv_rev,rootE_inv,weylR_inverse] at hh
  change (1 : ZMod 3)=0 at hh
  norm_num at hh
end Atlas.G2.TernaryTorus

namespace Atlas.G2.TernaryTorus
theorem torus_square (g : MG) (hg : g∈splitTorus) : g^2=1 := by
  obtain ⟨⟨l,m⟩,rfl⟩ := hg
  change (torus l m)^2=1
  rw [pow_two,torus_product]
  have hh : ∀a : (ZMod 3)ˣ,a*a=1 := by decide +kernel
  rw [hh,hh]
  exact torusHom.map_one
end Atlas.G2.TernaryTorus

namespace Atlas.G2.TernaryTorus
private theorem unipotent_fixed (v : Fin 6 → ZMod 3)
    (ha : Commute a (unipotentProduct v)) (hb : Commute b (unipotentProduct v)) : v=0 := by
  have he (l m : (ZMod 3)ˣ) (h : Commute (torus l m) (unipotentProduct v)) :
      torusUnipotentParameters l m v=v := by
    apply unipotentProduct_injective
    rw [←torus_unipotentProduct,h.eq,mul_inv_cancel_right]
  have h1 := he (-1) 1 ha
  have h2 := he 1 (-1) hb
  ext i
  have hh1 := congrFun h1 i
  have hh2 := congrFun h2 i
  have hneg : ∀ z : ZMod 3, -z=z → z=0 := by decide +kernel
  fin_cases i <;> norm_num [torusUnipotentParameters] at hh1 hh2 ⊢ <;>
    first | exact hneg _ hh1 | exact hneg _ hh2

/-- Centralizing the two generators of the ternary torus kills all unipotent coordinates. -/
theorem borel_centralizer_le_torus (g : MG) (hg : g∈borel)
    (ha : Commute a g) (hb : Commute b g) : g∈splitTorus := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := ZMod 3)).surjective ⟨g,hg⟩
  have he' : u.val*t.val=g := congrArg Subtype.val he
  have hat : Commute a t.val := by
    obtain ⟨t,⟨⟨l,m⟩,rfl⟩⟩ := t
    change Commute (torus (-1 : (ZMod 3)ˣ) 1) (torus l m)
    exact (Commute.all (-1,1) (l,m)).map (torusHom (K := ZMod 3))
  have hbt : Commute b t.val := by
    obtain ⟨t,⟨⟨l,m⟩,rfl⟩⟩ := t
    exact (Commute.all (1,-1) (l,m)).map torusHom
  have hau : Commute a u.val := by
    change a*u.val=u.val*a
    apply mul_right_cancel (b := t.val)
    calc
      a*u.val*t.val = a*g := by rw [mul_assoc,he']
      _ = g*a := ha.eq
      _ = u.val*a*t.val := by rw [←he',mul_assoc,←hat.eq,←mul_assoc]
  have hbu : Commute b u.val := by
    change b*u.val=u.val*b
    apply mul_right_cancel (b := t.val)
    calc
      b*u.val*t.val = b*g := by rw [mul_assoc,he']
      _ = g*b := hb.eq
      _ = u.val*b*t.val := by rw [←he',mul_assoc,←hbt.eq,←mul_assoc]
  obtain ⟨u,hu⟩ := u
  rw [unipotent_eq_range] at hu
  obtain ⟨v,rfl⟩ := hu
  have hv := unipotent_fixed v hau hbu
  change unipotentProduct v*t.val=g at he'
  rw [hv,unipotentProduct_zero,one_mul] at he'
  exact he' ▸ t.property

/-- The only torus element centralized by both Weyl reflections is the identity. -/
theorem torus_weyl_centralizer (g : MG) (hg : g∈splitTorus)
    (hs : Commute weylS g) (hr : Commute weylR g) : g=1 := by
  obtain ⟨⟨l,m⟩,rfl⟩ := hg
  have h1 := congrArg (fun g : MG => g.val (basisVector 0) 1) hs.eq
  have h2 := congrArg (fun g : MG => g.val (basisVector 1) 2) hr.eq
  simp [-ZMod.inv_coe_unit,torusHom,torus,torusEquiv,torusLinear,torusWeights,
    weylS,weylSEquiv,weylSLinear,weylSApply,basisVector] at h1
  simp [-ZMod.inv_coe_unit,torusHom,torus,torusEquiv,torusLinear,torusWeights,
    weylR,weylREquiv,weylRLinear,weylRApply,basisVector] at h2
  have hlm : l=m := Units.ext h1
  subst m
  have hl : l=1 := by
    apply Units.ext
    simpa [-ZMod.inv_coe_unit] using h2
  subst l
  exact torusHom.map_one
end Atlas.G2.TernaryTorus
