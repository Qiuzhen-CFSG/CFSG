module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The root formulas use the licensed split-octonion model from
Atlas/LinearGroups/G2, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. Changes: ternary radical coordinates,
central cubic extensions, and the literal parabolic generator actions.
-/

public import Theory.SpecificGroups.G2.TernaryCoreCoordinates
public import Mathlib.Tactic.ReduceModChar

/-!
# Full generator actions on the ternary G₂ radicals

The omitted simple-root element and Weyl reflection have explicit actions
on all four quotient coordinates, including the invariant center plane.
The Weyl reflection negates the cubic commutator coordinate. Together with
the positive-root and torus formulas, these calculations prove normalization
by each whole parabolic, with the literal ambient conjugation conventions.

This supplies the model action data used in the compatible endpoint
construction for Aschbacher–Smith I.4.5, printed p.417. Identifying the
original quotient modules and matching both maps on the whole Borel remain
separate source obligations.
-/

@[expose] public section
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup Theory.GroupTheory
namespace Atlas.G2.TernaryCore
/-- The Weyl action on the actual four-dimensional quotient coordinates. -/
def shortWeyl (v : V) : V := Multiplicative.ofAdd ![v.toAdd 3,v.toAdd 2,v.toAdd 1,v.toAdd 0]
/-- The omitted simple root acts nontrivially on the full quotient module. -/
def shortRoot (v : V) : V := Multiplicative.ofAdd ![v.toAdd 0-v.toAdd 3,v.toAdd 1+v.toAdd 2+v.toAdd 3,v.toAdd 2-v.toAdd 3,v.toAdd 3]

theorem short_weyl (k : (ZMod 3)) (v : V) :
    (weylS:Model (ZMod 3))*(short k v:Model (ZMod 3))*weylS⁻¹=
      (short (-k) (shortWeyl v):Model (ZMod 3)) := by
  have hw : (weylS:Model (ZMod 3))⁻¹=weylS := inv_eq_of_mul_eq_one_right (by
    rw [←pow_two,weylS_sq])
  rw [hw]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [short,shortWeyl,unipotentProduct,weylS,weylSEquiv,weylSLinear,weylSApply,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
      rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
      rootDApply,rootEApply,rootFApply] <;> ring_nf
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char


/-- The Weyl action on the actual four-dimensional quotient coordinates. -/
def longWeyl (v : V) : V := Multiplicative.ofAdd ![v.toAdd 1,v.toAdd 0,v.toAdd 3,v.toAdd 2]
/-- The omitted simple root acts nontrivially on the full quotient module. -/
def longRoot (v : V) : V := Multiplicative.ofAdd ![v.toAdd 0-v.toAdd 1+v.toAdd 3,v.toAdd 1+v.toAdd 3,v.toAdd 2+v.toAdd 3,v.toAdd 3]

theorem long_weyl (k : (ZMod 3)) (v : V) :
    (weylR:Model (ZMod 3))*(long k v:Model (ZMod 3))*weylR⁻¹=
      (long (-k) (longWeyl v):Model (ZMod 3)) := by
  have hw : (weylR:Model (ZMod 3))⁻¹=weylR := inv_eq_of_mul_eq_one_right (by
    rw [←pow_two,weylR_sq])
  rw [hw]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [long,longWeyl,unipotentProduct,weylR,weylREquiv,weylRLinear,weylRApply,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,
      rootDEquiv,rootEEquiv,rootFEquiv,rootALinear,rootBLinear,rootCLinear,
      rootDLinear,rootELinear,rootFLinear,rootAApply,rootBApply,rootCApply,
      rootDApply,rootEApply,rootFApply] <;> ring_nf
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char


/-- The actual omitted simple-root element gives the full quotient action. -/
theorem short_root (k : (ZMod 3)) (v : V) :
    rootF 1*(short k v:Model (ZMod 3))*(rootF 1)⁻¹=(short k (shortRoot v):Model (ZMod 3)) := by
  have hr : rootF (1:(ZMod 3))=unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  change rootF 1*unipotentProduct _*(rootF 1)⁻¹=unipotentProduct _
  rw [hr,unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> dsimp [shortRoot,unipotentProductParameters,unipotentInverseParameters]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char

/-- The actual omitted simple-root element gives the full quotient action. -/
theorem long_root (k : (ZMod 3)) (v : V) :
    rootE 1*(long k v:Model (ZMod 3))*(rootE 1)⁻¹=(long k (longRoot v):Model (ZMod 3)) := by
  have hr : rootE (1:(ZMod 3))=unipotentProduct ![0,0,0,0,1,0] := by simp [unipotentProduct]
  change rootE 1*unipotentProduct _*(rootE 1)⁻¹=unipotentProduct _
  rw [hr,unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> dsimp [longRoot,unipotentProductParameters,unipotentInverseParameters]
  all_goals ring_nf
  all_goals reduce_mod_char
  all_goals try simp only [ZMod.pow_card]
  all_goals ring_nf
  all_goals reduce_mod_char
private theorem unipotent_normalizes_fiveRoot (i : Fin 6) (hi : i=4 ∨ i=5) :
    unipotent (K:=ZMod 3) ≤ normalizer (fiveRootSubgroup (F:=ZMod 3) i hi:Set (Model (ZMod 3))) := by
  have hc : ∀ g∈unipotent (K:=ZMod 3),∀ x∈fiveRootSubgroup i hi,g*x*g⁻¹∈fiveRootSubgroup i hi := by
    intro g hg x hx
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    obtain ⟨u,hu,rfl⟩ := hx
    rw [unipotentProduct_inv,unipotentProduct_mul,unipotentProduct_mul]
    refine ⟨_,?_,rfl⟩
    rcases hi with rfl | rfl <;> simp [unipotentProductParameters,unipotentInverseParameters,hu]
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc g hg x
  · intro hx
    have h := hc g⁻¹ (unipotent.inv_mem hg) _ hx
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using h

private theorem torus_normalizes_fiveRoot (i : Fin 6) (hi : i=4 ∨ i=5) :
    splitTorus (K:=ZMod 3) ≤ normalizer (fiveRootSubgroup (F:=ZMod 3) i hi:Set (Model (ZMod 3))) := by
  have hc : ∀ g∈splitTorus (K:=ZMod 3),∀ x∈fiveRootSubgroup i hi,g*x*g⁻¹∈fiveRootSubgroup i hi := by
    rintro g ⟨⟨l,m⟩,rfl⟩ x ⟨t,ht,rfl⟩
    change torus l m*unipotentProduct t*(torus l m)⁻¹∈fiveRootSubgroup i hi
    rw [torus_unipotentProduct]
    refine ⟨_,?_,rfl⟩
    rcases hi with rfl | rfl <;> simp [torusUnipotentParameters,ht]
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc g hg x
  · intro hx
    have h := hc g⁻¹ (splitTorus.inv_mem hg) _ hx
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using h

private theorem short_weyl_normalizes :
    (weylS:Model (ZMod 3))∈normalizer (radical₁ (F:=ZMod 3):Set (Model (ZMod 3))) := by
  have hc : ∀ x∈radical₁ (F:=ZMod 3),weylS*x*weylS⁻¹∈radical₁ := by
    intro x hx
    obtain ⟨k,v,h⟩ := short_surjective ⟨x,hx⟩
    have he := congrArg Subtype.val h
    change (short k v:Model (ZMod 3))=x at he
    rw [←he,short_weyl]
    exact (short _ _).property
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc x
  · intro hx
    have h := hc _ hx
    have he : (weylS:Model (ZMod 3))*(weylS*x*weylS⁻¹)*weylS⁻¹=x := by
      calc
        _=(weylS*weylS)*x*(weylS*weylS)⁻¹ := by group
        _=x := by rw [←pow_two,weylS_sq]; simp
    rwa [he] at h

/-- The whole actual ternary parabolic normalizes this five-root core. -/
theorem short_parabolic_normalizes :
    parabolic₁ (F:=ZMod 3) ≤ normalizer (radical₁ (F:=ZMod 3):Set (Model (ZMod 3))) :=
  sup_le (sup_le (unipotent_normalizes_fiveRoot 5 (Or.inr rfl))
    (torus_normalizes_fiveRoot 5 (Or.inr rfl)))
    ((closure_le _).mpr (by simpa using short_weyl_normalizes))

private theorem long_weyl_normalizes :
    (weylR:Model (ZMod 3))∈normalizer (radical₂ (F:=ZMod 3):Set (Model (ZMod 3))) := by
  have hc : ∀ x∈radical₂ (F:=ZMod 3),weylR*x*weylR⁻¹∈radical₂ := by
    intro x hx
    obtain ⟨k,v,h⟩ := long_surjective ⟨x,hx⟩
    have he := congrArg Subtype.val h
    change (long k v:Model (ZMod 3))=x at he
    rw [←he,long_weyl]
    exact (long _ _).property
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc x
  · intro hx
    have h := hc _ hx
    have he : (weylR:Model (ZMod 3))*(weylR*x*weylR⁻¹)*weylR⁻¹=x := by
      calc
        _=(weylR*weylR)*x*(weylR*weylR)⁻¹ := by group
        _=x := by rw [←pow_two,weylR_sq]; simp
    rwa [he] at h

/-- The whole actual ternary parabolic normalizes this five-root core. -/
theorem long_parabolic_normalizes :
    parabolic₂ (F:=ZMod 3) ≤ normalizer (radical₂ (F:=ZMod 3):Set (Model (ZMod 3))) :=
  sup_le (sup_le (unipotent_normalizes_fiveRoot 4 (Or.inl rfl))
    (torus_normalizes_fiveRoot 4 (Or.inl rfl)))
    ((closure_le _).mpr (by simpa using long_weyl_normalizes))

end Atlas.G2.TernaryCore
