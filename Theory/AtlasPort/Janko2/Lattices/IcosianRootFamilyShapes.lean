/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootFamilyShapes.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootCDFamilies
public import Theory.AtlasPort.Janko2.Lattices.IcosianAxisRoots
public import Theory.AtlasPort.Janko2.Lattices.IcosianEdgeRoots
public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormShapes

/-!
# Icosian Root Family Shapes

The four coordinate-norm shapes uniquely classify the actual roots.
Norm-shape exhaustion and reconstruction identify the shape fibers
with the axis, edge, and two remaining parametrized families.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootFamilyShapes.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Matrix QuadraticAlgebra

def icosianRootShapeWord : Fin 4 → Fin 3 → GoldenInteger :=
  ![![0,0,4],![0,2,2],icosianRootCNorms,icosianRootDNorms]

def HasIcosianRootShape (r : IcosianRoot) (i : Fin 4) : Prop :=
  List.Perm [icosianRootNormWord r 0,icosianRootNormWord r 1,icosianRootNormWord r 2]
    [icosianRootShapeWord i 0,icosianRootShapeWord i 1,icosianRootShapeWord i 2]

theorem icosianRootShape_unique (r : IcosianRoot) {i j : Fin 4}
    (hi : HasIcosianRootShape r i) (hj : HasIcosianRootShape r j) : i=j := by
  have h := hi.symm.trans hj
  have hsep : ∀ i j : Fin 4,
      List.Perm [icosianRootShapeWord i 0,icosianRootShapeWord i 1,icosianRootShapeWord i 2]
        [icosianRootShapeWord j 0,icosianRootShapeWord j 1,icosianRootShapeWord j 2] → i=j := by
    decide +kernel
  exact hsep i j h

theorem icosianRootShape_exhaustive (r : IcosianRoot) : ∃ i,HasIcosianRootShape r i := by
  have h := icosianRoot_norm_shapes r.val r.property.1 r.property.2
  rcases h with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · refine ⟨3,?_⟩
    change List.Perm _ [1,(ω : GoldenInteger)^2,(1-ω)^2]
    have he : [(1 : GoldenInteger),ω^2,(1-ω)^2]=[1,⟨1,1⟩,⟨2,-1⟩] := by decide +kernel
    rw [he]
    exact h

theorem icosianRootNormWord_zero (r : IcosianRoot) (i : Fin 3)
    (h : icosianRootNormWord r i=0) : r.val i=0 := by
  apply (icosianIntegralNorm_real_zero _).mp
  exact congrArg QuadraticAlgebra.re h

theorem icosianRootShape_axis (r : IcosianRoot) :
    HasIcosianRootShape r 0 ↔ IsIcosianAxisRoot r := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := Atlas.triple_perm_exists (icosianRootNormWord r) ![0,0,4] h
    refine ⟨p 2,fun j hj => icosianRootNormWord_zero r j ?_⟩
    rw [hp]
    have hk : p.symm j≠2 := by
      intro he
      exact hj (by simpa using congrArg p he)
    generalize p.symm j=k at *
    fin_cases k <;> simp_all
  · rintro ⟨i,hi⟩
    have hw (j : Fin 3) : icosianRootNormWord r j=if j=i then 4 else 0 := by
      apply icosianRootNormWord_of_norm
      split_ifs with h
      · subst j
        simpa only [map_ofNat] using icosianRoot_single_norm r i hi
      · simp [hi j h,icosianNorm]
    have he (j : Fin 3) : icosianRootNormWord r j=
        (![0,0,4] : Fin 3 → GoldenInteger) ((Equiv.swap 2 i).symm j) := by
      rw [hw]
      fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]
    change List.Perm _ [0,0,4]
    simp only [he]
    exact Atlas.triple_perm_reindex (Equiv.swap 2 i) (![0,0,4] : Fin 3 → GoldenInteger)

theorem icosianRootShape_edge (r : IcosianRoot) :
    HasIcosianRootShape r 1 ↔ r∈Set.range icosianEdgeRootParameter := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := Atlas.triple_perm_exists (icosianRootNormWord r) ![0,2,2] h
    apply icosianEdgeRoot_recognition r (p 0)
    · apply icosianRootNormWord_zero
      simp [hp]
    · intro j hj
      have hk : p.symm j≠0 := by
        intro he
        exact hj (by simpa using congrArg p he)
      have hw : icosianRootNormWord r j=2 := by
        rw [hp]
        generalize p.symm j=k at *
        fin_cases k <;> simp_all
      have he := congrArg goldenIntegerToRational hw
      simpa [icosianRootNormWord,icosianIntegralNorm_spec,map_ofNat] using he
  · rintro ⟨p,rfl⟩
    have hw (j : Fin 3) : icosianRootNormWord (icosianEdgeRootParameter p) j=
        if j=p.1 then 0 else 2 := by
      apply icosianRootNormWord_of_norm
      split_ifs with h
      · subst j
        simp [icosianEdgeRootParameter_zero,icosianNorm]
      · simpa only [map_ofNat] using icosianEdgeRootParameter_norm p j h
    have he (j : Fin 3) : icosianRootNormWord (icosianEdgeRootParameter p) j=
        (![0,2,2] : Fin 3 → GoldenInteger) ((Equiv.swap 0 p.1).symm j) := by
      rw [hw]
      rcases p with ⟨i,p⟩
      fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_def]
    change List.Perm _ [0,2,2]
    simp only [he]
    exact Atlas.triple_perm_reindex (Equiv.swap 0 p.1) (![0,2,2] : Fin 3 → GoldenInteger)

theorem icosianRootShape_c (r : IcosianRoot) :
    HasIcosianRootShape r 2 ↔ r∈Set.range icosianRootCParameter := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := Atlas.triple_perm_exists (icosianRootNormWord r) icosianRootCNorms h
    apply icosianRootC_recognition r (p 2)
    intro j
    rw [hp]
    have he : j=p 2 ↔ p.symm j=2 := by
      constructor
      · rintro rfl; exact p.symm_apply_apply 2
      · intro h; simpa using congrArg p h
    simp only [he]
    generalize p.symm j=k
    fin_cases k <;> simp [icosianRootCNorms]
  · rintro ⟨p,rfl⟩
    change List.Perm _ [icosianRootCNorms 0,icosianRootCNorms 1,icosianRootCNorms 2]
    exact (by simpa only [icosianRootNormWord_permute,
      icosianRootCParameter,icosianRootCStandard_word] using
      Atlas.triple_perm_reindex (Equiv.swap 2 p.1) icosianRootCNorms)

theorem icosianRootShape_d (r : IcosianRoot) :
    HasIcosianRootShape r 3 ↔ r∈Set.range icosianRootDParameter := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := Atlas.triple_perm_exists (icosianRootNormWord r) icosianRootDNorms h
    exact icosianRootD_recognition r p hp
  · rintro ⟨p,rfl⟩
    change List.Perm _ [icosianRootDNorms 0,icosianRootDNorms 1,icosianRootDNorms 2]
    exact (by simpa only [icosianRootDParameter_word] using
      Atlas.triple_perm_reindex p.1 icosianRootDNorms)

end Atlas.Lattices
