/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootNormLevelCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointNormWord

/-!
# IcosianRootNormLevelCounts

Shape parametrizations count roots at each coordinate norm. Dividing by the scalar
fibers yields the six projective norm-level counts and exhaustiveness.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootNormLevelCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators Matrix QuadraticAlgebra

private def levelParameterEquiv {A B X : Type*} (e : A × B ≃ X)
    (f : X → GoldenInteger) (w : A → GoldenInteger) (hw : ∀ p, f (e p) = w p.1)
    (a : GoldenInteger) : {x : X // f x = a} ≃ {i : A // w i = a} × B where
  toFun x := ⟨⟨(e.symm x.val).1, by rw [← hw, e.apply_symm_apply]; exact x.property⟩,
    (e.symm x.val).2⟩
  invFun p := ⟨e (p.1.val,p.2), by rw [hw]; exact p.1.property⟩
  left_inv x := Subtype.ext (e.apply_symm_apply x.val)
  right_inv p := by simp

private theorem levelParameter_card {A B X : Type*} (e : A × B ≃ X)
    (f : X → GoldenInteger) (w : A → GoldenInteger) (hw : ∀ p, f (e p) = w p.1)
    (a : GoldenInteger) : Nat.card {x : X // f x = a} = Nat.card {i : A // w i = a} * Nat.card B := by
  rw [Nat.card_congr (levelParameterEquiv e f w hw a), Nat.card_prod]

abbrev IcosianRootShapeNormLevel (s : Fin 4) (i : Fin 3) (a : GoldenInteger) :=
  {r : IcosianRootShapeFiber s // icosianRootNormWord r.val i = a}

private def shapeNormLevelEquiv (i : Fin 3) (a : GoldenInteger) :
    (Σ s : Fin 4, IcosianRootShapeNormLevel s i a) ≃ IcosianRootNormLevel i a :=
  Equiv.ofBijective (fun p => ⟨p.2.val.val,p.2.property⟩) (by
    constructor
    · rintro ⟨s,r⟩ ⟨t,q⟩ h
      have hr : r.val.val = q.val.val := congrArg Subtype.val h
      have st : s=t := icosianRootShape_unique r.val.val r.val.property
        (hr.symm ▸ q.val.property)
      subst t
      exact congrArg (Sigma.mk s) (Subtype.ext (Subtype.ext hr))
    · intro r
      obtain ⟨s,hs⟩ := icosianRootShape_exhaustive r.val
      exact ⟨⟨s,⟨r.val,hs⟩,r.property⟩,rfl⟩)

theorem icosianRootNormLevel_card_sum (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootNormLevel i a) = ∑ s : Fin 4, Nat.card (IcosianRootShapeNormLevel s i a) := by
  rw [← Nat.card_congr (shapeNormLevelEquiv i a), Nat.card_sigma]

private theorem axis_word (p : Fin 3 × icosianNormOneGroup) (i : Fin 3) :
    icosianRootNormWord (icosianAxisRoot p) i = if i = p.1 then 4 else 0 := by
  apply icosianRootNormWord_of_norm
  by_cases h : i = p.1
  · subst i
    simpa only [ite_true, map_ofNat] using
      icosianRoot_single_norm (icosianAxisRoot p) p.1
        (fun j hj => by simp [icosianAxisRoot,icosianSingle,hj])
  · simp only [h, if_false, map_zero]
    have hz : (icosianAxisRoot p).val i = 0 := by
      simp [icosianAxisRoot,icosianSingle,h]
    rw [hz]
    simp [icosianNorm]

private theorem edge_word (p : Fin 3 × IcosianEdgePair) (i : Fin 3) :
    icosianRootNormWord (icosianEdgeRootParameter p) i = if i = p.1 then 0 else 2 := by
  apply icosianRootNormWord_of_norm
  by_cases h : i = p.1
  · subst i
    simp only [icosianEdgeRootParameter_zero]
    simp [icosianNorm]
  · simpa only [h, if_false, map_ofNat] using icosianEdgeRootParameter_norm p i h

theorem icosianRootShapeNormLevel_axis_card (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootShapeNormLevel 0 i a) =
      Nat.card {j : Fin 3 // (if i = j then (4 : GoldenInteger) else 0) = a} * 120 := by
  rw [levelParameter_card (icosianAxisRootEquiv.trans icosianRootShapeFiberAxis.symm)
    (fun r => icosianRootNormWord r.val i) (fun j => if i = j then 4 else 0)
    (fun p => axis_word p i), icosianNormOneGroup_card]

theorem icosianRootShapeNormLevel_edge_card (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootShapeNormLevel 1 i a) =
      Nat.card {j : Fin 3 // (if i = j then (0 : GoldenInteger) else 2) = a} * 960 := by
  rw [levelParameter_card (icosianEdgeRootEquiv.trans icosianRootShapeFiberEdge.symm)
    (fun r => icosianRootNormWord r.val i) (fun j => if i = j then 0 else 2)
    (fun p => edge_word p i), icosianEdgePairs_card]

theorem icosianRootShapeNormLevel_C_card (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootShapeNormLevel 2 i a) =
      Nat.card {j : Fin 3 // (if i = j then (2 : GoldenInteger) else 1) = a} * 7680 := by
  rw [levelParameter_card (icosianRootCFamilyEquiv.trans icosianRootShapeFiberC.symm)
    (fun r => icosianRootNormWord r.val i) (fun j => if i = j then 2 else 1)
    (fun p => icosianRootCParameter_word p i), icosianRootCStandard_card]

theorem icosianRootShapeNormLevel_D_card (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootShapeNormLevel 3 i a) =
      Nat.card {p : Equiv.Perm (Fin 3) // icosianRootDNorms (p.symm i) = a} * 1920 := by
  rw [levelParameter_card (icosianRootDFamilyEquiv.trans icosianRootShapeFiberD.symm)
    (fun r => icosianRootNormWord r.val i) (fun p => icosianRootDNorms (p.symm i))
    (fun p => icosianRootDParameter_word p i), icosianRootDStandard_card]

def icosianRootCoordinateLevels : Fin 6 → GoldenInteger := ![4,0,1,2,ω^2,(1-ω)^2]

theorem icosianRootNormLevel_six_card (k : Fin 6) :
    Nat.card (IcosianRootNormLevel 0 (icosianRootCoordinateLevels k)) =
      ![120,1200,19200,9600,3840,3840] k := by
  rw [icosianRootNormLevel_card_sum, Fin.sum_univ_four]
  rw [icosianRootShapeNormLevel_axis_card,icosianRootShapeNormLevel_edge_card,
    icosianRootShapeNormLevel_C_card,icosianRootShapeNormLevel_D_card]
  simp only [Nat.card_eq_fintype_card]
  fin_cases k <;> decide +kernel

theorem icosianRootPointNormLevel_six_card (k : Fin 6) :
    Nat.card (IcosianRootPointNormLevel 0 (icosianRootCoordinateLevels k)) =
      ![1,10,160,80,32,32] k := by
  have h := icosianRootPointNormLevel_card_mul 0 (icosianRootCoordinateLevels k)
  rw [icosianRootNormLevel_six_card] at h
  fin_cases k <;> dsimp at h ⊢ <;> omega

theorem icosianRootCoordinateLevels_injective : Function.Injective icosianRootCoordinateLevels := by
  decide +kernel

theorem icosianRootNormLevel_exhaustive (r : IcosianRoot) (i : Fin 3) :
    ∃ k : Fin 6, icosianRootNormWord r i = icosianRootCoordinateLevels k := by
  obtain ⟨s,hs⟩ := icosianRootShape_exhaustive r
  have hm : icosianRootNormWord r i ∈
      [icosianRootNormWord r 0,icosianRootNormWord r 1,icosianRootNormWord r 2] := by
    fin_cases i <;> simp
  have ht := hs.mem_iff.mp hm
  have hfinite : ∀ s : Fin 4, ∀ a : GoldenInteger,
      a ∈ [icosianRootShapeWord s 0,icosianRootShapeWord s 1,icosianRootShapeWord s 2] →
        ∃ k : Fin 6, a = icosianRootCoordinateLevels k := by
    intro s a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> fin_cases s <;> decide +kernel
  exact hfinite s _ ht

theorem icosianRootPointNormLevel_exhaustive (p : IcosianRootPoint) (i : Fin 3) :
    ∃ k : Fin 6, icosianRootPointNormWord p i = icosianRootCoordinateLevels k :=
  icosianRootNormLevel_exhaustive p.property.choose i

end Atlas.Conway
