/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointShapeNormCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootNormLevelCounts

/-!
# IcosianRootPointShapeNormCounts

Root shape and coordinate norm descend simultaneously to root points. Scalar-fiber
counting gives nine local pieces and their exhaustive labels.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianRootPointShapeNormCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped BigOperators Matrix QuadraticAlgebra

abbrev IcosianRootPointShapeNormLevel (s : Fin 4) (i : Fin 3) (a : GoldenInteger) :=
  {p : IcosianRootPoint // HasIcosianRootPointShape p s ∧ icosianRootPointNormWord p i = a}

def icosianRootShapeNormLevelToPoint (s : Fin 4) (i : Fin 3) (a : GoldenInteger)
    (r : IcosianRootShapeNormLevel s i a) : IcosianRootPointShapeNormLevel s i a :=
  ⟨icosianRootToPoint r.val.val, ⟨r.val.val,rfl,r.val.property⟩,
    by rw [icosianRootPointNormWord_toPoint]; exact r.property⟩

def icosianRootShapeNormLevelPointFiberEquiv (s : Fin 4) (i : Fin 3) (a : GoldenInteger)
    (p : IcosianRootPointShapeNormLevel s i a) :
    {r : IcosianRootShapeNormLevel s i a // icosianRootShapeNormLevelToPoint s i a r = p} ≃
      {r : IcosianRoot // icosianRootToPoint r = p.val} where
  toFun r := ⟨r.val.val.val, congrArg Subtype.val r.property⟩
  invFun r := by
    have hs : HasIcosianRootShape r.val s := by
      obtain ⟨v,hv,hvs⟩ := p.property.1
      exact (icosianRootShape_of_same_point v r.val
        ((congrArg Subtype.val r.property).trans hv.symm) s).mpr hvs
    have hn : icosianRootNormWord r.val i = a := by
      rw [← icosianRootPointNormWord_toPoint,r.property]
      exact p.property.2
    exact ⟨⟨⟨r.val,hs⟩,hn⟩,Subtype.ext r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianRootPointShapeNormLevel_card_mul (s : Fin 4) (i : Fin 3) (a : GoldenInteger) :
    Nat.card (IcosianRootPointShapeNormLevel s i a) * 120 =
      Nat.card (IcosianRootShapeNormLevel s i a) := by
  let : Fintype (IcosianRootPointShapeNormLevel s i a) := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.sigmaPreimageEquiv (icosianRootShapeNormLevelToPoint s i a))
  rw [Nat.card_sigma] at he
  change (∑ p : IcosianRootPointShapeNormLevel s i a,
    Nat.card {r : IcosianRootShapeNormLevel s i a // icosianRootShapeNormLevelToPoint s i a r = p}) =
      Nat.card (IcosianRootShapeNormLevel s i a) at he
  have hf (p : IcosianRootPointShapeNormLevel s i a) :
      Nat.card {r : IcosianRootShapeNormLevel s i a // icosianRootShapeNormLevelToPoint s i a r = p} = 120 := by
    rw [Nat.card_congr (icosianRootShapeNormLevelPointFiberEquiv s i a p),
      icosianRootToPoint_fiber_card]
  simp_rw [hf] at he
  simpa only [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    nsmul_eq_mul,Nat.cast_id] using he

def icosianNineLocalShapeIndices : Fin 9 → Fin 4 := ![0,0,1,1,2,2,3,3,3]

def icosianNineLocalNormValues : Fin 9 → GoldenInteger := ![4,0,0,2,1,2,1,ω^2,(1-ω)^2]

theorem icosianRootShapeNormLevel_nine_card (k : Fin 9) :
    Nat.card (IcosianRootShapeNormLevel (icosianNineLocalShapeIndices k) 0
      (icosianNineLocalNormValues k)) = ![120,240,960,1920,15360,7680,3840,3840,3840] k := by
  fin_cases k
  · change Nat.card (IcosianRootShapeNormLevel 0 0 (4)) = 120
    rw [icosianRootShapeNormLevel_axis_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 0 0 (0)) = 240
    rw [icosianRootShapeNormLevel_axis_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 1 0 (0)) = 960
    rw [icosianRootShapeNormLevel_edge_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 1 0 (2)) = 1920
    rw [icosianRootShapeNormLevel_edge_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 2 0 (1)) = 15360
    rw [icosianRootShapeNormLevel_C_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 2 0 (2)) = 7680
    rw [icosianRootShapeNormLevel_C_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 3 0 (1)) = 3840
    rw [icosianRootShapeNormLevel_D_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 3 0 (ω^2)) = 3840
    rw [icosianRootShapeNormLevel_D_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel
  · change Nat.card (IcosianRootShapeNormLevel 3 0 ((1-ω)^2)) = 3840
    rw [icosianRootShapeNormLevel_D_card]
    simp only [Nat.card_eq_fintype_card]
    decide +kernel

theorem icosianRootPointShapeNormLevel_nine_card (k : Fin 9) :
    Nat.card (IcosianRootPointShapeNormLevel (icosianNineLocalShapeIndices k) 0
      (icosianNineLocalNormValues k)) = ![1,2,8,16,128,64,32,32,32] k := by
  have h := icosianRootPointShapeNormLevel_card_mul (icosianNineLocalShapeIndices k) 0
    (icosianNineLocalNormValues k)
  rw [icosianRootShapeNormLevel_nine_card] at h
  fin_cases k <;> dsimp at h ⊢ <;> omega

theorem icosianNineLocalData_injective :
    Function.Injective (fun k => (icosianNineLocalShapeIndices k,icosianNineLocalNormValues k)) := by
  decide +kernel

theorem icosianRootPointShapeNormLevel_nine_exhaustive (p : IcosianRootPoint) :
    ∃ k : Fin 9, HasIcosianRootPointShape p (icosianNineLocalShapeIndices k) ∧
      icosianRootPointNormWord p 0 = icosianNineLocalNormValues k := by
  obtain ⟨s,r,hr,hs⟩ := icosianRootPointShape_exhaustive p
  have hm : icosianRootNormWord r 0 ∈
      [icosianRootShapeWord s 0,icosianRootShapeWord s 1,icosianRootShapeWord s 2] :=
    hs.mem_iff.mp (by simp)
  have hfinite : ∀ s : Fin 4, ∀ a : GoldenInteger,
      a ∈ [icosianRootShapeWord s 0,icosianRootShapeWord s 1,icosianRootShapeWord s 2] →
      ∃ k : Fin 9, icosianNineLocalShapeIndices k = s ∧ a = icosianNineLocalNormValues k := by
    intro s a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> fin_cases s <;> decide +kernel
  obtain ⟨k,hk,ha⟩ := hfinite s _ hm
  refine ⟨k,hk.symm ▸ ⟨r,hr,hs⟩,?_⟩
  have hp : icosianRootToPoint r = p := Subtype.ext hr
  rw [← hp,icosianRootPointNormWord_toPoint]
  exact ha

end Atlas.Conway
