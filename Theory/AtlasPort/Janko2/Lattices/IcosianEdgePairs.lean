/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianEdgePairs.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootPermutations
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTwoReductionFibers
public import Theory.AtlasPort.Janko2.Codes.IcosianDeterminantGlue
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite

/-!
# Icosian Edge Pairs

Pairs of norm-two icosians with equal reduction in the common row ideal
are parametrized by nonzero rows and two reduction fibers. The actual
scalar fiber counts give 960 such pairs.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianEdgePairs.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix BigOperators

abbrev IcosianNonzeroRow := {y : IcosianRow GoldenFour // y≠0}

def icosianEdgeMatrix (y : IcosianNonzeroRow) : IcosianMatrix :=
  fun r j => if r=0 then y.val j else 0

theorem icosianEdgeMatrix_det (y : IcosianNonzeroRow) : Matrix.det (icosianEdgeMatrix y)=0 := by
  simp [Matrix.det_fin_two,icosianEdgeMatrix]

theorem icosianEdgeMatrix_ne_zero (y : IcosianNonzeroRow) : icosianEdgeMatrix y≠0 := by
  intro h
  apply y.property
  funext j
  exact congrFun (congrFun h 0) j

abbrev IcosianEdgePair := {p : IcosianNormTwo × IcosianNormTwo //
  icosianModuloTwo p.1.val=icosianModuloTwo p.2.val ∧ p.1.val∈icosianP}

def IcosianEdgeParameters := (y : IcosianNonzeroRow) ×
  ({x : IcosianNormTwo // icosianModuloTwo x.val=icosianEdgeMatrix y} ×
   {x : IcosianNormTwo // icosianModuloTwo x.val=icosianEdgeMatrix y})

def icosianEdgePairRow (p : IcosianEdgePair) : IcosianNonzeroRow :=
  ⟨fun j => icosianModuloTwo p.val.1.val 0 j,by
    intro h
    apply icosianNormTwo_reduction_ne_zero p.val.1
    funext r j
    fin_cases r
    · exact congrFun h j
    · exact p.property.2 j⟩

theorem icosianEdgePairRow_matrix (p : IcosianEdgePair) :
    icosianEdgeMatrix (icosianEdgePairRow p)=icosianModuloTwo p.val.1.val := by
  funext r j
  fin_cases r
  · rfl
  · exact (p.property.2 j).symm

theorem icosianEdgeFiberPair_heq {y z : IcosianNonzeroRow} (h : y=z)
    (a b : {x : IcosianNormTwo // icosianModuloTwo x.val=icosianEdgeMatrix y})
    (c d : {x : IcosianNormTwo // icosianModuloTwo x.val=icosianEdgeMatrix z})
    (ha : a.val=c.val) (hb : b.val=d.val) : HEq (a,b) (c,d) := by
  subst z
  apply heq_of_eq
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

def icosianEdgePairsEquiv
 : IcosianEdgeParameters ≃ IcosianEdgePair where
  toFun p := ⟨(p.2.1.val,p.2.2.val),p.2.1.property.trans p.2.2.property.symm,by
    intro j
    rw [p.2.1.property]
    rfl⟩
  invFun p := ⟨icosianEdgePairRow p,
    ⟨p.val.1,(icosianEdgePairRow_matrix p).symm⟩,
    ⟨p.val.2,p.property.1.symm.trans (icosianEdgePairRow_matrix p).symm⟩⟩
  left_inv p := by
    rcases p with ⟨y,x,z⟩
    have hy : icosianEdgePairRow
        ⟨(x.val,z.val),x.property.trans z.property.symm,by intro j; rw [x.property]; rfl⟩=y := by
      apply Subtype.ext
      funext j
      change icosianModuloTwo x.val.val 0 j=y.val j
      rw [x.property]
      rfl
    apply Sigma.ext hy
    exact icosianEdgeFiberPair_heq hy _ _ _ _ rfl rfl
  right_inv p := by rfl

theorem icosianNonzeroRow_card : Nat.card IcosianNonzeroRow=15 := by
  rw [icosianNonzeroRows_card]
  have h : Nat.card GoldenFour=4 := by simpa [Nat.card_eq_fintype_card] using goldenFour_card
  rw [h]
  norm_num

theorem icosianEdgePairs_card : Nat.card IcosianEdgePair=960 := by
  classical
  let _ := Fintype.ofFinite IcosianNonzeroRow
  rw [← Nat.card_congr icosianEdgePairsEquiv]
  unfold IcosianEdgeParameters
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod,icosianNormTwoReduction_fiber_card _ (icosianEdgeMatrix_det _)
    (icosianEdgeMatrix_ne_zero _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  have h : Fintype.card IcosianNonzeroRow=15 := by
    simpa [Nat.card_eq_fintype_card] using icosianNonzeroRow_card
  rw [h]

end Atlas.Lattices
