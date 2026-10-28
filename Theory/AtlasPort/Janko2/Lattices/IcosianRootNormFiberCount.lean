/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootNormFiberCount.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRootNormFibers
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourFinite

/-!
# Icosian Root Norm Fiber Count

Fixed-norm roots are counted by determinant-glue words and their three
scalar reduction fibers. The structural fiber equivalence gives
240 times the product of the explicitly supplied fiber cardinalities.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootNormFiberCount.lean`, revision
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

/-- Count actual fixed-norm roots by the structural determinant-glue base and
three actual scalar reduction fibers. Scalar fiber sizes remain explicit
hypotheses until the corresponding norm-shell theorems are instantiated. -/
theorem icosianRootsWithNorms_card
    (n : Fin 3 → GoldenRational) (d : Fin 3 → GoldenFour) (k : Fin 3 → ℕ)
    (hn : (∑ i,n i)=4) (hd0 : d 0+d 1+d 2=0)
    (hd : ∀ i (x : icosianOrder),icosianNorm x.val=n i → Matrix.det (icosianModuloTwo x)=d i)
    (hne : ∃ i,d i≠0) (hk : ∀ i,0<k i)
    (hf : ∀ i (m : IcosianMatrix),Matrix.det m=d i → m≠0 →
      Nat.card (IcosianScalarNormReductionFiber (n i) m)=k i) :
    Nat.card (IcosianRootsWithNorms n)=240*∏ i,k i := by
  have hbase : Nat.card (IcosianDeterminantGlue d)=240 :=
    icosianDeterminantGlue_card_four (by simpa only [Nat.card_eq_fintype_card] using goldenFour_card) d hd0
  let _ : Finite (IcosianDeterminantGlue d) := Nat.finite_of_card_ne_zero (by rw [hbase]; decide)
  let _ : Fintype (IcosianDeterminantGlue d) := Fintype.ofFinite _
  have hc (m : IcosianDeterminantGlue d) (i : Fin 3) :
      Nat.card (IcosianScalarNormReductionFiber (n i) (m.val.val i))=k i :=
    hf i _ (m.property.1 i) (icosianDeterminantGlue_block_ne_zero d m i)
  let _ (m : IcosianDeterminantGlue d) (i : Fin 3) :
      Finite (IcosianScalarNormReductionFiber (n i) (m.val.val i)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.ne_of_gt (hk i))
  rw [Nat.card_congr (icosianRootsWithNormsEquiv n d hn hd hne),Nat.card_sigma]
  simp_rw [Nat.card_pi,hc]
  rw [Finset.sum_const,Finset.card_univ,← Nat.card_eq_fintype_card,
    hbase]
  simp

end Atlas.Lattices
