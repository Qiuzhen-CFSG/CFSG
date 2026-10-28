/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalMinimumLines.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.AntipodalCounting
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumLineOrder

/-!
The 46575 minimum lines orthogonal to a fixed minimum vector.
Antipodal counting and the proved orthogonal-vector transitivity identify the line action.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalMinimumLines.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

def orthogonalMinimumSet (v : leech) : Set leech :=
  {w | integerDot w.val w.val = 32 ∧ integerDot v.val w.val = 0}

instance (v : leech) : Finite (orthogonalMinimumSet v) := by
  let f : orthogonalMinimumSet v → LeechShell 4 := fun w => ⟨w.val,w.prop.1⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext (congrArg (fun z : LeechShell 4 => z.val) h))

def OrthogonalMinimumLines (v : leech) := AntipodalImage (orthogonalMinimumSet v)

instance (v : leech) : Finite (OrthogonalMinimumLines v) := inferInstanceAs (Finite (AntipodalImage _))

def orthogonalMinimumSetEquiv (i j : Omega) :
    orthogonalMinimumSet (minimumPairPlus i j) ≃ OrthogonalMinimumShell i j where
  toFun w := ⟨⟨w.val,w.prop.1⟩,w.prop.2⟩
  invFun w := ⟨w.val.val,w.val.prop,w.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orthogonalMinimumLines_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (OrthogonalMinimumLines (minimumPairPlus i j)) = 46575 := by
  have hn (v : leech) (w : leech) (hw : w ∈ orthogonalMinimumSet v) :
      -w ∈ orthogonalMinimumSet v := by
    change integerDot (-w.val) (-w.val) = 32 ∧ integerDot v.val (-w.val) = 0
    constructor
    · simpa [integerDot] using hw.1
    · simpa [integerDot,Finset.sum_neg_distrib] using congrArg Neg.neg hw.2
  have hz (v : leech) (w : leech) (hw : w ∈ orthogonalMinimumSet v) : w ≠ 0 :=
    minimum_vector_ne_zero ⟨w,hw.1⟩
  have h := antipodalImage_card (orthogonalMinimumSet (minimumPairPlus i j))
    (hn _) (hz _)
  rw [Nat.card_congr (orthogonalMinimumSetEquiv i j),orthogonalMinimumShell_card i j hij] at h
  change 2 * Nat.card (OrthogonalMinimumLines (minimumPairPlus i j)) = 93150 at h
  omega

theorem orthogonalMinimumLines_transporter (i j : Omega) (hij : i ≠ j)
    (l m : OrthogonalMinimumLines (minimumPairPlus i j)) :
    ∃ g : fullVectorStabilizer (minimumPairPlus i j),
      leechCentralProjection g.val • l.val = m.val := by
  obtain ⟨v,hv,he⟩ := l.prop
  obtain ⟨w,hw,hf⟩ := m.prop
  have horb := strict_overgroup_orthogonal_orbit_full ⊤ monomial_lt_full i j hij
    (⟨v,hv.1⟩ : LeechShell 4) hv.2 (⟨w,hw.1⟩ : LeechShell 4) hw.2
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp horb
  refine ⟨⟨g.val.val,g.prop⟩,?_⟩
  rw [← he,← hf,projection_antipodalLine]
  exact congrArg antipodalLine (congrArg Subtype.val hg)


instance orthogonalMinimumLinesAction (v : leech) :
    MulAction (fullVectorStabilizer v) (OrthogonalMinimumLines v) where
  smul g l := ⟨leechCentralProjection g.val • l.val,by
    obtain ⟨w,hw,he⟩ := l.prop
    refine ⟨g.val.val w,⟨(g.val.prop w w).trans hw.1,?_⟩,?_⟩
    · have h := g.val.prop v w
      change integerDot (g.val.val v).val (g.val.val w).val = _ at h
      rw [show g.val.val v = v from g.prop] at h
      exact h.trans hw.2
    · rw [← he]
      exact (projection_antipodalLine g.val w).symm⟩
  one_smul l := by
    apply Subtype.ext
    change leechCentralProjection 1 • l.val = l.val
    rw [map_one,one_smul]
  mul_smul g h l := by
    apply Subtype.ext
    change leechCentralProjection (g.val*h.val) • l.val =
      leechCentralProjection g.val • (leechCentralProjection h.val • l.val)
    rw [map_mul,mul_smul]

theorem orthogonalMinimumLines_pretransitive (i j : Omega) (hij : i ≠ j) :
    MulAction.IsPretransitive (fullVectorStabilizer (minimumPairPlus i j))
      (OrthogonalMinimumLines (minimumPairPlus i j)) := by
  constructor
  intro l m
  obtain ⟨g,hg⟩ := orthogonalMinimumLines_transporter i j hij l m
  exact ⟨g,Subtype.ext hg⟩

end Atlas.Conway
