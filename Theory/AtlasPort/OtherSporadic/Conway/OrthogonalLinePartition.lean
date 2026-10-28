/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalLinePartition.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineSuborbits
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineLocalOrder

/-!
The five classes of orthogonal minimum lines and their cardinalities.
The proof descends the explicit minimum-vector partition through antipodal identification.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalLinePartition.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

def orthogonalLineIndex (i j : Omega) (l : OrthogonalMinimumLines (minimumPairPlus i j)) : Fin 5 :=
  orthogonalClassIndex i (Classical.choose l.prop)

theorem orthogonalLineIndex_eq (i j : Omega) (l : OrthogonalMinimumLines (minimumPairPlus i j))
    (v : leech) (he : antipodalLine v = l.val) :
    orthogonalLineIndex i j l = orthogonalClassIndex i v := by
  have hh := (Classical.choose_spec l.prop).2
  have h := (antipodalLine_eq_iff _ _).mp (hh.trans he.symm)
  rcases h with h | h
  · exact congrArg (orthogonalClassIndex i) h
  · change orthogonalClassIndex i (Classical.choose l.prop) = _
    rw [h,orthogonalClassIndex_neg]

def orthogonalClassLine (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) : OrthogonalMinimumLines (minimumPairPlus i j) :=
  ⟨antipodalLine (orthogonalClassValue i j t x),orthogonalClassValue i j t x,
    orthogonalClass_good i j hij t x,rfl⟩

theorem orthogonalClassLine_index (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) : orthogonalLineIndex i j (orthogonalClassLine i j hij t x) = t :=
  (orthogonalLineIndex_eq i j _ _ rfl).trans (orthogonalClassIndex_value i j hij t x)

theorem orthogonalLine_partition (i j : Omega) (hij : i ≠ j)
    (l : OrthogonalMinimumLines (minimumPairPlus i j)) :
    ∃ x : OrthogonalClassType i j (orthogonalLineIndex i j l),
      orthogonalClassLine i j hij _ x = l := by
  obtain ⟨v,hv,he⟩ := l.prop
  obtain ⟨t,x,hx⟩ := orthogonalClass_exhaustive i j hij v hv.1 hv.2
  have ht : orthogonalLineIndex i j l = t :=
    (orthogonalLineIndex_eq i j l _ ((congrArg antipodalLine hx).trans he)).trans
      (orthogonalClassIndex_value i j hij t x)
  subst t
  exact ⟨x,Subtype.ext ((congrArg antipodalLine hx).trans he)⟩

theorem orthogonalLine_index_transitive (i j : Omega) (hij : i ≠ j)
    (l m : OrthogonalMinimumLines (minimumPairPlus i j))
    (he : orthogonalLineIndex i j l = orthogonalLineIndex i j m) :
    ∃ g : MulAction.stabilizer (fullVectorStabilizer (minimumPairPlus i j))
        (distinguishedOrthogonalLine i j hij), g • l = m := by
  obtain ⟨x,hx⟩ := orthogonalLine_partition i j hij l
  have hym : ∃ y : OrthogonalClassType i j (orthogonalLineIndex i j l),
      orthogonalClassLine i j hij _ y = m := by
    rw [he]
    exact orthogonalLine_partition i j hij m
  obtain ⟨y,hy⟩ := hym
  obtain ⟨r,hr⟩ := orthogonalClass_transitive i j hij _ x y
  let s := (orthogonalLineMonomialEquiv i j hij).symm r
  have hs : s.val ∈ MulAction.stabilizer (fullVectorStabilizer (minimumPairPlus i j))
      (distinguishedOrthogonalLine i j hij) :=
    (le_of_eq (distinguishedOrthogonalLine_stabilizer i j hij).symm) s.prop
  refine ⟨⟨s.val,hs⟩,?_⟩
  apply Subtype.ext
  change leechCentralProjection r.val.val • l.val = m.val
  rw [← hx,← hy]
  exact (projection_antipodalLine r.val.val _).trans (congrArg antipodalLine hr)

def orthogonalLineFiberOrbitEquiv (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) :
    {l : OrthogonalMinimumLines (minimumPairPlus i j) // orthogonalLineIndex i j l = t} ≃
      MulAction.orbit (orthogonalLineStabilizer i j)
        (antipodalLine (orthogonalClassValue i j t x)) := by
  let f : {l : OrthogonalMinimumLines (minimumPairPlus i j) // orthogonalLineIndex i j l = t} →
      MulAction.orbit (orthogonalLineStabilizer i j)
        (antipodalLine (orthogonalClassValue i j t x)) := fun l => ⟨l.val.val,by
    have he : orthogonalLineIndex i j (orthogonalClassLine i j hij t x) =
        orthogonalLineIndex i j l.val := (orthogonalClassLine_index i j hij t x).trans l.prop.symm
    obtain ⟨g,hg⟩ := orthogonalLine_index_transitive i j hij _ _ he
    refine ⟨⟨g.val,(le_of_eq (distinguishedOrthogonalLine_stabilizer i j hij)) g.prop⟩,?_⟩
    exact congrArg Subtype.val hg⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have he : a.val.val = b.val.val := congrArg
      (fun z : MulAction.orbit (orthogonalLineStabilizer i j)
        (antipodalLine (orthogonalClassValue i j t x)) => z.val) h
    exact Subtype.ext (Subtype.ext he)
  · intro l
    obtain ⟨v,hv,he⟩ := (orthogonalLineOrbitEquiv i j hij _ l).prop
    obtain ⟨y,hy⟩ := (orthogonalClass_monomial_orbit i j hij t x v).mp hv
    let m := orthogonalClassLine i j hij t y
    exact ⟨⟨m,orthogonalClassLine_index i j hij t y⟩,
      Subtype.ext ((congrArg antipodalLine hy).trans he)⟩

end Atlas.Conway
