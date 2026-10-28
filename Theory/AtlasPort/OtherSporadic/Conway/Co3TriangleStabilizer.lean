/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleBase
public import Theory.AtlasPort.OtherSporadic.Conway.CoordinateVectorStabilizer
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem monomial_fixes_normSix (m : GolayMonomialGroup) (a : Omega)
    (hm : (monomialEmbedding m).val (normSixVector a) = normSixVector a) :
    m.left.toAdd = 0 ∧ m.right.val a = a := by
  have hc (i : Omega) := congrArg (fun v : leech => v.val i) hm
  have hzero (i : Omega) : m.left.toAdd.val i = 0 := by
    have h := hc i
    rw [monomialEmbedding_apply,normSixVector_apply,normSixVector_apply] at h
    by_contra hn
    simp only [hn,ite_false] at h
    split_ifs at h
  refine ⟨Subtype.ext (funext hzero),?_⟩
  have h := hc (m.right.val a)
  rw [monomialEmbedding_apply,hzero,if_pos rfl,normSixVector_apply,
    Equiv.symm_apply_apply,if_pos rfl,normSixVector_apply] at h
  split_ifs at h with he
  · exact he
  · omega

theorem co3_triangle_fixer_eq_permutation (a : Omega) (g : LeechIsometryGroup)
    (hx : g.val (normSixVector a) = normSixVector a)
    (hu : g.val (oddMinimumVector a 0) = oddMinimumVector a 0) :
    ∃ p : Mathieu23PointModel a, permutationEmbedding p.val = g := by
  have hg : g ∈ monomialSubgroup := by
    apply coordinateEight_fixer_mem_monomial g a
    rw [← normSix_sub_oddMinimum,map_sub,hx,hu]
  obtain ⟨m,rfl⟩ := hg
  obtain ⟨hz,hp⟩ := monomial_fixes_normSix m a hx
  refine ⟨⟨m.right,hp⟩,?_⟩
  have he : m = SemidirectProduct.inr m.right := by
    apply SemidirectProduct.ext
    · exact hz
    · rfl
  change permutationEmbedding m.right = monomialEmbedding m
  rw [he]
  exact congrArg (fun f : Mathieu24CodeModel →* LeechIsometryGroup => f m.right) monomial_inr.symm

abbrev Co3TriangleStabilizer (a : Omega) :=
  MulAction.stabilizer (fullVectorStabilizer (normSixVector a)) (oddMinimumVector a 0)

def mathieu23TriangleEmbedding (a : Omega) : Mathieu23PointModel a →* Co3TriangleStabilizer a where
  toFun g := ⟨mathieu23ToNormSixStabilizer a g,mathieu23_fixes_triangle a g⟩
  map_one' := Subtype.ext ((mathieu23ToNormSixStabilizer a).map_one)
  map_mul' g h := Subtype.ext ((mathieu23ToNormSixStabilizer a).map_mul g h)

theorem mathieu23TriangleEmbedding_bijective (a : Omega) :
    Function.Bijective (mathieu23TriangleEmbedding a) := by
  constructor
  · intro g h he
    exact mathieu23ToNormSixStabilizer_injective a (congrArg Subtype.val he)
  · intro g
    obtain ⟨p,hp⟩ := co3_triangle_fixer_eq_permutation a g.val.val g.val.prop g.prop
    exact ⟨p,Subtype.ext (Subtype.ext hp)⟩

def mathieu23TriangleEquiv (a : Omega) : Mathieu23PointModel a ≃* Co3TriangleStabilizer a :=
  MulEquiv.ofBijective (mathieu23TriangleEmbedding a) (mathieu23TriangleEmbedding_bijective a)

end Atlas.Conway
