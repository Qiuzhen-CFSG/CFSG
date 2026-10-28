/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3Decompositions.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3EvenEndpoints
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3Decompositions.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Unordered pairs of minimum Leech vectors with specified sum. -/
def MinimumDecompositions (x : leech) := {p : Finset leech // ∃ y : leech,
  integerDot y.val y.val = 32 ∧ integerDot (x-y).val (x-y).val = 32 ∧ p = {y,x-y}}

def evenEndpointToDecomposition (a : Omega) (y : Co3EvenEndpoint a) :
    MinimumDecompositions (normSixVector a) :=
  ⟨{y.val,normSixVector a-y.val},y.val,y.prop.1,y.prop.2.1,rfl⟩

theorem evenEndpointToDecomposition_injective (a : Omega) :
    Function.Injective (evenEndpointToDecomposition a) := by
  intro y z he
  have hm : y.val ∈ ({z.val,normSixVector a-z.val} : Finset leech) := by
    have hh : ({y.val,normSixVector a-y.val} : Finset leech) = {z.val,normSixVector a-z.val} := congrArg Subtype.val he
    rw [← hh]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact Subtype.ext h
  · have h := congrArg (fun v : leech => v.val a) (Finset.mem_singleton.mp h)
    change y.val.val a = (normSixVector a).val a-z.val.val a at h
    rw [normSixVector_apply,if_pos rfl] at h
    have hy := y.prop.2.2 a
    have hz := z.prop.2.2 a
    omega

theorem evenEndpointToDecomposition_surjective (a : Omega) :
    Function.Surjective (evenEndpointToDecomposition a) := by
  rintro ⟨p,y,hy,hz,hp⟩
  rcases leech_coordinate_parity y.val y.prop with he | ho
  · exact ⟨⟨y,hy,hz,he⟩,Subtype.ext hp.symm⟩
  · have hs : normSixVector a-(normSixVector a-y) = y := by abel
    have he (i : Omega) : (normSixVector a-y).val i % 2 = 0 := by
      change ((normSixVector a).val i-y.val i) % 2 = 0
      have hi := ho i
      rw [normSixVector_apply]
      split_ifs <;> omega
    refine ⟨⟨normSixVector a-y,hz,by rw [hs]; exact hy,he⟩,Subtype.ext ?_⟩
    change {normSixVector a-y,normSixVector a-(normSixVector a-y)} = p
    rw [hs,hp,Finset.pair_comm]

def co3EvenDecompositionEquiv (a : Omega) :
    Co3EvenEndpoint a ≃ MinimumDecompositions (normSixVector a) :=
  Equiv.ofBijective (evenEndpointToDecomposition a)
    ⟨evenEndpointToDecomposition_injective a,evenEndpointToDecomposition_surjective a⟩

def co3PointHeptadDecompositionEquiv (a : Omega) :
    Co3PointHeptad a ≃ MinimumDecompositions (normSixVector a) :=
  (co3PointHeptadEvenEquiv a).trans (co3EvenDecompositionEquiv a)

theorem co3_decompositions_card (a : Omega) :
    Nat.card (MinimumDecompositions (normSixVector a)) = 276 := by
  rw [← Nat.card_congr (co3EvenDecompositionEquiv a),co3EvenEndpoint_card]

instance minimumDecompositionAction (x : leech) :
    MulAction (fullVectorStabilizer x) (MinimumDecompositions x) where
  smul g p := ⟨p.val.image g.val.val,by
    obtain ⟨y,hy,hz,hp⟩ := p.prop
    have hg : g.val.val x = x := g.prop
    have he : x-g.val.val y = g.val.val (x-y) := by rw [map_sub,hg]
    refine ⟨g.val.val y,(g.val.prop y y).trans hy,?_,?_⟩
    · rw [he]; exact (g.val.prop _ _).trans hz
    · simp [hp,map_sub,hg]⟩
  one_smul p := by
    apply Subtype.ext
    change p.val.image (fun y => y) = p.val
    exact Finset.image_id
  mul_smul g h p := by
    apply Subtype.ext
    change p.val.image ((g.val*h.val).val) = (p.val.image h.val.val).image g.val.val
    simp only [Finset.image_image]
    rfl

end Atlas.Conway
