module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Refinement.Separation
public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Neighbors
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon

/-!
# Rigidity of the marked finite binary Ree path

Fourteen checked neighbor-color refinements separate all 4680 vertices. The
generic invariant-signature argument therefore proves that a graph automorphism
fixing the ten vertices of the displayed nine-edge path is the identity. This
is a theorem about all graph automorphisms, independently of the group action.

Source: the building-automorphism assertion in Aschbacher--Smith J.5.6, p.447.
-/

@[expose] public section
namespace ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
open SimpleGraph SimpleGraph.ColorRefinement

/-- The ten distinguished vertices form the selected nine-edge path. -/
def seed : List Vertex := [0,1755,1,1757,4,1766,19,1813,100,1867]

private theorem fixed_val_iff (a : graph ≃g graph) (v w : Vertex) (hw : a w=w) :
    (a v).val=w.val ↔ v.val=w.val := by
  constructor
  · intro he
    exact congrArg Fin.val (a.injective ((Fin.ext he).trans hw.symm))
  · intro he
    have he' : v=w := Fin.ext he
    rw [he',hw]

private theorem color0_invariant (a : graph ≃g graph)
    (h : ∀ w ∈ seed, a w=w) (v : Vertex) :
    Refinement.color0 (a v).val = Refinement.color0 v.val := by
  have h0 : (a v).val=0 ↔ v.val=0 := fixed_val_iff a v 0 (h 0 (by decide +kernel))
  have h1 : (a v).val=1755 ↔ v.val=1755 := fixed_val_iff a v 1755 (h 1755 (by decide +kernel))
  have h2 : (a v).val=1 ↔ v.val=1 := fixed_val_iff a v 1 (h 1 (by decide +kernel))
  have h3 : (a v).val=1757 ↔ v.val=1757 := fixed_val_iff a v 1757 (h 1757 (by decide +kernel))
  have h4 : (a v).val=4 ↔ v.val=4 := fixed_val_iff a v 4 (h 4 (by decide +kernel))
  have h5 : (a v).val=1766 ↔ v.val=1766 := fixed_val_iff a v 1766 (h 1766 (by decide +kernel))
  have h6 : (a v).val=19 ↔ v.val=19 := fixed_val_iff a v 19 (h 19 (by decide +kernel))
  have h7 : (a v).val=1813 ↔ v.val=1813 := fixed_val_iff a v 1813 (h 1813 (by decide +kernel))
  have h8 : (a v).val=100 ↔ v.val=100 := fixed_val_iff a v 100 (h 100 (by decide +kernel))
  have h9 : (a v).val=1867 ↔ v.val=1867 := fixed_val_iff a v 1867 (h 1867 (by decide +kernel))
  simp only [Refinement.color0,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem eq_refl_of_fix_seed (a : graph ≃g graph)
    (h : ∀ w ∈ seed, a w=w) : a = SimpleGraph.Iso.refl := by
  have h0 := color0_invariant a h
  have h1 := refinement_invariant neighborLists a
    (fun v => Refinement.color0 v.val) (fun v => Refinement.color1 v.val)
    Refinement.decode1 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step1 v.val v.isLt) h0
  have h2 := refinement_invariant neighborLists a
    (fun v => Refinement.color1 v.val) (fun v => Refinement.color2 v.val)
    Refinement.decode2 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step2 v.val v.isLt) h1
  have h3 := refinement_invariant neighborLists a
    (fun v => Refinement.color2 v.val) (fun v => Refinement.color3 v.val)
    Refinement.decode3 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step3 v.val v.isLt) h2
  have h4 := refinement_invariant neighborLists a
    (fun v => Refinement.color3 v.val) (fun v => Refinement.color4 v.val)
    Refinement.decode4 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step4 v.val v.isLt) h3
  have h5 := refinement_invariant neighborLists a
    (fun v => Refinement.color4 v.val) (fun v => Refinement.color5 v.val)
    Refinement.decode5 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step5 v.val v.isLt) h4
  have h6 := refinement_invariant neighborLists a
    (fun v => Refinement.color5 v.val) (fun v => Refinement.color6 v.val)
    Refinement.decode6 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step6 v.val v.isLt) h5
  have h7 := refinement_invariant neighborLists a
    (fun v => Refinement.color6 v.val) (fun v => Refinement.color7 v.val)
    Refinement.decode7 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step7 v.val v.isLt) h6
  have h8 := refinement_invariant neighborLists a
    (fun v => Refinement.color7 v.val) (fun v => Refinement.color8 v.val)
    Refinement.decode8 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step8 v.val v.isLt) h7
  have h9 := refinement_invariant neighborLists a
    (fun v => Refinement.color8 v.val) (fun v => Refinement.color9 v.val)
    Refinement.decode9 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step9 v.val v.isLt) h8
  have h10 := refinement_invariant neighborLists a
    (fun v => Refinement.color9 v.val) (fun v => Refinement.color10 v.val)
    Refinement.decode10 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step10 v.val v.isLt) h9
  have h11 := refinement_invariant neighborLists a
    (fun v => Refinement.color10 v.val) (fun v => Refinement.color11 v.val)
    Refinement.decode11 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step11 v.val v.isLt) h10
  have h12 := refinement_invariant neighborLists a
    (fun v => Refinement.color11 v.val) (fun v => Refinement.color12 v.val)
    Refinement.decode12 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step12 v.val v.isLt) h11
  have h13 := refinement_invariant neighborLists a
    (fun v => Refinement.color12 v.val) (fun v => Refinement.color13 v.val)
    Refinement.decode13 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step13 v.val v.isLt) h12
  have h14 := refinement_invariant neighborLists a
    (fun v => Refinement.color13 v.val) (fun v => Refinement.color14 v.val)
    Refinement.decode14 (fun v => by
      rw [← rawSignature_eq_signature]
      exact Refinement.step14 v.val v.isLt) h13
  ext v
  exact congrArg Fin.val (Refinement.finalColor_injective (h14 v))

/-- The selected path, retained in the exact finite-graph labels. -/
def seedPath : BasedWalk graph 9 0 :=
  ⟨⟨1755, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨1, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨1757, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨4, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨1766, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨19, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨1813, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨100, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, ⟨⟨1867, by change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _); decide +kernel⟩, PUnit.unit⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem seedPath_vertices : seedPath.vertices = seed := rfl

theorem seedPath_nonbacktracking : seedPath.Nonbacktracking := by
  simp only [seedPath,BasedWalk.Nonbacktracking]
  decide +kernel

end ReeF4.Octagon.Binary.Automorphisms.FiniteGraph
