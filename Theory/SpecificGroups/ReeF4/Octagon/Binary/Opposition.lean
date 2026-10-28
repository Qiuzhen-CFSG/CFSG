module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.NeighborCounts
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.Opposition

/-!
# Opposition reconstructs adjacency on the actual binary Ree point cosets

The points are the literal cosets of the Suzuki first parabolic. Their embedding
into the native incidence graph identifies them with its zero-color fiber.
The actual order(2,4) geometry supplies every hypothesis of the generic count,
so any permutation preserving distance eight also preserves distance two.

This is the opposition-to-point-adjacency step needed in Aschbacher–Smith
J.5.6–7, with no assumed recurrence, point count or abstract building marking.
The assertion that every building automorphism is induced by the group is a
separate theorem and is not claimed here.
-/

public noncomputable section
namespace ReeF4.Octagon.Binary
open Subgroup Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
open SimpleGraph.OctagonShortPaths

local instance : Fintype (CosetGeometry.Vertex family) := Fintype.ofFinite _

abbrev PointCoset := Model 0 ⧸ Tits.ExceptionalParabolics.FullRee.first

@[expose] def pointVertex (q : PointCoset) : CosetGeometry.Vertex family := ⟨false,q⟩

@[expose] def cosetPointEquiv : PointCoset ≃ orderTwoFour.Point where
  toFun q := ⟨pointVertex q,by rfl⟩
  invFun v := by
    rcases v with ⟨⟨b,q⟩,hv⟩
    cases b
    · exact q
    · have hc : (1:ZMod 2)=0 := hv
      exact (one_ne_zero hc).elim
  left_inv q := rfl
  right_inv v := by
    apply Subtype.ext
    rcases v with ⟨⟨b,q⟩,hv⟩
    cases b
    · rfl
    · have hc : (1:ZMod 2)=0 := hv
      exact one_ne_zero hc |>.elim

@[simp] theorem cosetPointEquiv_val (q : PointCoset) :
    (cosetPointEquiv q).val=pointVertex q := rfl

@[expose] def pointDistance (u v : PointCoset) : ℕ := (graph family).dist (pointVertex u) (pointVertex v)

theorem opposition_determines_adjacency (e : PointCoset ≃ PointCoset)
    (hop : ∀ u v,pointDistance (e u) (e v)=8 ↔ pointDistance u v=8)
    (u v : PointCoset) : pointDistance (e u) (e v)=2 ↔ pointDistance u v=2 := by
  let e' := cosetPointEquiv.symm.trans (e.trans cosetPointEquiv)
  have hh : ∀ a b : orderTwoFour.Point,
      (graph family).dist (e' a).val (e' b).val=8 ↔ (graph family).dist a.val b.val=8 := by
    intro a b
    obtain ⟨u,rfl⟩ := cosetPointEquiv.surjective a
    obtain ⟨v,rfl⟩ := cosetPointEquiv.surjective b
    simpa only [e',Equiv.trans_apply,Equiv.symm_apply_apply,cosetPointEquiv_val,pointDistance] using hop u v
  simpa only [e',Equiv.trans_apply,Equiv.symm_apply_apply,cosetPointEquiv_val,pointDistance] using
    orderTwoFour.adjacency_preserved e' hh (cosetPointEquiv u) (cosetPointEquiv v)

end ReeF4.Octagon.Binary
