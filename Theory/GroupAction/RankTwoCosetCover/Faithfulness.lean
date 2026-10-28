module

public import Theory.GroupAction.RankTwoCosetCover.PathTransport

/-!
# Faithfulness through a common coset covering

A root stabilizer fixes every based walk precisely when it fixes every
vertex of the connected graph. The existing equivariant path bijections
therefore transfer faithful vertex action between completions covered by
the same coset geometry. No injectivity of either covering on all vertices
is required.

This is the kernel consequence of the actual common-cover argument in
Aschbacher--Smith F.3.4, used for the U₄(2) completion in F.4.24.
-/

@[expose] public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable {F : Bool → Subgroup A} {E : Bool → Subgroup B} {D : Bool → Subgroup C}

/-- Connectedness makes the action on all based walks detect every vertex. -/
theorem fixes_vertices_of_fixes_paths (hconn : (graph F).Connected) {v : Vertex F}
    (a : stabilizer F v) (ha : ∀ n (p : BasedWalk (graph F) n v), a • p = p) :
    ∀ w : Vertex F, (a : A) • w = w := by
  intro w
  obtain ⟨p⟩ := hconn v w
  have hp : (a : A) ∈ pathStabilizer F (ofWalk p) :=
    (mem_pathStabilizer_iff F (ofWalk p) a).mpr (ha _ (ofWalk p))
  apply hp w
  rw [vertices_ofWalk]
  exact p.end_mem_support

namespace CoverData
variable {f : A →* B} {g : A →* C} (c : CoverData F E f) (d : CoverData F D g)

include c d

/-- A connected faithful target gives faithful action in the other completion. -/
theorem injective_action_transfer (v : Vertex F) (hconn : (graph D).Connected)
    (hd : Function.Injective (MulAction.toPermHom C (Vertex D))) :
    Function.Injective (MulAction.toPermHom B (Vertex E)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro b hb
  change b = 1
  have hfix : ∀ w : Vertex E, b • w = w := fun w =>
    Equiv.Perm.ext_iff.mp hb w
  let a : stabilizer E (c.vertex v) := ⟨b, hfix _⟩
  have ha (n : ℕ) (p : BasedWalk (graph E) n (c.vertex v)) : a • p = p :=
    (mem_pathStabilizer_iff E p a).mp (fun w _ => hfix w)
  have ht (n : ℕ) (p : BasedWalk (graph D) n (d.vertex v)) :
      c.transportStabilizer d v a • p = p := by
    obtain ⟨q, rfl⟩ := (c.transportPathEquiv d n v).surjective p
    rw [← transportPathEquiv_smul, ha]
  have he : ((c.transportStabilizer d v a : stabilizer D (d.vertex v)) : C) = 1 := by
    apply hd
    apply Equiv.Perm.ext
    intro w
    simpa using fixes_vertices_of_fixes_paths hconn _ ht w
  have hea : c.transportStabilizer d v a = 1 := Subtype.ext he
  have : a = 1 := (c.transportStabilizer d v).injective (by simpa using hea)
  exact congrArg Subtype.val this

end CoverData
end Subgroup.CosetGeometry.RankTwo
