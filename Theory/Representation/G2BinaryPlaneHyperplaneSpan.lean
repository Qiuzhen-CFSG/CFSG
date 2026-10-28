module
public import Theory.Representation.G2BinaryPointFlag

/-!
# Hyperplane generation by the binary plane-parabolic cubic

The literal cubic sends the fourth basis vector to its sum with the fifth,
so the marked hyperplane and its image span the natural six-space. The
marked three-space has eight vectors. These are the concrete dimension
facts used in Aschbacher–Smith 13.3.18, printed p.895.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.G2.Explicit Subgroup
open BinaryParabolicPair

theorem hyperplane_plane_cubic_span :
    hyperplane⊔hyperplane.map (Restricted.NaturalCoordinates.action F cubicActor)=⊤ := by
  have h5:Pi.single (5:Fin 6) (1:F)∈hyperplane⊔hyperplane.map
      (Restricted.NaturalCoordinates.action F cubicActor) := by
    have hh:Restricted.NaturalCoordinates.action F cubicActor (Pi.single 4 1)-Pi.single 4 1=
        Pi.single 5 1 := by
      ext i;fin_cases i <;> simp [cubicActor,shortRoot,map_mul,Module.End.mul_apply]
    rw [←hh]
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_right ⟨Pi.single 4 1,by simp,rfl⟩
    · exact Submodule.mem_sup_left (by simp)
  apply top_unique
  intro w _
  have he:w=∑i:Fin 6,w i•Pi.single i (1:F) := pi_eq_sum_univ' w
  rw [he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  by_cases hi:i=5
  · exact hi ▸ h5
  · apply Submodule.mem_sup_left
    simp [Ne.symm hi]

private def seedCoordinateEquiv : seed≃(Fin 3→F) where
  toFun v := ![v.val 0,v.val 1,v.val 2]
  invFun w := ⟨![w 0,w 1,w 2,0,0,0],by simp⟩
  left_inv v := by
    apply Subtype.ext
    obtain ⟨h3,h4,h5⟩:=(mem_seed v.val).mp v.prop
    ext i;fin_cases i <;> simp [h3,h4,h5]
  right_inv w := by ext i;fin_cases i <;>rfl

theorem card_seed : Nat.card seed=8 := by
  rw [Nat.card_congr seedCoordinateEquiv]
  simp

end Atlas.G2.Natural.BinaryPointFlag
