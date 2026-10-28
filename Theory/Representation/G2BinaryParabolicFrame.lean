module
public import Theory.Representation.G2BinaryPointIrreducible
public import Theory.Representation.G2BinaryPointCrossPlanes
import all Theory.Representation.G2BinaryPointCrossPlanes

/-!
# The literal binary point and plane parabolic frame

The long point parabolic fixes the marked natural line pointwise over F₂.
The plane cubic preserves the first two coordinates. These facts let the source lift the point parabolic through
L₁T and the odd cubic through the actual plane residual separately.

The private import is an intentional internal split: this leaf publishes
coordinate specifications for the unchanged non-exposed `plane` definition
in its owning CrossPlanes module. No private helper enters a public type.
Source: Aschbacher–Smith 13.3.18, printed pp.894–895.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates Atlas.SplitOctonion

theorem pointParabolic_fixes_pointLine (g:Model F) (hg:g∈parabolic)
    (v:W) (hv:v∈pointLine) : Restricted.NaturalCoordinates.action F g v=v := by
  have hp:g∈pointStabilizer:=parabolic_le_pointStabilizer hg
  obtain ⟨a,ha⟩:= (mem_pointStabilizer_iff g).mp hp
  have ha1:a=1:=by
    apply Units.ext
    exact ((by decide +kernel:∀x:F,x=0∨x=1) a.val).resolve_left a.ne_zero
  rw [ha1,one_smul] at ha
  have hrep:(representative F (Pi.single 0 1)).val=(basisVector 0:Carrier F) := by
    ext i;fin_cases i <;>simp [representative,basisVector]
  have he:Restricted.NaturalCoordinates.action F g (Pi.single 0 1)=Pi.single 0 1 := by
    rw [action_apply]
    change ![g.val ((representative F (Pi.single 0 1)).val) 0,
      g.val ((representative F (Pi.single 0 1)).val) 1,
      g.val ((representative F (Pi.single 0 1)).val) 2,
      g.val ((representative F (Pi.single 0 1)).val) 5,
      g.val ((representative F (Pi.single 0 1)).val) 6,
      g.val ((representative F (Pi.single 0 1)).val) 7]=_
    rw [hrep,ha]
    ext i;fin_cases i <;>simp [basisVector]
  have hv':v=v 0•Pi.single 0 1 := by
    ext i
    by_cases hi:i=0
    · subst i;simp
    · simp [Ne.symm hi,(mem_pointLine v).mp hv i hi]
  rw [hv',map_smul,he]

theorem mem_plane (v:W) : v∈plane ↔ v 2=0 ∧ v 3=0 ∧ v 4=0 ∧ v 5=0 := by
  constructor
  · intro hv
    have hc:plane≤LinearMap.ker (LinearMap.pi
        ![LinearMap.proj (2:Fin 6),LinearMap.proj 3,LinearMap.proj 4,LinearMap.proj 5]) := by
      apply Submodule.span_le.mpr
      rintro w (rfl|hw)
      · ext i;fin_cases i <;>simp
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        ext i;fin_cases i <;>simp
    have hh:=hc hv
    exact ⟨congrFun hh 0,congrFun hh 1,congrFun hh 2,congrFun hh 3⟩
  · rintro ⟨h2,h3,h4,h5⟩
    have he:v=v 0•Pi.single 0 1+v 1•Pi.single 1 1 := by
      ext i;fin_cases i <;>simp [h2,h3,h4,h5]
    rw [he]
    exact plane.add_mem (plane.smul_mem _ (Submodule.subset_span (by simp)))
      (plane.smul_mem _ (Submodule.subset_span (by simp)))

theorem plane_cubic_preserves (v:W) (hv:v∈plane) :
    Restricted.NaturalCoordinates.action F BinaryParabolicPair.cubicActor v∈plane := by
  obtain ⟨h2,h3,h4,h5⟩:=(mem_plane v).mp hv
  rw [mem_plane]
  simp [BinaryParabolicPair.cubicActor,BinaryParabolicPair.shortRoot,map_mul,Module.End.mul_apply,h2,h3,h4,h5]

end Atlas.G2.Natural.BinaryPointFlag
