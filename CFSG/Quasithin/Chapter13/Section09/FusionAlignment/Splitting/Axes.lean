module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion.Coordinates
public import Theory.GroupTheory.DihedralInvolutionLift
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
/-!
# The two original central axes of the dihedral base

Central elements of the marked D₈×D₈ base are exactly 1,t,z,tz. A dihedral
central involution embedded in S₄ lies in its Klein four-group: it is an
even involution because it is a square. Together these facts identify the
second factor's central involution after source Sylow placement.
Source: Aschbacher–Smith 13.9.10.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath
variable {G:Type*} [Group G] {d:Configuration G} (m:Marking d)

theorem central_dihedralBase_cases (x:G) (hx:x∈m.dihedralBase)
    (hc:∀y∈m.dihedralBase,y*x=x*y) :
    x=1 ∨ x=m.t ∨ x=m.z ∨ x=m.t*m.z := by
  rw [←m.range_baseProductEmbedding] at hx
  obtain ⟨⟨a,b⟩,rfl⟩:=hx
  have hh : ∀c:D8×D8,c*(a,b)=(a,b)*c := by
    intro c
    apply m.baseProductEmbedding_injective
    rw [map_mul,map_mul]
    exact hc _ (m.range_baseProductEmbedding ▸ (show m.baseProductEmbedding c∈m.baseProductEmbedding.range from ⟨c,rfl⟩))
  have hs : ∀a b:D8,(∀c:D8×D8,c*(a,b)=(a,b)*c) →
      (a,b)=(1,1) ∨ (a,b)=(.r 2,1) ∨ (a,b)=(.r 2,.r 2) ∨ (a,b)=(1,.r 2) := by decide +kernel
  rcases hs a b hh with h|h|h|h
  · left
    rw [h]
    exact map_one _
  · right;left
    rw [h,m.baseProductEmbedding_axis]
  · right;right;left
    change m.embedding (sylowEmbedding (pair (a,b)))=m.z
    rw [h]
    exact m.sylowModelEmbedding_center
  · right;right;right
    rw [h,←m.baseProductEmbedding_axis]
    have hz : m.z=m.baseProductEmbedding (.r 2,.r 2) := m.sylowModelEmbedding_center.symm
    rw [hz,←map_mul]
    exact congrArg m.baseProductEmbedding (by decide +kernel)

theorem dihedral_square_mem_symmetric_core (f:D8→*Equiv.Perm (Fin 4)) :
    f (.r 2)∈pCore 2 (Equiv.Perm (Fin 4)) := by
  rw [←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_mem_iff]
  have hs : (.r 1:D8)^2=.r 2 := by decide
  have hi : (.r 2:D8)^2=1 := by decide
  refine ⟨?_,?_⟩
  · rw [←hs,map_pow,map_pow]
    exact Units.val_injective (by simp)
  · rw [←map_pow,hi,map_one]

end CFSG.Quasithin.Chapter13.Section09.Marking
