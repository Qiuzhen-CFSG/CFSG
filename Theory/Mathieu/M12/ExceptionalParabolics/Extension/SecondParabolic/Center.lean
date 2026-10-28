module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Overlap
public import Theory.GroupTheory.PGroup.Omega

/-!
# The center and central first omega of the whole overlap

Four quaternion-generator commutation tests on the 128 normal forms force
an element into the distinguished two-group. Every overlap element already
centralizes its generator z. Hence both the actual center and its first
omega, with their ambient embeddings, equal the specified subgroup ⟨z⟩.
Source: Aschbacher--Smith, 14.2.21, printed p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open QuaternionSwapModel MarkedSylow
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def centerTest (i : Fin 4) : Coordinates :=
  ![((QuaternionGroup.a 1,0,false),false), ((QuaternionGroup.xa 0,0,false),false),
    ((QuaternionGroup.a 0,1,false),false), ((QuaternionGroup.a 0,2,false),false)] i

theorem center_census : ∀ n : Coordinates, (∀ i : Fin 4, Commutes n (centerTest i)) →
    n.2 = false ∧ (raw n.1 = 1 ∨ raw n.1 = killed ∨
      raw n.1 = leftRaw (QuaternionGroup.a 2) ∨ raw n.1 = leftRaw (QuaternionGroup.a 2) * killed) := by
  decide +kernel

theorem center_mem (m : InnerModel) (g : overlap) (hg : g ∈ Subgroup.center overlap) :
    (g : Carrier) = 1 ∨ (g : Carrier) = z := by
  let d := geometry m
  obtain ⟨n,he⟩ := (d.evaluate_cover g).mp g.property
  have ht (i : Fin 4) : Commutes n (centerTest i) := by
    apply (d.evaluate_commute n (centerTest i)).mp
    have hm : d.evaluate (centerTest i) ∈ overlap :=
      (d.evaluate_cover _).mpr ⟨centerTest i,rfl⟩
    rw [he]
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hg) ⟨_,hm⟩)).symm
  obtain ⟨hb,hw⟩ := center_census n ht
  have hp : movement (projection (raw n.1)) = 1 ∨ movement (projection (raw n.1)) = z := by
    rcases hw with h | h | h | h <;> rw [h] <;>
      change rawValue _ = 1 ∨ rawValue _ = z <;> decide +kernel
  rw [← he]
  simpa only [Geometry.evaluate, Geometry.word, hb, Bool.false_eq_true, ↓reduceIte, mul_one] using hp

theorem z_mem_overlap : z ∈ overlap := movement_z ▸ movement_mem_overlap QuaternionSwapModel.z

def centralZ : Subgroup.center overlap :=
  ⟨⟨z,z_mem_overlap⟩, Subgroup.mem_center_iff.mpr (by
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.property.1)⟩

theorem center_image (m : InnerModel) :
    (Subgroup.center overlap).map overlap.subtype = distinguished := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    change (g : Carrier) ∈ distinguished
    rcases center_mem m g hg with h | h
    · rw [h]; exact distinguished.one_mem
    · rw [h]; exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr ⟨centralZ.val,centralZ.property,rfl⟩

theorem omega_center_image (m : InnerModel) :
    (omega₁ (Subgroup.center overlap) (p := 2)).map
      (overlap.subtype.comp (Subgroup.center overlap).subtype) = distinguished := by
  apply le_antisymm
  · rw [← center_image m]
    rintro _ ⟨g,hg,rfl⟩
    exact ⟨g.val,g.property,rfl⟩
  · apply Subgroup.zpowers_le.mpr
    refine ⟨centralZ, Subgroup.subset_closure ?_, rfl⟩
    change centralZ ^ (2^1) = 1
    apply Subtype.ext
    apply Subtype.ext
    change z ^ (2^1) = 1
    decide +kernel

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
