module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActor
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
/-!
# Two-core actors fix the marked Borel quotient

If g lies in the two-core of the marked maximal subgroup M, its
commutator with M intersection K lies in that intersection's two-core.
The actual component quotient map sends this core into the core of the
marked Borel. Thus g acts trivially on the whole Borel modulo its
2-core. This supplies the source 14.2.12 torus-fixation input directly.

Source: Aschbacher--Smith 14.2.12, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] [Finite D] in
theorem markedParabolicActor_core_displacement (M K : Subgroup H) [K.Normal]
    (e : sourceImage M K ≃* D) {B : Subgroup D}
    (he : (componentOverlap M K).map e.toMonoidHom = B)
    (g : H) (hg : g ∈ M.pCoreIn 2) (b : D) (hb : b ∈ B) :
    markedParabolicActor M K e g b * b⁻¹ ∈ B.pCoreIn 2 := by
  let f := markedParabolicMap M K e
  let A := M.subgroupOf K
  have hA : A.map K.subtype = M ⊓ K := by
    change (M.comap K.subtype).map K.subtype = M ⊓ K
    rw [map_comap_eq,range_subtype,inf_comm]
  have hB : A.map f = B := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (markedParabolicMap_mem_borel M K e he y).mpr hy
    · intro hx
      obtain ⟨y,rfl⟩ := markedParabolicMap_surjective M K e x
      exact mem_map.mpr ⟨y,(markedParabolicMap_mem_borel M K e he y).mp hx,rfl⟩
  obtain ⟨x,rfl⟩ := markedParabolicMap_surjective M K e b
  have hxM : (x : H) ∈ M := (markedParabolicMap_mem_borel M K e he x).mp hb
  have hxK : g * (x : H) * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ x.property g
  let y : K := ⟨g * (x : H) * g⁻¹ * (x : H)⁻¹,K.mul_mem hxK (K.inv_mem x.property)⟩
  have hyQ : (y : H) ∈ M.pCoreIn 2 := by
    have hxN : (x : H) ∈ normalizer (M.pCoreIn 2 : Set H) :=
      (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))) hxM
    have hcomm : g * (x : H) * g⁻¹ * (x : H)⁻¹ ∈ M.pCoreIn 2 := by
      have hz : g * (x : H) * g⁻¹ * (x : H)⁻¹ =
          g * ((x : H) * g⁻¹ * (x : H)⁻¹) := by group
      rw [hz]
      exact (M.pCoreIn 2).mul_mem hg ((mem_normalizer_iff.mp hxN g⁻¹).mp
        ((M.pCoreIn 2).inv_mem hg))
    exact hcomm
  have hycore : (y : H) ∈ (M ⊓ K).pCoreIn 2 :=
    inf_pCoreIn_le_of_le 2 (show M ⊓ K ≤ M from inf_le_left)
      ⟨⟨pCoreIn_le 2 M hyQ,y.property⟩,hyQ⟩
  have hpc : (A.pCoreIn 2).map K.subtype = (M ⊓ K).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ K.subtype_injective,hA]
  have hy : y ∈ A.pCoreIn 2 := by
    rw [← hpc] at hycore
    exact (mem_map_iff_mem K.subtype_injective).mp hycore
  have hh := Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le f A
    (mem_map_of_mem f hy)
  rw [hB] at hh
  convert hh using 1
  change markedParabolicActor M K e g (f x) * (f x)⁻¹ = f y
  rw [markedParabolicActor_apply]
  change f ⟨g * (x : H) * g⁻¹,hxK⟩ * (f x)⁻¹ =
    f (⟨g * (x : H) * g⁻¹,hxK⟩ * x⁻¹)
  rw [map_mul,map_inv]
end CFSG.Quasithin.Chapter14.Section02
