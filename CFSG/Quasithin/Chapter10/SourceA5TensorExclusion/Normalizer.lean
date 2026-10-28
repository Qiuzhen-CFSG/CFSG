module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Model
public import Theory.Representation.BinaryConjugationSection.NormalizerAction
public import Theory.Representation.OrthogonalFourPlusMatrix.Normalizer
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRank

/-!
# The original full normalizer in determinant coordinates

Transport conjugation on the original module by the bijective coordinates.
The normal subgroup L₀ has exactly the literal determinant-action image,
so every element of M lies in that image's binary linear normalizer. The
intrinsic matrix results give semilinearity and exclude binary transvections
without assuming a normalizer description of the ambient source group.
Source: Aschbacher–Smith 9.1.2, printed p.729.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

def maximalAction : D.maximalLocal →* (Binary.V ≃ₗ[ZMod 2] Binary.V) :=
  (BinaryConjugationSection.normalizerAction m.sectionData.coordinates
    ⟨m.coordinates_injective,m.sectionData.onto⟩).comp
      (D.maximalLocal.subtype.codRestrict _
        (fun g => D.maximalLocal_normalizes_fullModule g.property))

theorem maximalAction_coordinates (h : D.maximalLocal) (a : D.fullModule) :
    m.maximalAction h (m.sectionData.coordinates a).toAdd =
      (m.sectionData.coordinates
        (D.fullModule.normalizerMonoidHom
          ⟨h,D.maximalLocal_normalizes_fullModule h.property⟩ a)).toAdd :=
  BinaryConjugationSection.normalizerAction_coordinates _ _ _ _

theorem maximalAction_on_orbit (h : localOrbit T L) :
    m.maximalAction ⟨h,(localOrbit T L).le_normalizer h.property⟩ =
      Binary.linearAction (m.quotient h) := by
  apply LinearEquiv.toLinearMap_injective
  exact BinaryConjugationSection.normalizerAction_restrict m.sectionData
    m.coordinates_injective h

theorem maximalAction_orbit_image :
    ((localOrbit T L).subgroupOf D.maximalLocal).map m.maximalAction =
      Binary.linearAction.range := by
  apply le_antisymm
  · rintro _ ⟨h,hh,rfl⟩
    exact ⟨m.quotient ⟨h,hh⟩, (m.maximalAction_on_orbit ⟨h,hh⟩).symm⟩
  · rintro _ ⟨g,rfl⟩
    obtain ⟨h,rfl⟩ := m.onto g
    exact ⟨⟨h,(localOrbit T L).le_normalizer h.property⟩,h.property,
      m.maximalAction_on_orbit h⟩

theorem maximalAction_mem_normalizer (h : D.maximalLocal) :
    m.maximalAction h ∈ normalizer (Binary.linearAction.range :
      Set (Binary.V ≃ₗ[ZMod 2] Binary.V)) := by
  rw [← m.maximalAction_orbit_image]
  apply Subgroup.le_normalizer_map m.maximalAction
  apply Subgroup.mem_map_of_mem
  rw [Subgroup.normalizer_eq_top]
  trivial

theorem maximalAction_no_transvection (h : D.maximalLocal) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((m.maximalAction h).toLinearMap - LinearMap.id)) ≠ 1 :=
  Binary.normalizer_no_transvection _ (m.maximalAction_mem_normalizer h)

theorem maximalAction_semilinear (h : D.maximalLocal) :
    ∃ σ : Binary.F ≃+* Binary.F, ∀ (c : Binary.F) (v : Binary.V),
      m.maximalAction h (c • v) = σ c • m.maximalAction h v :=
  Binary.normalizer_semilinear _ (m.maximalAction_mem_normalizer h)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
