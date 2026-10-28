module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLineNatural
public import Theory.Representation.OrthogonalFourPlusMatrix.FirstCohomology
public import Theory.GroupTheory.Commutator.FixedPointFree

/-!
# The original component moves its tensor plane fully

A fixed-point-free cubic in the first SL₂(4) factor lifts through the
original component quotient. Restricting the literal tensor coordinates
to its normalized singular plane keeps that action fixed-point-free.
Surjectivity of its commutator map gives [V₂,L]=V₂.

Source: Aschbacher–Smith9.3.5–9.3.7, printed pp.733–734. This is the
fully moved seed used for the original overgroup omega-orbit action.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem tensorPlane_component_commutator : ⁅m.tensorPlane,L⁆ = m.tensorPlane := by
  obtain ⟨a,ha⟩ := Binary.exists_left_fixedPointFree
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L)
    (e.symm (m.firstMarking.symm a))
  let t : localOrbit T L := ⟨l,le_componentOrbit L T l.property⟩
  have ht : m.quotient t = (a,1) := by
    rw [m.first_factor l,hl]
    simp
  apply commutator_eq_of_fixedPointFree m.tensorPlane L m.tensorPlane_normalized l l.property
  intro v hv hc
  let v0 : D.fullModule := ⟨v,m.tensorPlane_le_fullModule hv⟩
  have he := m.sectionData.equivariant t v0
  have hs : (⟨(t : G)*v0*(t : G)⁻¹,
    (mem_normalizer_iff.mp (m.sectionData.normalized t.property) v0).mp v0.property⟩ :
      D.fullModule) = v0 := by
    apply Subtype.ext
    change (l : G)*v*(l : G)⁻¹ = v
    rw [hc.eq,mul_inv_cancel_right]
  rw [hs] at he
  have hz : (m.sectionData.coordinates v0).toAdd = 0 := ha _ (by
    change _ = Binary.action (m.quotient t) (m.sectionData.coordinates v0).toAdd at he
    rw [ht] at he
    exact he.symm)
  have hone : m.sectionData.coordinates v0 = 1 := Multiplicative.toAdd.injective hz
  exact (m.sectionData.coordinates_eq_one_iff v0).mp hone

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
