module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleCoreIntersection

/-!
# The original field subgroup fuses an outside-core involution

Translation by the quadratic basis element changes the field involution
by the fixed translation by one. The resulting involution centralizes the
original field involution and belongs to the original point subgroup.
Its precise full-core intersection is the field involution line, which
excludes the new element from the entire ambient involution core.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer

private def translation : Model := root (Multiplicative.ofAdd (⟨0,1⟩ : K))
private def fixedTranslation : Model := root (Multiplicative.ofAdd (1 : K))

private theorem translation_conjugates :
    translation * fieldElement * translation⁻¹ = fieldElement * fixedTranslation := by
  apply SemidirectProduct.ext
  · decide +kernel
  · decide +kernel

private theorem fixed_commutes : Commute fieldElement fixedTranslation := by
  apply mul_inv_eq_iff_eq_mul.mp
  change fieldElement * root (Multiplicative.ofAdd (1 : K)) * fieldElement⁻¹ = _
  rw [fieldElement_conjugation]
  rfl

private theorem changed_ne : fieldElement * fixedTranslation ≠ fieldElement := by
  intro h
  have hh := congrArg SemidirectProduct.left h
  exact (by decide +kernel : (fieldElement * fixedTranslation).left ≠ fieldElement.left) hh

/-- The actual point subgroup contains a conjugator from the field involution
to an involution outside its full ambient two-core. -/
theorem literal_field_outside_returning
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j) :
    ∃ v ∈ Janko23.involutionCentralizer (j fieldElement), orderOf v = 2 ∧
      v ∉ Janko23.ambientCore (j fieldElement) ∧
      ∃ r ∈ j.range, r * j fieldElement * r⁻¹ = v := by
  let f := j fieldElement
  let v := j (fieldElement * fixedTranslation)
  have hf : orderOf f = 2 := BaumeisterParabolics.image_involution_order j hj.1
  have hvconj : j translation * f * (j translation)⁻¹ = v := by
    rw [←map_inv,←map_mul,←map_mul,translation_conjugates]
  have hvorder : orderOf v = 2 := by
    rw [←hvconj]
    exact ((MulAut.conj (j translation)).orderOf_eq f).trans hf
  have hvH : v ∈ Janko23.involutionCentralizer f := by
    apply mem_centralizer_singleton_iff.mpr
    exact ((Commute.refl fieldElement).mul_left fixed_commutes.symm).map j |>.eq
  have hvne : v ≠ f := fun hh => changed_ne (hj.1 hh)
  have hvout : v ∉ Janko23.ambientCore f := by
    intro hvQ
    have hi := literal_triangle_point_core_intersection P hc A C a j hj
    have hvline : v ∈ zpowers f := hi ▸ (show v ∈
        (j.range ⊓ Janko23.involutionCentralizer f) ⊓ Janko23.ambientCore f from
      ⟨⟨⟨_,rfl⟩,hvH⟩,hvQ⟩)
    have he := IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨v,hvline⟩ : zpowers f)) (y := (⟨f,mem_zpowers f⟩ : zpowers f))
      ((orderOf_coe _).symm.trans hvorder) ((orderOf_coe _).symm.trans hf)
    exact hvne (congrArg Subtype.val he)
  exact ⟨v,hvH,hvorder,hvout,j translation,⟨_,rfl⟩,hvconj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
