module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Core
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.HexadOuterComplement

/-!
# An elementary preimage preserved by the original hexad actor

The exact native A6 section fixes the chosen point outside its hexad.
The compatible outer involution fixes that same point. Their original
cubic projections therefore generate a point-fixing subgroup. The point
preimage construction gives an actual elementary order-128 subgroup of Q
normalized by this same actor, containing the original central marker.

This removes existence, order, elementary structure, and invariance from
the preimage premise in the Todd splitting reduction. The intersection
with the original cocode subgroup remains to be proved.
Source: Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280. The original marked Mathieu application is in
MathieuJ4RecognitionApplication.InvariantPoint.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup LocalGeometry Sporadic.Mathieu M22ValueBound.Concrete
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e))

/-- The original perfect section and compatible outer involution fix the same
point through the original automorphism quotient. -/
theorem hexad_actor_fixes_point
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (him : A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB)
    (v : fullCubicNormalizer e X) (t : m22DesignAut)
    (htp : t • Classical.choose (exists_m22Hexad_complementary_point hB) =
      Classical.choose (exists_m22Hexad_complementary_point hB))
    (hvt : CubicLift.projection e v.val=m22DesignAutToAut t) :
    ∀ j ∈ A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val,
      (designAutEquiv.symm (CubicLift.projection e j)) •
          Classical.choose (exists_m22Hexad_complementary_point hB) =
        Classical.choose (exists_m22Hexad_complementary_point hB) := by
  let p := Classical.choose (exists_m22Hexad_complementary_point hB)
  let f := designAutEquiv.symm.toMonoidHom.comp (CubicLift.projection e)
  have hle : A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val ≤
      (MulAction.stabilizer m22DesignAut p).comap f := by
    apply sup_le
    · rintro j ⟨a,ha,rfl⟩
      change designAutEquiv.symm (CubicLift.projection e a.val) • p=p
      have he : designAutEquiv.symm (CubicLift.projection e a.val) =
          inclusion (fullCubicSimpleProjection h e X a) := by
        apply designAutEquiv.injective
        rw [MulEquiv.apply_symm_apply,designAutEquiv_inclusion]
        exact (fullCubicSimpleProjection_conj h e X a).symm
      rw [he]
      exact ((hexadSectionImage_mem_iff hB _).mp (him.le (mem_map_of_mem _ ha))).2
    · apply zpowers_le.mpr
      change designAutEquiv.symm (CubicLift.projection e v.val) • p=p
      rw [hvt]
      change designAutEquiv.symm (designAutEquiv t) • p=p
      rw [MulEquiv.symm_apply_apply]
      exact htp
  exact fun j hj => hle hj

/-- The same marked order-2160 actor preserves an actual elementary preimage
of order 128 in the original core. No invariant-subgroup premise is added. -/
theorem hexad_actor_invariant_preimage
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (A : Subgroup (fullCubicCentralizer e X))
    (him : A.map (fullCubicSimpleProjection h e X)=hexadSectionImage hB)
    (v : fullCubicNormalizer e X) (t : m22DesignAut)
    (htp : t • Classical.choose (exists_m22Hexad_complementary_point hB) =
      Classical.choose (exists_m22Hexad_complementary_point hB))
    (hvt : CubicLift.projection e v.val=m22DesignAutToAut t) :
    ∃ P : Subgroup (centralizer z), P ≤ core z ∧ IsElementaryAbelian 2 P ∧
      Nat.card P=128 ∧ center (centralizer z) ≤ P ∧
      A.map (fullCubicCentralizer e X).subtype ⊔ zpowers v.val ≤
        normalizer (P : Set (centralizer z)) := by
  let := h.extraspecial
  exact exists_original_pointCore h e X _ _
    (hexad_actor_fixes_point h e X hB A him v t htp hvt)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
