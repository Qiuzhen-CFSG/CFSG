module
public import Theory.Representation.BinaryConjugationSection
/-!
# Transport through an equivariant subgroup quotient

An equivariant isomorphism Q/C ≃ Z carries a faithful conjugation section
on Z to the literal section Q/C. The coordinate homomorphism is the
composition with the original quotient map; its kernel and conjugation
formula are preserved.

Used to transfer the natural center to the centralizer quotient in
DGS85, Groups and Graphs, printed p.188(5).
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
/-- Transport the actual conjugation action through an equivariant quotient identification. -/
def of_equivariant_quotient (A Q C Z : Subgroup G) [(C.subgroupOf Q).Normal]
    {ρ : Representation (ZMod 2) A W}
    (d : BinaryConjugationSection A Z ⊥ ρ)
    (hQA : Q ≤ A) (hCQ : C ≤ Q) (hAQ : A ≤ normalizer (Q : Set G))
    (E : (Q ⧸ C.subgroupOf Q) ≃* Z)
    (hE : ∀ a : A, ∀ q : Q,
      (E (QuotientGroup.mk ⟨(a : G)*q*(a : G)⁻¹,
        (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩) : G) =
      (a : G) * E (QuotientGroup.mk q) * (a : G)⁻¹) :
    BinaryConjugationSection A Q C ρ where
  section_le := hQA
  kernel_le := hCQ
  normalized := hAQ
  coordinates := d.coordinates.comp (E.toMonoidHom.comp (QuotientGroup.mk' (C.subgroupOf Q)))
  onto := d.onto.comp (E.surjective.comp (QuotientGroup.mk'_surjective _))
  kernel_eq := by
    ext q
    change d.coordinates (E (QuotientGroup.mk q)) = 1 ↔ _
    rw [d.coordinates_eq_one_iff,mem_bot]
    change (E (QuotientGroup.mk q) : G) = ((1 : Z) : G) ↔ _
    rw [Subtype.coe_inj]
    rw [E.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff q
  equivariant a q := by
    change (d.coordinates (E (QuotientGroup.mk _))).toAdd = _
    have hh : E (QuotientGroup.mk ⟨(a : G)*q*(a : G)⁻¹,
        (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩) =
      ⟨(a : G) * E (QuotientGroup.mk q) * (a : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized a.property) _).mp
          (E (QuotientGroup.mk q)).property⟩ := Subtype.ext (hE a q)
    rw [hh]
    exact d.equivariant a (E (QuotientGroup.mk q))
end Representation.BinaryConjugationSection
