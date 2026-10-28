module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.ElementaryFour
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six

/-!
# The natural S6 quotient reduction for H.15.5

Every outer elementary subgroup of order sixteen has an offender image on
the four-dimensional hexad kernel. The proved degree-six classification then
puts that image, after a witnessed conjugation, inside the three-transposition
cube or onto the exceptional order-eight subgroup. Surjectivity of the actual
hexad quotient lifts the conjugator back to the ambient hexad stabilizer.
No maximal-elementary hypothesis is used.

`HexadQuotientData` records the earlier common Sylow, natural-action and
quotient-marking facts. No witness of this structure is asserted here. In
particular, its quintet and Sylow image identities must be proved when applying
this reduction; incidence of the source objects does not supply them. The
mixed planes in the canonical Sylow list require the explicit conjugation.

This is the initial group reduction in Aschbacher--Smith H.15.5, printed
p.401, using B.3.2(5), printed p.84 (1 March 2004 manuscript).
-/

@[expose] public section

open Representation.BinaryOffender
open MathieuCode MathieuCode.M22ElementaryFour
open CFSG.Quasithin.ChapterB.Offenders

namespace CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour

theorem offender_conjugate_into_cube_or_exceptional
    (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : IsOffender (BinaryPermutation.naturalRepresentation (Fin 6)) A) :
    ∃ g : Equiv.Perm (Fin 6),
      A.map (MulAut.conj g).toMonoidHom ≤ D 6 ∨
      A.map (MulAut.conj g).toMonoidHom = exceptional 6 (by decide) := by
  have hr (B : Subgroup (Equiv.Perm (Fin 6))) (hB : B ≤ D 6)
      (hAB : IsConjugateTo A B) :
      ∃ g : Equiv.Perm (Fin 6), A.map (MulAut.conj g).toMonoidHom ≤ D 6 ∨
        A.map (MulAut.conj g).toMonoidHom = exceptional 6 (by decide) := by
    obtain ⟨g, hg⟩ := hAB.symm
    exact ⟨g, Or.inl (hg ▸ hB)⟩
  rcases (Six.caseBFamily_iff A).mp ((Six.isOffender_natural_iff A).mp hA) with
    h | h | h | h | h | h
  · exact hr _ (disjointTranspositions_le_D _ _) h
  · exact hr _ (disjointTranspositions_le_D _ _) h
  · exact hr _ le_rfl h
  · obtain ⟨g, hg⟩ := h.symm
    exact ⟨g, Or.inr hg.symm⟩
  · exact hr _ inf_le_left h
  · exact hr _ Six.plus_le_D h

/-- The exact earlier hexad quotient and its natural kernel action. -/
structure HexadQuotientData (T : Sylow 2 Ambient) where
  compatible : SourceCompatible T
  kernel_le_sylow : HexadKernel ≤ (T : Subgroup Ambient)
  kernel_le_inner : HexadKernel ≤ MathieuCode.M22ElementaryFour.Inner
  quotientMap : Hexad →* Equiv.Perm (Fin 6)
  surjective : Function.Surjective quotientMap
  kernel_eq : quotientMap.ker = HexadKernel.subgroupOf Hexad
  coordinates : quotientMap.ker ≃ BinaryPermutation.natural (Fin 6)
  coordinates_mul : ∀ a b, coordinates (a * b) = coordinates a + coordinates b
  coordinates_conj : ∀ (a : Hexad) (k : quotientMap.ker),
    coordinates ⟨a * k.val * a⁻¹, (inferInstance : quotientMap.ker.Normal).conj_mem k.val k.property a⟩ =
      BinaryPermutation.naturalRepresentation (Fin 6) (quotientMap a) (coordinates k)
  inner_preimage : (alternatingGroup (Fin 6)).comap quotientMap = MathieuCode.M22ElementaryFour.Inner.subgroupOf Hexad
  quintet_image : (QuintetKernel.subgroupOf Hexad).map quotientMap = D 6
  sylow_image : ((T : Subgroup Ambient).subgroupOf Hexad).map quotientMap = Six.sylowCarrier

theorem HexadQuotientData.commuting_coordinates {T : Sylow 2 Ambient}
    (d : HexadQuotientData T) (a : Hexad) (k : d.quotientMap.ker)
    (h : Commute a k.val) :
    BinaryPermutation.naturalRepresentation (Fin 6) (d.quotientMap a)
      (d.coordinates k) = d.coordinates k := by
  rw [← d.coordinates_conj]
  congr 1
  apply Subtype.ext
  change a * k.val * a⁻¹ = k.val
  rw [h.eq, mul_inv_cancel_right]

theorem HexadQuotientData.image_offender {T : Sylow 2 Ambient}
    (d : HexadQuotientData T) (A : Subgroup Ambient)
    (hAT : A ≤ (T : Subgroup Ambient)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner) :
    IsOffender (BinaryPermutation.naturalRepresentation (Fin 6))
      ((A.subgroupOf Hexad).map d.quotientMap) := by
  let := hA
  have hAH := hAT.trans d.compatible.le_hexad
  apply image_offender_of_kernel_coordinates d.quotientMap
    (BinaryPermutation.naturalRepresentation (Fin 6)) d.coordinates
    d.commuting_coordinates (A.subgroupOf Hexad) (IsElementaryAbelian.subgroupOf hAH)
  · have hc : Nat.card (A.subgroupOf Hexad) = 16 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hcard
    rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    norm_num [Nat.card_eq_fintype_card]
  · intro hle
    apply houter
    intro a ha
    have hk := hle (show (⟨a, hAH ha⟩ : Hexad) ∈ A.subgroupOf Hexad from ha)
    rw [d.kernel_eq] at hk
    exact d.kernel_le_inner hk

theorem HexadQuotientData.conjugate_image_cases {T : Sylow 2 Ambient}
    (d : HexadQuotientData T) (A : Subgroup Ambient)
    (hAT : A ≤ (T : Subgroup Ambient)) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (houter : ¬ A ≤ MathieuCode.M22ElementaryFour.Inner) :
    ∃ g : Hexad,
      (((A.subgroupOf Hexad).map (MulAut.conj g).toMonoidHom).map d.quotientMap ≤ D 6 ∨
      ((A.subgroupOf Hexad).map (MulAut.conj g).toMonoidHom).map d.quotientMap =
        exceptional 6 (by decide)) := by
  obtain ⟨s, hs⟩ := offender_conjugate_into_cube_or_exceptional _
    (d.image_offender A hAT hA hcard houter)
  obtain ⟨g, rfl⟩ := d.surjective s
  exact ⟨g, by rwa [map_conj_image]⟩


theorem HexadQuotientData.intersection_card_of_image_card_two {T : Sylow 2 Ambient}
    (d : HexadQuotientData T) (A : Subgroup Ambient)
    (hAT : A ≤ (T : Subgroup Ambient)) (hcard : Nat.card A = 16)
    (himage : Nat.card ((A.subgroupOf Hexad).map d.quotientMap) = 2) :
    Nat.card (A ⊓ HexadKernel : Subgroup Ambient) = 8 := by
  have hAH := hAT.trans d.compatible.le_hexad
  have hc : Nat.card (A.subgroupOf Hexad) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hcard
  have h := card_intersection_of_card_image_two d.quotientMap (A.subgroupOf Hexad) hc himage
  have he : A.subgroupOf Hexad ⊓ d.quotientMap.ker =
      (A ⊓ HexadKernel : Subgroup Ambient).subgroupOf Hexad := by
    rw [d.kernel_eq]
    rfl
  rw [he] at h
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left.trans hAH)).toEquiv).symm.trans h


end CFSG.Quasithin.ChapterH.Section13To16.M22ElementaryFour
