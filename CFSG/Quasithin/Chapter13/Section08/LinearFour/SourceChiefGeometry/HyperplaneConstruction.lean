module
public import Theory.Representation.BinaryParabolicExteriorSquare.HyperplaneFixed
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.OrthogonalActors

/-!
# Constructing the reciprocal critical hyperplane

The original natural quotient sends an upper critical image into a conjugate
of the plane radical. Centralization of the actual natural hyperplane gives
order at most four by its two free binary coordinates. The strict inclusion
of the lower critical image, of order two, forces order four. Applying this
to the inverse of the same source conjugator gives |V_H : V_H ∩ Qγ| = 4.
Together with |U_H : U_H ∩ Qγ| = 2, subgroup index multiplication constructs
the hyperplane (V_H ∩ Qγ)U_H. The original commutator bound on V_H ∩ Qγ
extends over U_H, and the marked exterior action supplies A₁ ≤ V_H.

The final application proves all three critical-geometry conclusions from
these earlier reciprocal premises. The original quotient maps, conjugator,
relative normality, and line are retained. Construction of the initial
natural/exterior markings, reciprocal placement and fixed-axis premises, and
the chief-factor obstruction remain with qt-d-138-linear-four-source.
Earlier 13.8.27 setup belongs to qt-d-138-six-g2-source, and final 13.8.1
assembly to qt-d-1381-source. This is not a proof of full 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.32(3), printed p.965, using the symmetry of Remark F.9.17.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare
variable {G : Type*} [Group G] [Finite G]

/-- The genuine parabolic containment and fixed natural hyperplane bound the
critical upper image, through its original quotient map. -/
theorem source_critical_upper_image_bound
    (H UH V1 DH QH Vγ : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1D : V1 ≤ DH) (hDU : DH ≤ UH) (hindex : DH.relIndex UH = 2)
    (hVγH : Vγ ≤ H) (hcentral : Vγ ≤ centralizer (DH:Set G))
    (g : SL(4,ZMod 2)) (hradical : (Vγ.subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g) :
    QH.relIndex Vγ ≤ 4 := by
  let P := d.imageSpace DH
  have hd := d.imageSpace_codimension_of_index DH hDU hV1D 1 (by simpa using hindex)
  have hp : Module.finrank (ZMod 2) P = 3 := by
    simp only [Module.finrank_pi,Fintype.card_fin] at hd
    change Module.finrank (ZMod 2) P + 1 = 4 at hd
    omega
  let A := (Vγ.subgroupOf H).map π
  have hfix (a : A) (w : Fin 4 → ZMod 2) (hw : w ∈ P) :
      Matrix.mulVec a.val.val w = w := by
    obtain ⟨b,hb,he⟩ := a.property
    obtain ⟨x,hx,hxw⟩ := (d.mem_imageSpace_iff DH w).mp hw
    have heq : (⟨(b:G) * x * (b:G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized b.property) x).mp x.property⟩ : UH) = x := by
      apply Subtype.ext
      have hc : (x:G) * (b:G) = (b:G) * x := hcentral hb x hx
      change (b:G) * (x:G) * (b:G)⁻¹ = (x:G)
      rw [←hc,mul_assoc,mul_inv_cancel,mul_one]
    have hh := d.equivariant b x
    rw [heq,hxw,hnatural,he] at hh
    exact hh.symm
  have hc := PlaneRadical.card_le_four_of_fixed_hyperplane_conjugate A g hradical P hp hfix
  have he : Nat.card A = QH.relIndex Vγ := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hVγH]
  rwa [he] at hc

/-- The proper upper image containing the order-two critical image has order
four. Neither its rank nor its cardinality is assumed. -/
theorem source_critical_upper_image_four
    (H UH V1 DH QH Uγ Vγ : Subgroup G)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1D : V1 ≤ DH) (hDU : DH ≤ UH) (hindex : DH.relIndex UH = 2)
    (hUγH : Uγ ≤ H) (hVγH : Vγ ≤ H)
    (hstar : QH.relIndex Uγ = 2)
    (hstrict : (Uγ.subgroupOf H).map π < (Vγ.subgroupOf H).map π)
    (hcentral : Vγ ≤ centralizer (DH:Set G))
    (g : SL(4,ZMod 2)) (hradical : (Vγ.subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g) :
    QH.relIndex Vγ = 4 := by
  have hbound := source_critical_upper_image_bound H UH V1 DH QH Vγ
    ρ d π hker hnatural hV1D hDU hindex hVγH hcentral g hradical
  let A := (Uγ.subgroupOf H).map π
  let B := (Vγ.subgroupOf H).map π
  have hA : Nat.card A = 2 := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hUγH,hstar]
  have hB : Nat.card B = QH.relIndex Vγ := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hVγH]
  have hne : Nat.card B ≠ 2 := by
    intro he
    exact hstrict.ne (eq_of_le_of_card_ge hstrict.le (by rw [hA,he]))
  have hd := card_dvd_of_le hstrict.le
  change Nat.card A ∣ Nat.card B at hd
  rw [hA] at hd
  have hp : 0 < Nat.card B := Nat.card_pos
  rw [←hB] at hbound ⊢
  omega

/-- The reciprocal image of order four and the natural axis of index two
construct the actual hyperplane (V_H ∩ Qγ)U_H. -/
theorem source_reciprocal_hyperplane_index
    (UH VH Qγ : Subgroup G) (hUV : UH ≤ VH)
    (hn : VH ≤ normalizer (UH:Set G))
    (hupper : Qγ.relIndex VH = 4) (hlower : Qγ.relIndex UH = 2) :
    (VH ⊓ Qγ ⊔ UH).relIndex VH = 2 := by
  let E := VH ⊓ Qγ
  have hEU : E.relIndex UH = 2 := by
    rw [←inf_relIndex_right E UH]
    have hi : E ⊓ UH = Qγ ⊓ UH := by
      ext x
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨hUV h.2,h.1⟩,h.2⟩⟩
    rw [hi,inf_relIndex_right,hlower]
  have he : E.relIndex (E ⊔ UH) = 2 := by
    rw [sup_comm,relIndex_sup_of_normalizes UH E (inf_le_left.trans hn),hEU]
  have hm := relIndex_mul_relIndex E (E ⊔ UH) VH le_sup_left (sup_le inf_le_left hUV)
  have hEV : E.relIndex VH = 4 := by rw [inf_relIndex_left,hupper]
  rw [he,hEV] at hm
  change (E ⊔ UH).relIndex VH = 2
  omega


/-- Apply the radical calculation at the opposite endpoint, using the inverse
of the same source conjugator and the original natural quotient marking. -/
theorem source_hyperplane_of_reciprocal_parabolic
    (H UH V1 DR QH VH : Subgroup G) (hUV : UH ≤ VH) (hVH : VH ≤ H)
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (hV1D : V1 ≤ DR) (hDU : DR ≤ UH) (hindex : DR.relIndex UH = 2)
    (y : G) (hbackUH : UH.conjBy y⁻¹ ≤ H) (hbackVH : VH.conjBy y⁻¹ ≤ H)
    (hlower : (QH.conjBy y).relIndex UH = 2)
    (hstrict : ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π)
    (hcentral : VH.conjBy y⁻¹ ≤ centralizer (DR:Set G))
    (g : SL(4,ZMod 2))
    (hradical : ((VH.conjBy y⁻¹).subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g) :
    (QH.conjBy y).relIndex VH = 4 ∧ (VH ⊓ QH.conjBy y ⊔ UH).relIndex VH = 2 := by
  have hi (B : Subgroup G) : (QH.conjBy y).relIndex B = QH.relIndex (B.conjBy y⁻¹) := by
    have hh := relIndex_map_map_of_injective (f := (MulAut.conj y).toMonoidHom)
      QH (B.conjBy y⁻¹) (MulAut.conj y).injective
    change (QH.conjBy y).relIndex ((B.conjBy y⁻¹).conjBy y) = _ at hh
    rwa [conjBy_inv'] at hh
  have hf := source_critical_upper_image_four H UH V1 DR QH
    (UH.conjBy y⁻¹) (VH.conjBy y⁻¹) ρ d π hker hnatural hV1D hDU hindex
    hbackUH hbackVH ((hi UH).symm.trans hlower) hstrict hcentral g hradical
  have hu : (QH.conjBy y).relIndex VH = 4 := (hi VH).trans hf
  exact ⟨hu,source_reciprocal_hyperplane_index UH VH (QH.conjBy y)
    hUV (hVH.trans d.normalized) hu hlower⟩

omit [Finite G] in
/-- The critical commutator on E_H extends to E_H U_H using the original
normality of U_H, without enlarging the source line. -/
theorem source_hyperplane_commutator
    (H UH E Uγ A1 : Subgroup G)
    (hn : H ≤ normalizer (UH:Set G)) (hEH : E ≤ H) (hUγH : Uγ ≤ H)
    (hcomm : ⁅Uγ,E⁆ ≤ A1) : ⁅Uγ,E ⊔ UH⁆ ≤ A1 ⊔ UH := by
  apply commutator_le.mpr
  intro a ha x hx
  have hprod := coe_mul_of_left_le_normalizer_right E UH (hEH.trans hn)
  change x ∈ (↑(E ⊔ UH) : Set G) at hx
  rw [hprod] at hx
  obtain ⟨e,he,u,hu,rfl⟩ := hx
  have hfirst : a * e * a⁻¹ * e⁻¹ ∈ A1 := hcomm (commutator_mem_commutator ha he)
  have hsecond : e * (a * u * a⁻¹ * u⁻¹) * e⁻¹ ∈ UH := by
    apply (mem_normalizer_iff.mp (hn (hEH he)) _).mp
    exact UH.mul_mem ((mem_normalizer_iff.mp (hn (hUγH ha)) _).mp hu) (UH.inv_mem hu)
  have hh := (A1 ⊔ UH).mul_mem
    ((le_sup_left : A1 ≤ A1 ⊔ UH) hfirst) ((le_sup_right : UH ≤ A1 ⊔ UH) hsecond)
  convert hh using 1
  group

open Atlas.Order20160A8.Bivectors (exteriorMap)
/-- The reciprocal parabolic constructs the actual source hyperplane. The
orthogonal action then supplies all three conclusions of 13.8.32, retaining
the original quotient map, the critical line and the source conjugator. -/
theorem source_critical_geometry_of_reciprocal_parabolic
    (H UH V1 DR QH VH Uγ A1 : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (ρ : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (d : BinaryConjugationSection H UH V1 ρ)
    (π : H →* SL(4,ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hnatural : ∀ h w, ρ h w = Matrix.mulVec (π h).val w)
    (ξ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (dexterior : BinaryConjugationSection H VH UH ξ)
    (hexterior : ∀ h w, ξ h w = exteriorMap (π h).val w)
    (hV1D : V1 ≤ DR) (hDU : DR ≤ UH) (hindex : DR.relIndex UH = 2)
    (y : G) (hbackUH : UH.conjBy y⁻¹ ≤ H) (hbackVH : VH.conjBy y⁻¹ ≤ H)
    (hlower : (QH.conjBy y).relIndex UH = 2)
    (hstrict : ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π)
    (hcentral : VH.conjBy y⁻¹ ≤ centralizer (DR:Set G))
    (g : SL(4,ZMod 2))
    (hradical : ((VH.conjBy y⁻¹).subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g)
    (hUγH : Uγ ≤ H) (houtside : ¬ Uγ ≤ QH)
    (hcommV : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hVQ : VH ≤ QH) (hU : Nat.card Uγ = 32) (hmeet : Uγ ⊓ UH ≠ ⊥)
    (hcommE : ⁅Uγ,VH ⊓ QH.conjBy y⁆ ≤ A1)
    (hAH : A1 ≤ H) (hA : Nat.card A1 = 2) :
    QH.relIndex Uγ = 2 ∧ 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) ∧ A1 ≤ VH := by
  have hh := source_hyperplane_of_reciprocal_parabolic H UH V1 DR QH VH
    dexterior.kernel_le dexterior.section_le ρ d π hker hnatural hV1D hDU hindex
    y hbackUH hbackVH hlower hstrict hcentral g hradical
  have hc := source_hyperplane_commutator H UH (VH ⊓ QH.conjBy y) Uγ A1
    d.normalized (inf_le_left.trans dexterior.section_le) hUγH hcommE
  exact source_critical_geometry_of_exterior_action H VH UH QH Uγ
    (VH ⊓ QH.conjBy y ⊔ UH) A1 ξ π hker hexterior dexterior hUγH houtside
    hcommV hVQ hU hmeet le_sup_right (sup_le inf_le_left dexterior.kernel_le)
    hh.2 hc hAH hA

end CFSG.Quasithin.Chapter13.Section08.LinearFour
