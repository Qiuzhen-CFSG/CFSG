module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.CommutatorSpaces

/-!
# Lifting linear commutators through the actual source section

The specified quotient map sends group commutators to linear displacements.
Their spans therefore lie in the image of the ambient commutator subgroup.
The reverse containment must restore the kernel V₁. This gives the exact
comparison used by 13.8.9(2), rather than identifying quotient commutators
with ambient subgroups. A nonzero commutator also excludes I ≤ D_H after
the source intersection-centralizer argument. Star images commute with the
actual H-conjugator, including the source's inverse convention.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.9 and 13.8.25, printed pp.949–950 and 962.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

open Subgroup
open scoped commutatorElement
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

namespace ConjugationSection
variable (s : ConjugationSection H UH Z ρ)

/-- The zero subgroup has zero image in the actual central section. -/
theorem image_bot : s.image ⊥ = ⊥ := by
  apply le_bot_iff.mp
  rintro u ⟨x, hx, he⟩
  have hx1 : x = 1 := Subtype.ext hx
  rw [hx1, map_one] at he
  exact he.symm

/-- Linear commutators in a subrepresentation are actual images of group
commutators. No quotient denominator is added in this direction. -/
theorem commSpace_le_image (I A : Subgroup G) (N : Subrepresentation ρ)
    (hN : s.image I = N.toSubmodule) :
    (MarkedGeometry.commSpace N.toRepresentation (Source.starImage H A)).map
      N.toSubmodule.subtype ≤ s.image ⁅A, I⁆ := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, u⟩, rfl⟩
  obtain ⟨b, hb, he⟩ := a.property
  obtain ⟨x, hx, hxu⟩ := (s.mem_image I u).mp (hN.symm ▸ u.property)
  change ρ a (u : U) - u ∈ s.image ⁅A, I⁆
  rw [← he, ← hxu, s.displacement]
  exact ⟨⟨⁅(b : G), (x : G)⁆, s.commutator_mem b x⟩,
    Subgroup.commutator_mem_commutator hb hx, rfl⟩

/-- To lift back, the comparison subgroup must contain the entire kernel. -/
theorem commutator_le_of_commSpace_le (I A X : Subgroup G)
    (hIU : I ≤ UH) (hAH : A ≤ H) (hZX : Z ≤ X)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hcomm : (MarkedGeometry.commSpace N.toRepresentation (Source.starImage H A)).map
      N.toSubmodule.subtype ≤ s.image X) : ⁅A, I⁆ ≤ X := by
  apply commutator_le.mpr
  intro a ha u hu
  let aH : H := ⟨a, hAH ha⟩
  let uH : UH := ⟨u, hIU hu⟩
  have hqu : (s.quotient uH).toAdd ∈ N.toSubmodule := by
    rw [← hN]
    exact ⟨uH, hu, rfl⟩
  let uN : N.toSubmodule := ⟨(s.quotient uH).toAdd, hqu⟩
  let aS : Source.starImage H A :=
    ⟨QuotientGroup.mk' (pCore 2 H) aH, mem_map_of_mem _ ha⟩
  have hδ := Coinvariants.sub_mem_ker
    (ρ := N.toRepresentation.comp (Source.starImage H A).subtype) aS uN
  have hm := hcomm (Submodule.mem_map_of_mem hδ)
  change ρ (QuotientGroup.mk' (pCore 2 H) aH) (s.quotient uH).toAdd -
    (s.quotient uH).toAdd ∈ s.image X at hm
  rw [s.displacement] at hm
  exact (s.quotient_mem_image_iff X hZX _).mp hm

/-- Equality of the two linear commutators gives precisely the lifted bound
used in 13.8.9(2), with V₁ explicitly restored. -/
theorem lift_commSpace_comparison (I A B : Subgroup G)
    (hIU : I ≤ UH) (hBH : B ≤ H)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hcomm : MarkedGeometry.commSpace N.toRepresentation (Source.starImage H B) ≤
      MarkedGeometry.commSpace N.toRepresentation (Source.starImage H A)) :
    ⁅I, B⁆ ≤ ⁅I, A⁆ ⊔ Z := by
  rw [commutator_comm I B, commutator_comm I A]
  apply s.commutator_le_of_commSpace_le I B _ hIU hBH le_sup_right N hN
  exact ((Submodule.map_mono hcomm).trans (s.commSpace_le_image I A N hN)).trans
    (s.image_mono le_sup_left)

/-- A nonzero commutator on I rules out I≤D_H, using the centralization
already proved from the actual source intersection. -/
theorem not_le_DH_of_commSpace_rank (I Ug A : Subgroup G)
    (N : Subrepresentation ρ) (hN : s.image I = N.toSubmodule)
    (hcentral : ⁅I ⊓ Source.DH UH Ug A, Ug⁆ = ⊥)
    (hdim : 0 < Module.finrank (ZMod 2)
      (MarkedGeometry.commSpace N.toRepresentation (Source.starImage H Ug))) :
    ¬ I ≤ Source.DH UH Ug A := by
  intro hle
  have hc : ⁅Ug, I⁆ = ⊥ := by
    rw [commutator_comm, ← inf_eq_left.mpr hle]
    exact hcentral
  have hm := s.commSpace_le_image I Ug N hN
  rw [hc, s.image_bot] at hm
  have hzero : MarkedGeometry.commSpace N.toRepresentation (Source.starImage H Ug) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hz := hm (Submodule.mem_map_of_mem hv)
    exact Subtype.ext hz
  rw [hzero, finrank_bot] at hdim
  omega

end ConjugationSection


namespace MarkedGeometry

/-- Star images commute with the displayed ambient conjugator in H. In the
source's right-conjugation notation, apply this with the inverse of h. -/
theorem starImage_conjugate (A : Subgroup G) (hAH : A ≤ H) (h : H) :
    Source.starImage H (A.map (MulAut.conj (h : G)).toMonoidHom) =
      (Source.starImage H A).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, he⟩ := hb
    let aH : H := ⟨a, hAH ha⟩
    refine mem_map.mpr ⟨q aH, mem_map_of_mem _ ha, ?_⟩
    change q h * q aH * (q h)⁻¹ = q b
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg q
    apply Subtype.ext
    exact he
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine mem_map.mpr ⟨h * a * h⁻¹, ?_, ?_⟩
    · exact mem_map.mpr ⟨a, ha, rfl⟩
    · change q (h * a * h⁻¹) = q h * q a * (q h)⁻¹
      simp only [map_mul, map_inv]

end MarkedGeometry

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
