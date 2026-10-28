module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Membership
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.QuotientPentagons

/-!
# The original two-member parabolic family E(z)

The canonical quotient-pentagon correspondence restricts to the parabolics
containing the original marked inverter u. Its genuine order-four root in
I and the original quotient calculation select exactly two pentagons.
Thus the literal family of H-conjugates of F₁ containing u has order two.
Neither a six-five-subgroup closure nor normalization of an SL₂(5) factor
is used. The endpoint, source choices and quotient map remain unchanged.
Source: Aschbacher--Smith J.4.7, the E(z) paragraph on printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
open Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (p : Plane d) (s : SourceChoice p) (B5 : Sylow 5 d.toTypeRuSetup.H)
  (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹)

/-- Restrict the proved source correspondence using an actual membership criterion. -/
@[expose] def familyEquivOfMembership (u : G) (pred : Sylow 5 S5 → Prop)
    (hm : ∀ P, u ∈ parabolicFor p B5 P ↔ pred P) :
    {P : Sylow 5 S5 // pred P} ≃ family p B5 u :=
  Equiv.ofBijective
    (fun P => ⟨parabolicFor p B5 P, parabolicFor_mem p B5 P, (hm P).mpr P.property⟩)
    ⟨fun _ _ hh => Subtype.ext (parabolicFor_injective p s B5 hi (congrArg Subtype.val hh)), by
      rintro ⟨E, hE, hu⟩
      obtain ⟨h, rfl⟩ := hE
      let P := d.ru2.quotientMap h • basePentagon B5
      have he := parabolicFor_eq_conjugate p s B5 hi h
      refine ⟨⟨P, (hm P).mp ?_⟩, Subtype.ext he⟩
      rwa [he]⟩

theorem familyEquivOfMembership_apply (u : G) (pred : Sylow 5 S5 → Prop)
    (hm : ∀ P, u ∈ parabolicFor p B5 P ↔ pred P) (P : {P : Sylow 5 S5 // pred P}) :
    (familyEquivOfMembership p s B5 hi u pred hm P : Subgroup G) =
      parabolicFor p B5 P := rfl

/-- The exact square criterion gives an equivalence with the original containing family. -/
@[expose] def squareFamilyEquiv (t : d.toTypeRuSetup.H) (ht : orderOf (d.ru2.quotientMap t)=4) :
    {P : Sylow 5 S5 // d.ru2.quotientMap (t^2) ∈ normalizer ((P : Subgroup S5) : Set S5)} ≃
      family p B5 ((t : G)^2) :=
  familyEquivOfMembership p s B5 hi ((t : G)^2) _ (square_mem_iff p s B5 hi t ht)

include s hi in
/-- Exactly two original parabolics contain a square with the marked quotient order-four root. -/
theorem square_family_card (t : d.toTypeRuSetup.H) (ht : orderOf (d.ru2.quotientMap t)=4) :
    Nat.card (family p B5 ((t : G)^2)) = 2 := by
  apply (Nat.card_congr (squareFamilyEquiv p s B5 hi t ht)).symm.trans
  simpa only [map_pow] using
    Theory.SpecificGroups.SymmetricFive.SquareNormalizer.sylow_square_normalizer_count _ ht

variable (c : Choices d) (e : first ≃* p.F₁ B5)

/-- The original marked inverter regarded in its original centralizer H. -/
@[expose] def sourceInverter : d.toTypeRuSetup.H :=
  ⟨sourceU e, p.F₁_le_H B5 (e modelU).property⟩

include s hi c in
/-- Source membership is exactly normalization of the canonical quotient pentagon. -/
theorem source_family_mem_iff
    (hz : (e modelZ : G)=c.z)
    (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    (P : Sylow 5 S5) :
    sourceU e ∈ parabolicFor p B5 P ↔
      d.ru2.quotientMap (sourceInverter p B5 e) ∈ normalizer ((P : Subgroup S5) : Set S5) := by
  obtain ⟨t,_,ht2,ht,_,_⟩ := source_quotient_pentagons c B5 e hz hfive
  have he : t^2=sourceInverter p B5 e := Subtype.ext ht2
  have hh := square_mem_iff p s B5 hi t ht P
  rwa [ht2,he] at hh

/-- The canonical quotient labels are retained in the actual original two-member family. -/
@[expose] def sourceFamilyEquiv
    (hz : (e modelZ : G)=c.z)
    (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5) :
    {P : Sylow 5 S5 // d.ru2.quotientMap (sourceInverter p B5 e) ∈
      normalizer ((P : Subgroup S5) : Set S5)} ≃ family p B5 (sourceU e) :=
  familyEquivOfMembership p s B5 hi (sourceU e) _ (source_family_mem_iff p s B5 hi c e hz hfive)

theorem sourceFamilyEquiv_apply
    (hz : (e modelZ : G)=c.z)
    (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)
    (P : {P : Sylow 5 S5 // d.ru2.quotientMap (sourceInverter p B5 e) ∈
      normalizer ((P : Subgroup S5) : Set S5)}) :
    (sourceFamilyEquiv p s B5 hi c e hz hfive P : Subgroup G) = parabolicFor p B5 P := rfl

include s hi c in
/-- The original E(z) has exactly two members, with all model and quotient
inputs supplied by the genuine marked first endpoint. -/
theorem source_family_card
    (hz : (e modelZ : G)=c.z)
    (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5) :
    Nat.card (family p B5 (sourceU e)) = 2 := by
  obtain ⟨t,_,ht2,ht,_,_⟩ := source_quotient_pentagons c B5 e hz hfive
  rw [← ht2]
  exact square_family_card p s B5 hi t ht

include c in
/-- Every original conjugate already contains z, since H centralizes z. -/
theorem conjugateFamily_contains_z (hz : (e modelZ : G)=c.z)
    {E : Subgroup G} (hE : E ∈ conjugateFamily p B5) : c.z ∈ E := by
  obtain ⟨h,rfl⟩ := hE
  have hzF : c.z ∈ p.F₁ B5 := hz ▸ (e modelZ).property
  have hh : (h : G)*c.z=c.z*(h : G) := by
    apply mem_centralizer_singleton_iff.mp
    rw [← c.H_eq_centralizer_z]
    exact h.property
  exact ⟨c.z,hzF,mul_inv_eq_of_eq_mul hh⟩

include c in
/-- The containing-inverter definition is exactly the source definition
requiring the original pair span to lie in the parabolic. -/
theorem source_family_iff_pair (hz : (e modelZ : G)=c.z) (E : Subgroup G) :
    E ∈ family p B5 (sourceU e) ↔ E ∈ conjugateFamily p B5 ∧
      zpowers c.z ⊔ zpowers (sourceU e) ≤ E := by
  constructor
  · rintro ⟨hE,hu⟩
    exact ⟨hE,sup_le (zpowers_le.mpr (conjugateFamily_contains_z p B5 c e hz hE))
      (zpowers_le.mpr hu)⟩
  · rintro ⟨hE,hpair⟩
    exact ⟨hE,(le_sup_right.trans hpair) (mem_zpowers (sourceU e))⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
