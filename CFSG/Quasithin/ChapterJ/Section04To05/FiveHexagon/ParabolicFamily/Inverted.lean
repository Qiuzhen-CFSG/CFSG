module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.ParabolicFamily.Source

/-!
# The original parabolic labels as inverted quotient pentagons

The original source inverter has quotient order two. An involution normalizing
a five-subgroup of S5 must invert it, since its centralizer has odd order.
Thus the proved parabolic correspondence is also the literal correspondence
with the two inverted quotient pentagons in J.4.7, printed p.443.
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
  (c : Choices d) (e : first ≃* p.F₁ B5)
  (hz : (e modelZ : G)=c.z)
  (hfive : (zpowers modelRotation).map ((p.F₁ B5).subtype.comp e.toMonoidHom)=B5Image B5)

include c hz hfive in
/-- The original inverter has order two in the original Ru2 quotient. -/
theorem source_quotient_order_two : orderOf (d.ru2.quotientMap (sourceInverter p B5 e))=2 := by
  obtain ⟨t,_,ht2,ht,_,_⟩ := source_quotient_pentagons c B5 e hz hfive
  have he : t^2=sourceInverter p B5 e := Subtype.ext ht2
  rw [← he,map_pow,orderOf_pow,ht]
  decide

include s hi c hz hfive in
/-- Membership in the canonical parabolic means inversion of its literal
quotient pentagon by the original u image. -/
theorem source_family_mem_iff_inverts (P : Sylow 5 S5) :
    sourceU e ∈ parabolicFor p B5 P ↔
      ∀ x ∈ (P : Subgroup S5),
        d.ru2.quotientMap (sourceInverter p B5 e) * x *
          (d.ru2.quotientMap (sourceInverter p B5 e))⁻¹ = x⁻¹ := by
  rw [source_family_mem_iff p s B5 hi c e hz hfive P]
  let v := d.ru2.quotientMap (sourceInverter p B5 e)
  have hv : orderOf v=2 := source_quotient_order_two p B5 c e hz hfive
  have hP := Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.card_sylow P
  constructor
  · intro hn
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one (P : Subgroup S5)
      (by rw [hP]; decide) v ((orderOf_eq_prime_iff.mp hv).1) hn with hc | hI
    · have hvc : v ∈ centralizer ((P : Subgroup S5) : Set S5) := by
        intro x hx
        exact (hc x hx).eq.symm
      have hh := orderOf_dvd_natCard (⟨v,hvc⟩ : centralizer ((P : Subgroup S5) : Set S5))
      rw [← orderOf_coe,hv,Equiv.Perm.five_subgroup_centralizer_card (P : Subgroup S5) hP] at hh
      contradiction
    · exact hI
  · intro hI
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨y,hy,rfl⟩
      change v*y*v⁻¹ ∈ (P : Subgroup S5)
      rw [hI y hy]
      exact inv_mem hy
    · rw [card_map_of_injective (MulAut.conj v).injective]

/-- The literal two inverted quotient pentagons label precisely the original E(z). -/
@[expose] def sourceInvertedFamilyEquiv :
    {P : Sylow 5 S5 // ∀ x ∈ (P : Subgroup S5),
      d.ru2.quotientMap (sourceInverter p B5 e) * x *
        (d.ru2.quotientMap (sourceInverter p B5 e))⁻¹ = x⁻¹} ≃
      family p B5 (sourceU e) :=
  familyEquivOfMembership p s B5 hi (sourceU e) _
    (source_family_mem_iff_inverts p s B5 hi c e hz hfive)

theorem sourceInvertedFamilyEquiv_apply
    (P : {P : Sylow 5 S5 // ∀ x ∈ (P : Subgroup S5),
      d.ru2.quotientMap (sourceInverter p B5 e) * x *
        (d.ru2.quotientMap (sourceInverter p B5 e))⁻¹ = x⁻¹}) :
    (sourceInvertedFamilyEquiv p s B5 hi c e hz hfive P : Subgroup G) =
      parabolicFor p B5 P := rfl

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily
