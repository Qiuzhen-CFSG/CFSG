module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CentralProjection
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Theory.SpecificGroups.AlternatingSix.NoOrderTwelve
public import Theory.SpecificGroups.PSL2.CubicFourExclusion
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# The original vertices in an odd central cover of A6

Projection to A6 is faithful on each Goldschmidt vertex. An exceptional
vertex in the mixed classification would contain either an element of
order twelve or C3 times E4. The former is impossible on six points; the
latter is excluded by the actual A6--PSL2(9) comparison. Both vertices
are therefore characteristic two and are the actual symmetric groups
on four points.

Source: Aschbacher--Smith F.6.18(6), printed p.310, in its triple-A6 case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem not_mixed_alternatingSix_central_quotient
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (eQ : (G ⧸ center G) ≃* alternatingGroup (Fin 6))
    (hZ : Odd (Nat.card (center G))) : False := by
  let f := eQ.toMonoidHom.comp ((QuotientGroup.mk' (center G)).comp G₂.subtype)
  have hf : Function.Injective f := eQ.injective.comp
    (h.symm.left_center_quotient_injective hZ)
  rcases h.mixed_eight_cases hcore hgood hbad hT with hi | hi
  · obtain ⟨iso⟩ := hi
    let j := iso.right.trans MixedEight.reflectionVertexEquiv
    let x := j.symm (DihedralGroup.r 1)
    apply AlternatingSix.orderOf_ne_twelve (f x)
    rw [orderOf_injective f hf, ← j.orderOf_eq x]
    simp [x, DihedralGroup.orderOf_r_one]
  · obtain ⟨iso⟩ := hi
    let a := Atlas.Comparisons.Exceptional.psl2NineEquivAlt6.symm
    let g := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField 3 2)).comp
      (a.toMonoidHom.comp (f.comp (iso.right.symm.toMonoidHom.comp MixedEight.baseHom)))
    have hg : Function.Injective g := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp
      (a.injective.comp (hf.comp (iso.right.symm.injective.comp MixedEight.baseHom_injective)))
    have hF : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
      ⟨3, 2, by decide, by decide, by decide, by rw [GaloisField.card]; norm_num⟩
    exact Theory.PSL2.no_injective_cubic_four_product hF g hg

/-- The literal Goldschmidt vertices in an odd central cover of A6 are S4. -/
theorem alternatingSix_central_quotient_symmetricFour_vertices
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (eQ : (G ⧸ center G) ≃* alternatingGroup (Fin 6))
    (hZ : Odd (Nat.card (center G))) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) := by
  have hT' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 8 := by simpa only [inf_comm] using hT
  have hg : generalizedFitting G₁ = pCore 2 G₁ ∧
      generalizedFitting G₂ = pCore 2 G₂ := by
    by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
    · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
      · exact ⟨h₁, h₂⟩
      · exact (not_mixed_alternatingSix_central_quotient h hcore hT h₁ h₂ eQ hZ).elim
    · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
      · exact (not_mixed_alternatingSix_central_quotient h.symm hcore hT' h₂ h₁ eQ hZ).elim
      · have hs := h.intersection_card_of_neither_characteristic_two hcore h₁ h₂
        omega
  exact ⟨h.local_equiv_symmetric_four_of_intersection_card_eight hg.1 hT,
    h.symm.local_equiv_symmetric_four_of_intersection_card_eight hg.2 hT'⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
