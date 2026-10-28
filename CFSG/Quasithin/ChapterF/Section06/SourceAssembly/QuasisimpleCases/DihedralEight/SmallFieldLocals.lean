module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Theory.SpecificGroups.PSL2.CubicFourExclusion
public import Theory.SpecificGroups.PSL2.SmallFieldOrders
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# The original Goldschmidt vertices in PSL₂(7) and PSL₂(9)

Each exceptional local type contains either an element of order twelve or a
cubic group times a four-group. The actual small PSL₂ models exclude both.
Thus both original vertices have characteristic two; their common Sylow has
order eight, so the vertices are S₄. This conclusion is restricted to the two
small fields selected by the Chapter 15 action, not arbitrary PSL₂ models.
Source: Aschbacher–Smith F.6.18 and the final marked exclusion of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.GroupTheory.RankTwoAmalgam
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
private theorem no_mixed_small_psl
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (hc : Nat.card F = 7 ∨ Nat.card F = 9) (e : G ≃* PSL(2,F)) : False := by
  let f := e.toMonoidHom.comp G₂.subtype
  have hf : Function.Injective f := e.injective.comp Subtype.val_injective
  rcases h.mixed_eight_cases hcore hgood hbad hT with hi | hi
  · obtain ⟨iso⟩ := hi
    let j := iso.right.trans MixedEight.reflectionVertexEquiv
    let x := j.symm (DihedralGroup.r 1)
    apply Theory.PSL2.orderOf_ne_twelve_of_card_seven_or_nine hF hc (f x)
    rw [orderOf_injective f hf, ← j.orderOf_eq x]
    simp [x, DihedralGroup.orderOf_r_one]
  · obtain ⟨iso⟩ := hi
    let g := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
      (f.comp (iso.right.symm.toMonoidHom.comp MixedEight.baseHom))
    have hg : Function.Injective g := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp
      (hf.comp (iso.right.symm.injective.comp MixedEight.baseHom_injective))
    exact Theory.PSL2.no_injective_cubic_four_product hF g hg

theorem small_psl_symmetricFour_vertices
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (hc : Nat.card F = 7 ∨ Nat.card F = 9) (e : G ≃* PSL(2,F)) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) := by
  have hT' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 8 := by simpa only [inf_comm] using hT
  have hg : generalizedFitting G₁ = pCore 2 G₁ ∧
      generalizedFitting G₂ = pCore 2 G₂ := by
    by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
    · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
      · exact ⟨h₁, h₂⟩
      · exact (no_mixed_small_psl h hcore hT h₁ h₂ hF hc e).elim
    · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
      · exact (no_mixed_small_psl h.symm hcore hT' h₂ h₁ hF hc e).elim
      · have hs := h.intersection_card_of_neither_characteristic_two hcore h₁ h₂
        omega
  exact ⟨h.local_equiv_symmetric_four_of_intersection_card_eight hg.1 hT,
    h.symm.local_equiv_symmetric_four_of_intersection_card_eight hg.2 hT'⟩

/-- The two original vertices of an actual A₆ completion are S₄. -/
theorem alternatingSix_symmetricFour_vertices
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (e : G ≃* alternatingGroup (Fin 6)) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) := by
  have hc : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by decide)]
    norm_num
  exact small_psl_symmetricFour_vertices h hcore hT (F := GaloisField 3 2)
    ⟨3,2,by decide,by decide,by decide,by norm_num [hc]⟩ (Or.inr hc)
    (e.trans Atlas.Comparisons.Exceptional.psl2NineEquivAlt6.symm)

/-- The two original vertices of an actual SL₃(2) completion are S₄. -/
theorem binaryThree_symmetricFour_vertices
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (e : G ≃* SL(3,ZMod 2)) :
    Nonempty (G₁ ≃* Equiv.Perm (Fin 4)) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let j : G ≃* PSL(2,ZMod 7) :=
    e.trans Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two.symm
  have hc : Nat.card (ZMod 7) = 7 := Nat.card_zmod 7
  have hp : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 7)) :=
    ⟨7,1,by decide,by decide,by decide,by simpa only [pow_one] using hc⟩
  exact small_psl_symmetricFour_vertices h hcore hT (F := ZMod 7) hp (Or.inl hc) j


end CFSG.Quasithin.ChapterF.SourceAssembly
