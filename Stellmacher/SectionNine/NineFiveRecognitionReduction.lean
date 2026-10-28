module

public import Stellmacher.PushingUp.FaithfulFourNaturalAction
public import Stellmacher.SectionOne.Defs
public import Stellmacher.SectionNine.NineFiveSupportData
public import Stellmacher.TwoSL2FactorsWreathRecognition

/-!
# The order-four faithful-action recognition needed in (9.5)

An even-order group with trivial two-core acting faithfully on an
elementary abelian group of order four is SL2(2). The coordinate embedding
forces its order to divide six, and the core hypothesis excludes order two.
The graph application must produce the faithful terminal quotient action.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u v

public theorem nine_five_sl2_of_faithful_card_four
    {Actor : Type u} {Module : Type v}
    [Group Actor] [Finite Actor] [Group Module] [Finite Module]
    [IsElementaryAbelian 2 Module] [MulDistribMulAction Actor Module]
    (hfaithful : fixingSubgroup Actor (Set.univ : Set Module) = ⊥)
    (hcard : Nat.card Module = 4)
    (heven : Even (Nat.card Actor))
    (hcore : pCore 2 Actor = ⊥) : IsSL2Two Actor := by
  obtain ⟨representation, hinjective, _⟩ :=
    FourGroupMatrixCoordinates.faithful_card_four_embedding hfaithful hcard
  have hmodel : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have hdiv : Nat.card Actor ∣ 6 := by
    rw [← hmodel]
    exact Subgroup.card_dvd_of_injective representation hinjective
  have hnotTwo : Nat.card Actor ≠ 2 := by
    intro htwo
    have hgroup : IsPGroup 2 Actor := IsPGroup.of_card (n := 1) (by simpa using htwo)
    have htop : (⊤ : Subgroup Actor) ≤ pCore 2 Actor :=
      le_sSup ⟨inferInstance, hgroup.to_subgroup _⟩
    have hbot : (⊤ : Subgroup Actor) = ⊥ := by
      rw [hcore] at htop
      exact bot_unique htop
    have hone : Nat.card Actor = 1 := by
      rw [← Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup Actor) ≃* Actor).toEquiv]
      exact Subgroup.card_eq_one.mpr hbot
    omega
  have hsix : Nat.card Actor = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hdiv
    have hcases : ∀ order ≤ 6, order ∣ 6 → Even order → order ≠ 2 → order = 6 := by
      decide
    exact hcases _ hle hdiv heven hnotTwo
  exact ⟨MulEquiv.ofBijective representation
    ((Nat.bijective_iff_injective_and_card representation).mpr
      ⟨hinjective, hsix.trans hmodel.symm⟩)⟩

public theorem nine_five_terminal_quotient_model_of_equiv
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    {Model : Type v} [Group Model]
    (hequiv : Nonempty
      ((GAt ctx.Γ ctx.criticalPath.a' ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) ≃*
        Model)) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') Model := by
  obtain ⟨equiv⟩ := hequiv
  refine ⟨equiv.toMonoidHom.comp (QuotientGroup.mk' _),
    equiv.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective, QuotientGroup.ker_mk']
  change pCore 2 (ctx.Γ.stabilizer ctx.criticalPath.a') =
    (ctx.Γ.twoCoreAt ctx.criticalPath.a').subgroupOf _
  rw [ctx.Γ.twoCoreAt_def]
  exact (Subgroup.comap_map_eq_self_of_injective
    (ctx.Γ.stabilizer ctx.criticalPath.a').subtype_injective _).symm

public theorem nine_five_terminal_wreath_model_of_two_factors
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (first second : Subgroup
      (GAt ctx.Γ ctx.criticalPath.a' ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a')))
    (hfirst : IsSL2Two first) (hsecond : IsSL2Two second)
    (hcommute : first ≤ Subgroup.centralizer (second : Set _))
    (hdisjoint : Disjoint first second) [(first ⊔ second).Normal]
    (hcentralizer : Subgroup.centralizer ((first ⊔ second : Subgroup
      (GAt ctx.Γ ctx.criticalPath.a' ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))) :
        Set (GAt ctx.Γ ctx.criticalPath.a' ⧸ pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))) = ⊥)
    (hpermute : ∀ element,
      (first.conjBy element = first ∧ second.conjBy element = second) ∨
      (first.conjBy element = second ∧ second.conjBy element = first))
    (hswap : ∃ element, first.conjBy element = second) :
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 := by
  exact nine_five_terminal_quotient_model_of_equiv ctx
    (wreath_of_two_sl2_factors first second hfirst hsecond hcommute hdisjoint
      hcentralizer hpermute hswap)

end Stellmacher.SectionNine
