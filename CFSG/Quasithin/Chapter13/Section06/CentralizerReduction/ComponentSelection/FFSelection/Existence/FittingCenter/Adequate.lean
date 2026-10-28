module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Complete

/-!
# The adequate Fitting-center route after 13.6.13

In the group-only outer A6--C3 case, offender generation makes the quotient
by the displayed product a two-group. The odd Fitting subgroup lies in that
product, and its solvable normal projection to A6 is trivial. Its order
therefore divides three. This supplies the missing outer case without any
assertion about a splitting of the module by its fixed space.

The other adequate branches retain their full earlier module conclusions.
The established generation arguments now apply to every adequate alternative,
and the completed known-simple classifier supplies that alternative on the
literal Thompson action. The actual solvable exclusion implies F(J*)=Z(J*).
Source: Aschbacher--Smith, B.5.6(4) and the paragraph after13.6.13, pp.105,929.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
open FFAlternatives
universe u
variable {D : Type*} [Group D] [Finite D]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem six_solvable_normal (A : Subgroup (alternatingGroup (Fin 6)))
    [A.Normal] [Group.IsSolvable A] : A = ⊥ := by
  let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 6))
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := A.subtype)
        (by rw [h]; exact topEquiv.surjective))).elim

/-- The odd Fitting subgroup lies in the literal cubic factor. -/
theorem outer_shape_fitting_le_second (ρ : Representation (ZMod 2) D W)
    (c : ChapterB.OuterSixThreeShape D) (hg : offenderSubgroup ρ = ⊤)
    (hcore : pCore 2 D = ⊥) : fittingSubgroup D ≤ c.second := by
  let P := c.first ⊔ c.second
  let : P.Normal := outerSixThreeShape_product_normal c
  let : IsCyclic (D ⧸ P) := outerSixThreeShape_quotient_isCyclic c
  let : CommGroup (D ⧸ P) := IsCyclic.commGroup
  have hq := abelian_image_isTwoGroup ρ (QuotientGroup.mk' P)
    (QuotientGroup.mk'_surjective P) hg
  have hRP : pResidual 2 D ≤ P := sInf_le ⟨inferInstance, hq⟩
  have hFP : fittingSubgroup D ≤ P := by
    intro x hx
    apply hRP
    exact mem_pResidual_of_orderOf_coprime
      ((Generation.fitting_coprime_two hcore).of_dvd_right
        ((fittingSubgroup D).orderOf_dvd_natCard hx))
  let R := (fittingSubgroup D).subgroupOf P
  let f : P →* alternatingGroup (Fin 6) := c.firstEquiv.toMonoidHom.comp
    ((MonoidHom.fst c.first c.second).comp c.product.symm.toMonoidHom)
  have hf : Function.Surjective f :=
    c.firstEquiv.surjective.comp (Prod.fst_surjective.comp c.product.symm.surjective)
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hFP).toMonoidHom) (subgroupOfEquivOfLe hFP).injective
  let : (R.map f).Normal := (inferInstance : R.Normal).map f hf
  let : Group.IsSolvable (R.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective R)
  have hz := six_solvable_normal (R.map f)
  intro x hx
  let xP : P := ⟨x, hFP hx⟩
  have hxR : xP ∈ R := hx
  have he : f xP = 1 := mem_bot.mp (hz ▸ mem_map_of_mem f hxR)
  have ha : (c.product.symm xP).1 = 1 := c.firstEquiv.map_eq_one_iff.mp he
  have hp := congrArg Subtype.val (c.product.apply_symm_apply xP)
  rw [c.product_apply, ha, Subgroup.coe_one, one_mul] at hp
  have hval : ((c.product.symm xP).2 : D) = x := hp
  exact hval ▸ (c.product.symm xP).2.property

/-- The source group configuration bounds the actual Fitting subgroup. -/
theorem outer_shape_fitting_card (ρ : Representation (ZMod 2) D W)
    (c : ChapterB.OuterSixThreeShape D) (hg : offenderSubgroup ρ = ⊤)
    (hcore : pCore 2 D = ⊥) : Nat.card (fittingSubgroup D) ∣ 3 := by
  have hc : Nat.card c.second = 3 := by
    rw [Nat.card_congr c.secondEquiv.toEquiv]
    exact Nat.card_zmod 3
  exact hc ▸ card_dvd_of_le (outer_shape_fitting_le_second ρ c hg hcore)

variable {G : Type u} [Group G] [Finite G]

/-- Every adequate branch gives generation by the actual Sylow Thompson image. -/
theorem thompson_generation_of_adequate
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hclassification : ProjectiveLine.AdequateSourceAlternative
      (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) := by
  cases hclassification with
  | trivial ht =>
    exact Generation.thompson_generation T z v hz hSyl hcore (.trivial ht)
  | quasisimple hq c =>
    exact Generation.thompson_generation_of_quasisimple T z v hz hSyl hq c
  | symmetricThree c =>
    exact Generation.thompson_generation_of_symmetricThree T z v hz hSyl hcore c
  | twoFactors c =>
    exact Generation.thompson_generation T z v hz hSyl hcore (.twoFactors c)
  | outerSixThree c =>
    exact Generation.thompson_generation_of_fitting_card_dvd_prime T z v hSyl Nat.prime_three
      (outer_shape_fitting_card _ c (thompsonRepresentation_generated z v hz)
        (JGstar_twoCore z v hcore))
  | hyperplane c =>
    exact Generation.thompson_generation_of_hyperplane T z v hz hSyl hcore c

/-- The full known-simple classification and actual solvable exclusion give F(J*)=Z(J*). -/
theorem fitting_eq_center_knownSimple
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    fittingSubgroup (JGstar z v) = center (JGstar z v) :=
  fitting_eq_center_of_commutator_generation L T z v hcore
    (thompson_generation_of_adequate T z v hz hSyl hcore
      (SourceB5.classification.general _ _ _ (thompson_hypothesis z v hz hlocal hcore)))
    hexclude

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
