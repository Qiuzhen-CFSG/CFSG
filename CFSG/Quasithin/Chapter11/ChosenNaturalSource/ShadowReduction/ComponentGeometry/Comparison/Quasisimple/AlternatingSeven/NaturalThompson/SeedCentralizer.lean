module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.SeedQuotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import Theory.GroupTheory.PerfectFiveSectionSmallCore
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The original quotient centralizer fixes the marked seed image

The actual projection from L1 has solvable kernel, so its PSL2(4)
two-core quotient survives in the seed image inside A7. The image two-core
has order dividing eight. Perfectness and the simple five-section make
that two-core central. An element normalizing L1 and centralizing L/O2(L)
therefore gives two maps from L1 to its image which agree modulo a central
kernel. Perfectness makes them equal on the literal image.

This is the quotient-action compatibility required in the final paragraph
of Aschbacher--Smith 11.4.2, printed p.777. The actual earlier L1 quotient
marking remains explicit; its source owner is qt-d-1222-natural-flag-cartan.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

theorem field_four (hmodel : AlternatingSevenModel E) :
    Nat.card E.input.field.Carrier = 4 := by
  rw [E.input.field.card_eq,hmodel.1]
  rfl

/-- The surviving quotient uses the literal seed projection. -/
def seedCoreQuotientEquiv
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    (seedImage E ⧸ pCore 2 (seedImage E)) ≃* PSL(2,E.input.field.Carrier) := by
  let d := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (field_four E hmodel)).some
  let : IsSimpleGroup (E.L₁ ⧸ pCore 2 E.L₁) := (e.trans d).isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsSolvable (seedProjection E).ker := seedProjection_ker_solvable E hstar hmodel
  exact (PerfectCoreTwoExtension.solvableKernelQuotientEquiv
    (seedProjection E) (seedProjection_surjective E)).symm.trans e

/-- The A7 order bound and perfect five-section centralize the seed two-core. -/
theorem seedCore_le_center
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier)) :
    pCore 2 (seedImage E) ≤ center (seedImage E) := by
  obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (field_four E hmodel)
  let t := (seedCoreQuotientEquiv E hstar hmodel e).trans d
  let : IsSimpleGroup (seedImage E ⧸ pCore 2 (seedImage E)) := t.isSimpleGroup
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let : Group.IsPerfect (seedImage E) :=
    Group.IsPerfect.ofSurjective (f := seedProjection E) (seedProjection_surjective E)
  apply pCore_two_le_center_of_perfect_simple_five_section
  · have hc : Nat.card (seedImage E ⧸ pCore 2 (seedImage E)) = 60 := by
      rw [Nat.card_congr t.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc]
    decide
  · have hcomponent : Nat.card (componentImage E) = 2520 := by
      change Nat.card ((component E).map (projection E)) = 2520
      rw [Nat.card_congr hmodel.2.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hdiv : Nat.card (pCore 2 (seedImage E)) ∣ 2520 := by
      rw [← hcomponent]
      exact (pCore 2 (seedImage E)).card_subgroup_dvd_card.trans
        (card_dvd_of_injective (inclusion (seedImage_le_componentImage E))
          (inclusion_injective _))
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := seedImage E)).exists_card_eq
    rw [hn] at hdiv ⊢
    have hcop : Nat.Coprime (2 ^ n) 315 := (by decide : Nat.Coprime 2 315).pow_left n
    exact hcop.dvd_of_dvd_mul_right (show 2 ^ n ∣ 8 * 315 from hdiv)

/-- The original quotient centralizer fixes the actual seed image. -/
theorem projection_centralizes_seedImage_of_coreQuotientCentralizer
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel E)
    (e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* PSL(2,E.input.field.Carrier))
    (a : localGroup E) (hn : (a : G) ∈ normalizer (E.L₁ : Set G))
    (ha : (a : G) ∈ Closure.coreQuotientCentralizer L) :
    projection E a ∈ centralizer (seedImage E : Set (ActionQuotient E)) := by
  let : Group.IsPerfect E.L₁ := LocalGeometry.localResidual_perfect _
  let b := E.L₁.normalizerMonoidHom ⟨a,hn⟩
  have hp : (pCore 2 E.L₁).map (seedProjection E) ≤ pCore 2 (seedImage E) := by
    have hn' : ((pCore 2 E.L₁).map (seedProjection E)).Normal :=
      Subgroup.Normal.map inferInstance _ (seedProjection_surjective E)
    exact le_sSup ⟨hn',pCore_isPGroup.map _⟩
  have he : (seedProjection E).comp b.toMonoidHom = seedProjection E := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      (QuotientGroup.mk' (pCore 2 (seedImage E)))
      (by rw [QuotientGroup.ker_mk']; exact seedCore_le_center E hstar hmodel e)
    ext l
    apply QuotientGroup.eq_iff_div_mem.mpr
    change seedProjection E (b l) / seedProjection E l ∈ pCore 2 (seedImage E)
    rw [← map_div]
    apply hp (mem_map_of_mem _ ?_)
    have hcomm : ⁅(a : G),(l : G)⁆ ∈ E.L₁.pCoreIn 2 := by
      apply inf_pCoreIn_le_of_le 2 E.L₁_le
      refine ⟨?_, Closure.coreQuotientCentralizer_commutator ha (E.L₁_le l.property)⟩
      change (a : G) * (l : G) * (a : G)⁻¹ * (l : G)⁻¹ ∈ E.L₁
      exact E.L₁.mul_mem ((hn l).mp l.property) (E.L₁.inv_mem l.property)
    obtain ⟨k,hk,he⟩ := hcomm
    have hk' : k = b l / l := by
      apply Subtype.ext
      simpa only [b,subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,
        normalizerMonoidHom_apply_apply_coe,commutatorElement_def] using he
    exact hk' ▸ hk
  intro x hx
  obtain ⟨l,hl⟩ := seedProjection_surjective E ⟨x,hx⟩
  have hc := congrArg (fun f : E.L₁ →* seedImage E => (f l : ActionQuotient E)) he
  have hconj : projection E a * (seedProjection E l : ActionQuotient E) *
      (projection E a)⁻¹ = (seedProjection E l : ActionQuotient E) := by
    change projection E (a * ⟨l,((le_conjugateSpanBy _ _).trans le_sup_left) l.property⟩ * a⁻¹) = _ at hc
    rw [map_mul,map_mul,map_inv] at hc
    exact hc
  have hx' : (seedProjection E l : ActionQuotient E) = x := congrArg Subtype.val hl
  rw [hx'] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
