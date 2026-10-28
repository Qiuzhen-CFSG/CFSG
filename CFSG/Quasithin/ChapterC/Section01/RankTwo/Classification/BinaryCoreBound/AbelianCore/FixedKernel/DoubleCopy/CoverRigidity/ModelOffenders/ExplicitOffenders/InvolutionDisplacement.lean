module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.ActorProducts
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.InvolutionDisplacement.InvolutionClass
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Involution displacement on the actual cover models

Every nonidentity involution of SL₃(2) moves at least two dimensions of the
universal natural cover U. At an elementary transvection, a principal cocycle
and the exceptional cocycle give independent evaluation directions. The
principal map is injective, so these directions survive in the universal
action. Actual matrix conjugacy, inverse-transpose transport, and equality
of dual displacement ranks carry this bound to U.

For diagonal actors, the displacement ranks of the two summands add.
A nonzero mixed shear makes the second coordinate projection of displacement
surjective onto V. Nonidentity mixing on U × U has an off-diagonal entry one,
which similarly gives a surjection onto U. Thus the mixed and doubled actor
involutions have displacement at least three and four, respectively.

These independent estimates supply the pointwise bounds in the cover argument
for Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),(5),
printed pp.136–137. The cover and exceptional cohomology are those of
I.1.5–6, printed p.408.
-/

public section

open Representation Representation.OneCohomology Module
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
noncomputable section

private lemma rank_equiv {X Y X' Y' : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup X'] [Module (ZMod 2) X'] [AddCommGroup Y'] [Module (ZMod 2) Y']
    (f : X →ₗ[ZMod 2] Y) (f' : X' →ₗ[ZMod 2] Y')
    (e : X ≃ₗ[ZMod 2] X') (e' : Y ≃ₗ[ZMod 2] Y')
    (h : ∀ x, e' (f x) = f' (e x)) :
    finrank (ZMod 2) f.range = finrank (ZMod 2) f'.range := by
  have he : e'.toLinearMap.comp f = f'.comp e.toLinearMap := LinearMap.ext h
  have hr := congrArg (fun a => finrank (ZMod 2) (LinearMap.range a)) he
  rw [LinearMap.range_comp, e'.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ e.range] at hr
  exact hr

private lemma universal_rank {G X : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) G X)
    (hf : fixed ρ = ⊥) (g : G) :
    finrank (ZMod 2) (LinearMap.range (universalAction ρ g - LinearMap.id)) =
      finrank (ZMod 2) (evaluation ρ g).range := by
  have hi : Function.Injective (principal ρ) := LinearMap.ker_eq_bot.mp ((ker_principal ρ).trans hf)
  have he : universalAction ρ g - LinearMap.id = (principal ρ).comp (evaluation ρ g) := by
    change LinearMap.id + _ - LinearMap.id = _
    abel
  rw [he, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (principal ρ) hi (evaluation ρ g).range).finrank_eq.symm

private abbrev transv : MatrixGroup :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

private lemma evaluation_transv_rank :
    2 ≤ finrank (ZMod 2) (evaluation base transv).range := by
  let z := SLHigherNatural.SLThreeBinary.exceptional
  let e₀ : V := Pi.single 0 1
  let e₁ : V := Pi.single 1 1
  have hp : evaluation base transv (principal base e₁) = e₀ := by
    change (principal base e₁).val transv = e₀
    rw [SLHigherNatural.principal_transvection]
    simp [e₀, e₁]
  have hz : z.val transv 2 = 1 :=
    SLHigherNatural.SLThreeBinary.exceptional_spare 0 1 2 (by decide) (by decide) (by decide)
  let v : Fin 2 → (evaluation base transv).range :=
    ![⟨e₀, ⟨principal base e₁, hp⟩⟩, ⟨z.val transv, ⟨z, rfl⟩⟩]
  have hi : LinearIndependent (ZMod 2) v := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro h
      have he := congrArg (fun w : (evaluation base transv).range => w.val 2) h
      change z.val transv 2 = 0 at he
      rw [hz] at he
      exact one_ne_zero he
    · intro a ha
      have h₂ := congrArg (fun w : (evaluation base transv).range => w.val 2) ha
      change a * z.val transv 2 = e₀ 2 at h₂
      have ha0 : a = 0 := by simpa [hz, e₀] using h₂
      have h₀ := congrArg (fun w : (evaluation base transv).range => w.val 0) ha
      change a * z.val transv 0 = e₀ 0 at h₀
      simp [ha0, e₀] at h₀
  simpa using hi.fintype_card_le_finrank

private lemma natural_universal_involution (g : MatrixGroup) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (universalAction base g - LinearMap.id)) := by
  obtain ⟨c,hc⟩ := InvolutionDisplacement.involution_conjugate_transvection g hg hne
  have he : g = c * transv * c⁻¹ := by
    have h := congrArg (fun x => x * c⁻¹) hc
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
  rw [he, ← BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
    BinaryOffender.fixedCodim_zpowers_conj,
    BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
    universal_rank base base_fixed]
  exact evaluation_transv_rank

private lemma evaluation_rank_congr {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) G X) (σ : Representation (ZMod 2) H Y)
    (a : G ≃* H) (e : X ≃ₗ[ZMod 2] Y)
    (he : ∀ g v, e (ρ g v) = σ (a g) (e v)) (g : G) :
    finrank (ZMod 2) (evaluation ρ g).range =
      finrank (ZMod 2) (evaluation σ (a g)).range := by
  apply rank_equiv (evaluation ρ g) (evaluation σ (a g)) (cocyclesCongr ρ σ a e he) e
  intro f
  change e (f.val g) = e (f.val (a.symm (a g)))
  rw [a.symm_apply_apply]

private lemma cover_involution_rank (g : MatrixGroup) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    2 ≤ finrank (ZMod 2) (LinearMap.range (cover g - LinearMap.id)) := by
  -- Retain the additive monoid and scalar action used by `universalAction`.
  -- The inherited additive-group instance need not be definitionally compatible.
  let : AddCommGroup (cocycles base.dual) :=
    @Module.addCommMonoidToAddCommGroup (ZMod 2) (cocycles base.dual) _
      (cocycles base.dual).addCommMonoid (cocycles base.dual).module
  let : Module (ZMod 2) (cocycles base.dual) := (cocycles base.dual).module
  let a := BinaryLinearThree.AutomorphismAction.graph
  let e := BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm
  have he : ∀ g v, e (base.dual g v) = base (a g) (e v) := by
    intro g v
    exact LinearMap.congr_fun (e.isIntertwining' g) v
  have hr := evaluation_rank_congr base.dual base a e.toLinearEquiv he g
  have hag : (a g) ^ 2 = 1 := by rw [← map_pow, hg, map_one]
  have hane : a g ≠ 1 := fun h => hne (a.injective (h.trans a.map_one.symm))
  have h := natural_universal_involution (a g) hag hane
  rw [universal_rank base base_fixed] at h
  have hd := BinaryOffender.fixedCodim_zpowers_dual (universalAction base.dual) g
  rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
    BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hd
  change finrank (ZMod 2) (LinearMap.range (cover g - LinearMap.id)) = _ at hd
  have hdelta : universalAction base.dual g - LinearMap.id =
      (principal base.dual).comp (evaluation base.dual g) := by
    change LinearMap.id + _ - LinearMap.id = _
    abel
  have hi : Function.Injective (principal base.dual) :=
    LinearMap.ker_eq_bot.mp ((ker_principal base.dual).trans base_dual_fixed)
  rw [hd, hdelta, LinearMap.range_comp,
    ← (Submodule.equivMapOfInjective (principal base.dual) hi
      (evaluation base.dual g).range).finrank_eq, hr]
  exact h

private lemma action_surjective {G X : Type*} [Group G]
    [AddCommGroup X] [Module (ZMod 2) X] (ρ : Representation (ZMod 2) G X) (g : G) :
    Function.Surjective (ρ g) := by
  intro v
  refine ⟨ρ g⁻¹ v, ?_⟩
  change (ρ g * ρ g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private lemma rank_ge_of_surjective_comp {X Y Z : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup Z] [Module (ZMod 2) Z] [FiniteDimensional (ZMod 2) Y]
    (f : X →ₗ[ZMod 2] Y) (p : Y →ₗ[ZMod 2] Z) (h : Function.Surjective (p.comp f)) :
    finrank (ZMod 2) Z ≤ finrank (ZMod 2) f.range := by
  have hd := Submodule.finrank_map_le p f.range
  rw [← LinearMap.range_comp, LinearMap.range_eq_top.mpr h, finrank_top] at hd
  exact hd

private lemma rank_prod_ge {X Y : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    (f : X →ₗ[ZMod 2] X) (g : Y →ₗ[ZMod 2] Y) :
    finrank (ZMod 2) f.range + finrank (ZMod 2) g.range ≤
      finrank (ZMod 2) (f.prodMap g).range := by
  let i : (f.range × g.range) →ₗ[ZMod 2] (f.prodMap g).range :=
    (f.range.subtype.prodMap g.range.subtype).codRestrict _ (by
      rintro ⟨⟨x, u, hu⟩, ⟨y, v, hv⟩⟩
      exact ⟨(u,v), Prod.ext hu hv⟩)
  have hi : Function.Injective i := by
    intro a b h
    have he := congrArg Subtype.val h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  simpa only [Module.finrank_prod] using LinearMap.finrank_le_finrank_of_injective hi

private lemma base_nonidentity_rank (g : MatrixGroup) (hne : g ≠ 1) :
    1 ≤ finrank (ZMod 2) (LinearMap.range (base g - LinearMap.id)) := by
  by_contra h
  have hz : finrank (ZMod 2) (LinearMap.range (base g - LinearMap.id)) = 0 := by omega
  have he : base g - LinearMap.id = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
  apply hne
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.toLinearMap_injective
  change base g = base 1
  rw [map_one]
  exact sub_eq_zero.mp he

private lemma mixed_nonzero_shear_rank (g : MatrixGroup) :
    3 ≤ finrank (ZMod 2) (LinearMap.range
      ((mixedParam (g,Multiplicative.ofAdd 1)).toLinearMap - LinearMap.id)) := by
  conv_lhs => rw [← finrank_V]
  apply rank_ge_of_surjective_comp _ (LinearMap.snd (ZMod 2) U V)
  intro v
  obtain ⟨w,hw⟩ := action_surjective base g v
  obtain ⟨u,hu⟩ := projection_isCover.1 w
  refine ⟨(u,0), ?_⟩
  change (mixedParam (g,Multiplicative.ofAdd 1) (u,0)).2 - 0 = v
  rw [mixedParam_apply, projection.isIntertwining, hu]
  simpa using hw

private lemma doubled_nontrivial_mixing_rank (g : MatrixGroup) (h : MixingGroup) (hne : h ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range
      ((doubledParam (g,h)).toLinearMap - LinearMap.id)) := by
  have hoff : h 0 1 = 1 ∨ h 1 0 = 1 := by
    have hall : ∀ h : MixingGroup, h ≠ 1 → h 0 1 = 1 ∨ h 1 0 = 1 := by decide +kernel
    exact hall h hne
  conv_lhs => rw [← finrank_U]
  rcases hoff with hh | hh
  · apply rank_ge_of_surjective_comp _ (LinearMap.fst (ZMod 2) U U)
    intro v
    obtain ⟨u,hu⟩ := action_surjective cover g v
    refine ⟨(0,u), ?_⟩
    change (doubledParam (g,h) (0,u)).1 - 0 = v
    rw [doubledParam_apply]
    simpa only [map_zero, smul_zero, hh, one_smul, zero_add, sub_zero] using hu
  · apply rank_ge_of_surjective_comp _ (LinearMap.snd (ZMod 2) U U)
    intro v
    obtain ⟨u,hu⟩ := action_surjective cover g v
    refine ⟨(u,0), ?_⟩
    change (doubledParam (g,h) (u,0)).2 - 0 = v
    rw [doubledParam_apply]
    simpa only [map_zero, smul_zero, hh, one_smul, add_zero, sub_zero] using hu

/-- Every nonidentity mixed involution moves at least three dimensions. -/
theorem mixedActors_involution_displacement_ge_three (a : mixedActors) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    3 ≤ finrank (ZMod 2) (LinearMap.range (a.val.toLinearMap - LinearMap.id)) := by
  obtain ⟨⟨g,c⟩, rfl⟩ := mixedActorEquiv.surjective a
  have hp : (g,c)^2 = 1 := mixedActorEquiv.injective (by simpa only [map_pow, map_one] using ha)
  have hg : g ^ 2 = 1 := congrArg Prod.fst hp
  have hc : c = 1 ∨ c = Multiplicative.ofAdd 1 := by
    have h : ∀ c : Multiplicative (ZMod 2), c = 1 ∨ c = Multiplicative.ofAdd 1 := by decide
    exact h c
  rw [mixedActorEquiv_val]
  rcases hc with rfl | rfl
  · have hg1 : g ≠ 1 := by
      intro h
      subst g
      exact hne mixedActorEquiv.map_one
    have he : (mixedParam (g,1)).toLinearMap - LinearMap.id =
        (cover g - LinearMap.id).prodMap (base g - LinearMap.id) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        mixedParam_apply, LinearMap.prodMap_apply]
      change (cover g x.1, base g x.2 + 0 • projection (cover g x.1)) - x = _
      simp only [zero_smul, add_zero]
      rfl
    rw [he]
    have h := rank_prod_ge (cover g - LinearMap.id) (base g - LinearMap.id)
    have h₁ := cover_involution_rank g hg hg1
    have h₂ := base_nonidentity_rank g hg1
    omega
  · exact mixed_nonzero_shear_rank g

/-- Every nonidentity doubled involution moves at least four dimensions. -/
theorem doubledActors_involution_displacement_ge_four (a : doubledActors) (ha : a ^ 2 = 1) (hne : a ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (a.val.toLinearMap - LinearMap.id)) := by
  obtain ⟨⟨g,h⟩, rfl⟩ := doubledActorEquiv.surjective a
  have hp : (g,h)^2 = 1 := doubledActorEquiv.injective (by simpa only [map_pow, map_one] using ha)
  have hg : g ^ 2 = 1 := congrArg Prod.fst hp
  rw [doubledActorEquiv_val]
  by_cases hh : h = 1
  · subst h
    have hg1 : g ≠ 1 := by
      intro h
      subst g
      exact hne doubledActorEquiv.map_one
    have he : (doubledParam (g,1)).toLinearMap - LinearMap.id =
        (cover g - LinearMap.id).prodMap (cover g - LinearMap.id) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        doubledParam_apply, LinearMap.prodMap_apply]
      change ((1 : ZMod 2) • cover g x.1 + 0 • cover g x.2,
        0 • cover g x.1 + (1 : ZMod 2) • cover g x.2) - x = _
      simp only [zero_smul, add_zero, one_smul, zero_add]
      rfl
    rw [he]
    have h := rank_prod_ge (cover g - LinearMap.id) (cover g - LinearMap.id)
    have h₁ := cover_involution_rank g hg hg1
    omega
  · exact doubled_nontrivial_mixing_rank g h hh

end
end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
