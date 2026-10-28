module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Action

/-!
# Reducing the corrected joint residual to a model action calculation

The E₉ joint residual is normal in the joint centralizer. Its image under
conjugation on an invariant component is therefore a normal three-subgroup
of the actual action image. A trivial three-core in that image forces the
residual to centralize the component, contradicting the complete centralizer
alternative of `FieldModels`.

The action image lies in the automorphism centralizer of the plane and
contains the inner automorphisms induced by its fixed subgroup. The TI
hypothesis also says that every two-perfect subgroup fixed by a nonidentity
plane element is fixed by the entire plane. `ThreeCoreFreeAction` isolates a
sufficient intrinsic model calculation using exactly these action witnesses.
It is a proof obligation, not a classification assertion: this module does
not prove it for PSL₃(4), J₂ or PSL₃(7), nor select the component. The final
conditional theorem assembles fusion and this model calculation without
assuming the incompatible order-27 joint residual.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137; see `JointCentralizer` for the source correction.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G]

/-- The subgroup fixed pointwise by the given action. -/
@[expose] def fixedSubgroupOfAction {A K : Type*} [Group A] [Group K]
    (φ : A →* MulAut K) : Subgroup K where
  carrier := {x | ∀ a, φ a x = x}
  one_mem' := by simp
  mul_mem' := by intro x y hx hy a; simp [map_mul, hx a, hy a]
  inv_mem' := by intro x hx a; simp [map_inv, hx a]

/-- The intrinsic consequence of assertion (*): a two-perfect subgroup fixed
by one nonidentity actor is fixed by all actors. -/
@[expose] def FixesTwoPerfectSubgroups {A K : Type*} [Group A] [Group K]
    (φ : A →* MulAut K) : Prop :=
  ∀ (a : A), a ≠ 1 → ∀ F : Subgroup K, IsPPerfect 2 F →
    (∀ x : F, φ a x = x) → ∀ b : A, ∀ x : F, φ b x = x

/-- A sufficient model property: every automorphism subgroup centralizing
the action and containing its fixed inner automorphisms has trivial three-core.
No instance of this property for a field-component model is asserted here. -/
@[expose] def ThreeCoreFreeAction {A K : Type*} [Group A] [Group K]
    (φ : A →* MulAut K) : Prop :=
  ∀ D : Subgroup (MulAut K), D ≤ centralizer (φ.range : Set (MulAut K)) →
    (fixedSubgroupOfAction φ).map (MulAut.conj : K →* MulAut K) ≤ D →
    pCore 3 D = ⊥

/-- The TI geometry implies the intrinsic fixed-subgroup restriction. -/
theorem conjugation_fixes_twoPerfect (U K : Subgroup G) [IsKleinFour U]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hUN : U ≤ normalizer (K : Set G)) :
    FixesTwoPerfectSubgroups (K.normalizerMonoidHom.comp (inclusion hUN)) := by
  intro a ha F hF hfix b x
  let D := F.map K.subtype
  have hp : IsPPerfect 2 D := hF.of_surjective
    (K.subtype.subgroupMap F) (K.subtype.subgroupMap_surjective F)
  have haD : (a : G) ∈ centralizer (D : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have he := congrArg Subtype.val (hfix ⟨y, hy⟩)
    change (a : G) * (y : G) * (a : G)⁻¹ = (y : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hUD := centralizes_of_twoPerfect_fixed U D hU hp a.property
    (fun he => ha (Subtype.ext he)) haD
  apply Subtype.ext
  change (b : G) * ((x : K) : G) * (b : G)⁻¹ = ((x : K) : G)
  have hc := hUD b.property ((x : K) : G) (mem_map_of_mem K.subtype x.property)
  rw [← hc, mul_inv_cancel_right]

/-- The actual action of the joint centralizer on its invariant component. -/
@[expose] def jointAction (U K : Subgroup G) (f : G)
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G)) :
    jointCentralizer U f →* MulAut K :=
  K.normalizerMonoidHom.comp (inclusion hJN)

/-- Commuting ambient elements induce commuting component automorphisms. -/
theorem jointAction_range_le_centralizer (U K : Subgroup G) (f : G)
    (hUN : U ≤ normalizer (K : Set G))
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G)) :
    (jointAction U K f hJN).range ≤ centralizer
      ((K.normalizerMonoidHom.comp (inclusion hUN)).range : Set (MulAut K)) := by
  rintro _ ⟨j, rfl⟩ _ ⟨u, rfl⟩
  have hc : inclusion hUN u * inclusion hJN j =
      inclusion hJN j * inclusion hUN u := Subtype.ext (j.property.1 u u.property)
  simpa only [jointAction, MonoidHom.comp_apply, map_mul] using
    congrArg K.normalizerMonoidHom hc

/-- Inner automorphisms from the plane-fixed subgroup occur in the
actual joint-centralizer action image. -/
theorem fixed_inner_le_jointAction_range (U K : Subgroup G) (f : G)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hUN : U ≤ normalizer (K : Set G))
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G)) :
    (fixedSubgroupOfAction (K.normalizerMonoidHom.comp (inclusion hUN))).map
      (MulAut.conj : K →* MulAut K) ≤ (jointAction U K f hJN).range := by
  rintro _ ⟨k, hk, rfl⟩
  have hkU : (k : G) ∈ centralizer (U : Set G) := by
    intro u hu
    have he := congrArg Subtype.val (hk ⟨u, hu⟩)
    change u * (k : G) * u⁻¹ = (k : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  refine ⟨⟨k, hkU, hKf k.property⟩, ?_⟩
  ext x
  rfl

/-- The normal E₉ residual acts trivially if the actual action image
has trivial three-core. -/
theorem jointResidual_le_centralizer_of_threeCore [Finite G] (U K : Subgroup G) (f : G)
    (e : jointResidual U f ≃* ElementaryNine)
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G))
    (hcore : pCore 3 (jointAction U K f hJN).range = ⊥) :
    jointResidual U f ≤ centralizer (K : Set G) := by
  let J := jointCentralizer U f
  let R := pResidual 2 J
  let φ := jointAction U K f hJN
  have hcard : Nat.card R = 3 ^ 2 := by
    calc
      Nat.card R = Nat.card (jointResidual U f) := Nat.card_congr
        (R.equivMapOfInjective J.subtype J.subtype_injective).toEquiv
      _ = Nat.card ElementaryNine := Nat.card_congr e.toEquiv
      _ = 3 ^ 2 := by simp [ElementaryNine, Nat.card_eq_fintype_card]
  have hp : IsPGroup 3 R := IsPGroup.of_card hcard
  have hm : R.map φ.rangeRestrict ≤ pCore 3 φ.range :=
    le_sSup ⟨Subgroup.Normal.map inferInstance φ.rangeRestrict φ.rangeRestrict_surjective,
      hp.map φ.rangeRestrict⟩
  rw [hcore] at hm
  rintro _ ⟨r, hr, rfl⟩
  have he : φ r = 1 := congrArg Subtype.val
    (mem_bot.mp (hm (mem_map_of_mem φ.rangeRestrict hr)))
  have hk : inclusion hJN r ∈ K.normalizerMonoidHom.ker := he
  rwa [normalizerMonoidHom_ker] at hk

/-- The model three-core calculation contradicts the full component
centralizer alternative, including its exceptional-cover branch. -/
theorem jointResidual_contradiction_of_threeCore [Finite G] (U K : Subgroup G) (f : G)
    (e : jointResidual U f ≃* ElementaryNine)
    (hJN : jointCentralizer U f ≤ normalizer (K : Set G))
    (hcore : pCore 3 (jointAction U K f hJN).range = ⊥)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K) :
    False :=
  jointResidual_not_le_component_centralizer U K f e hC
    (jointResidual_le_centralizer_of_threeCore U K f e hJN hcore)

/-- Conditional terminal assembly for a chosen relatively normal component.
Fusion constructs the plane, its E₉ residual and faithful action; the intrinsic
model theorem supplies the three-core calculation. Component selection and the
three model theorems remain separate obligations. -/
theorem contradiction_of_component_model_action [Finite G]
    (V L K : Subgroup G) [IsKleinFour V] [IsQuasisimple K]
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2)
    {w f : G} (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eF : pResidual 2 (L ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (hK : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K)
    (hmodel : ∀ (U : Subgroup G), IsKleinFour U → ∀ φ : U →* MulAut K,
      Function.Injective φ → FixesTwoPerfectSubgroups φ → ThreeCoreFreeAction φ) :
    False := by
  obtain ⟨g, _, hfour, hTI, e, _, _, _, hUN, hinj⟩ :=
    faithful_conjugate_plane V L K hV hLC hindex hw hfusion eF hK hn
  let U := V.map (MulAut.conj g).toMonoidHom
  let : IsKleinFour U := hfour
  have hJN : jointCentralizer U f ≤ normalizer (K : Set G) :=
    inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hK).mp hn)
  apply jointResidual_contradiction_of_threeCore U K f e hJN _ hC
  exact hmodel U hfour _ hinj (conjugation_fixes_twoPerfect U K hTI hUN) _
    (jointAction_range_le_centralizer U K f hUN hJN)
    (fixed_inner_le_jointAction_range U K f hK hUN hJN)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
