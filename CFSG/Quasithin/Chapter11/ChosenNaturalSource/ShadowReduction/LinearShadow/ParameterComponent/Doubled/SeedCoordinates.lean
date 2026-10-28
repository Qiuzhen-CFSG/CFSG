module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Moved
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.SL3DoubledNaturalOffenders.Model
public import Theory.Representation.BinaryParabolicNatural.Basic

/-!
# Comparing the original seed with its doubled module

Faithful doubled coordinates force the L-fixed subgroup to vanish, including
on the original seed V. Its literal quotient projection is therefore bijective.
For actors whose induced automorphisms belong to the image of L, the action
on V_M is two copies of their action on V. Transport of displacement spaces
then gives |[A,V_M]| = |[A,V]|². The same image condition gives field-linearity
on V under every natural marking of the original quotient.

CriticalLine applies the square identity in both directions to the actual
critical pair, and uses field-linearity to recognize its seed commutator.
Source: Aschbacher--Smith, 11.3.6, printed p.772, second paragraph.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SeedCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The full doubled module has no L-fixed subgroup. -/
theorem full_fixed_trivial (d : Coordinates D S) :
    fullModule L V ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨m,⟨c⟩⟩ := d
  have hi : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,bot_subgroupOf]
  apply bot_unique
  rintro v ⟨hv,hc⟩
  let w : fullModule L V := ⟨v,hv⟩
  have hf (a : SL S.field.Carrier) :
      representation S.field.Carrier a (c.coordinates w).toAdd = (c.coordinates w).toAdd := by
    obtain ⟨l,hl⟩ := (LocalGeometry.Coordinates.sl3 m).quotientMap_surjective a
    have hh := c.equivariant l w
    have he : (⟨(l:G)*v*(l:G)⁻¹, (mem_normalizer_iff.mp (c.normalized l.property) v).mp hv⟩ :
        fullModule L V) = w := by
      apply Subtype.ext
      change (l:G)*v*(l:G)⁻¹=v
      rw [hc l l.property,mul_inv_cancel_right]
    change (c.coordinates (⟨(l:G)*v*(l:G)⁻¹, _⟩ : fullModule L V)).toAdd = _ at hh
    rw [he] at hh
    change (c.coordinates w).toAdd = representation S.field.Carrier
      ((LocalGeometry.Coordinates.sl3 m).quotientMap l) (c.coordinates w).toAdd at hh
    rw [hl] at hh
    exact hh.symm
  have hz : (c.coordinates w).toAdd = 0 := by
    ext i j
    obtain ⟨k,hkj⟩ : ∃ k : Fin 3, k ≠ j := by fin_cases j <;> decide
    have hh := congrArg (fun z : Space S.field.Carrier => z i k)
      (hf (Matrix.SpecialLinearGroup.transvection hkj 1))
    change ((1 : Matrix (Fin 3) (Fin 3) S.field.Carrier) + Matrix.single k j 1).mulVec
      ((c.coordinates w).toAdd i) k = (c.coordinates w).toAdd i k at hh
    simpa [Matrix.add_mulVec,Matrix.single_mulVec_eq] using hh
  exact mem_bot.mpr (congrArg Subtype.val (hi (hz.trans c.coordinates.map_one.symm)))

theorem seed_fixed_trivial (d : Coordinates D S) : V ⊓ centralizer (L : Set G) = ⊥ :=
  le_bot_iff.mp ((inf_le_inf_right _ seed_le_fullModule).trans (full_fixed_trivial d).le)

theorem projection_bijective (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    Function.Bijective (LocalGeometry.Coordinates.sl3 m).projection := by
  refine ⟨?_,(LocalGeometry.Coordinates.sl3 m).projection_surjective⟩
  apply ((LocalGeometry.Coordinates.sl3 m).projection.ker_eq_bot_iff).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [← seed_fixed_trivial d]
  exact ⟨v.property,((LocalGeometry.Coordinates.sl3 m).projection_eq_one_iff v).mp hv⟩

section Transport
variable {A W : Subgroup G} [IsElementaryAbelian 2 W]
    {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]

private def linearCoordinates (e : W ≃* Multiplicative X) : Additive W ≃ₗ[ZMod 2] X :=
  LinearEquiv.ofBijective
    (({ toFun := fun w => (e w.toMul).toAdd
        map_zero' := e.map_one
        map_add' := e.map_mul } : Additive W →+ X).toZModLinearMap 2)
    ⟨e.injective,e.surjective⟩

private theorem moved_card (hn : A ≤ normalizer (W : Set G))
    (ρ : Representation (ZMod 2) A X) (e : Additive W ≃ₗ[ZMod 2] X)
    (he : ∀ a : A, ∀ w : W,
      e (Additive.ofMul (W.normalizerMonoidHom (inclusion hn a) w)) =
        ρ a (e (Additive.ofMul w))) :
    Nat.card (subspaceCommutator ρ ⊤ ⊤) = Nat.card (⁅A,W⁆ : Subgroup G) := by
  let σ := (automizerRepresentation W).comp
    (W.normalizerMonoidHom.rangeRestrict.comp (inclusion hn))
  have hm := BinaryParabolicNatural.commutator_map σ ρ e.toLinearMap
    (fun a w => he a w.toMul) ⊤ ⊤
  rw [Submodule.map_top, e.range] at hm
  let f : A →* (⊤ : Subgroup A) := (MonoidHom.id A).codRestrict ⊤ (fun _ => mem_top _)
  have hf : Function.Surjective f := fun x => ⟨x.val,Subtype.ext rfl⟩
  have hc := coinvariants_card_of_conjugation hn
    (σ.comp (⊤ : Subgroup A).subtype) f hf (fun _ _ => rfl)
  rw [← BinaryParabolicNatural.commutator_top] at hc
  rw [← hm]
  exact (Nat.card_congr (e.submoduleMap (subspaceCommutator σ ⊤ ⊤)).toEquiv).symm.trans hc

end Transport

/-- The two copies and original seed have identical actions for every actor
in the literal L-induced automizer. -/
theorem commutator_card_square (d : Coordinates D S) {A : Subgroup G}
    (hAW : A ≤ normalizer (fullModule L V : Set G))
    (hAV : A ≤ normalizer (V : Set G))
    (hI : inducedAutomizer (fullModule L V) A ≤ inducedAutomizer (fullModule L V) L) :
    Nat.card (⁅A,fullModule L V⁆ : Subgroup G) = Nat.card (⁅A,V⁆ : Subgroup G)^2 := by
  let := fullModule_elementary d
  let := D.elementary
  obtain ⟨m,⟨c⟩⟩ := d
  let d : Coordinates D S := ⟨m,⟨c⟩⟩
  let W := fullModule L V
  let b := LocalGeometry.Coordinates.sl3 m
  let π := MulEquiv.ofBijective b.projection (projection_bijective d m)
  let eV : Additive V ≃ₗ[ZMod 2] (Fin 3 → S.field.Carrier) := linearCoordinates π
  have hi : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,bot_subgroupOf]
  let cEq : W ≃* Multiplicative (Space S.field.Carrier) :=
    MulEquiv.ofBijective c.coordinates ⟨hi,c.onto⟩
  let eW := linearCoordinates cEq
  let e := eW.trans (LinearEquiv.finTwoArrow (R := ZMod 2) (M := Fin 3 → S.field.Carrier))
  let ρ := b.conjugationAction (hAW.trans (fullModule_normalizer d).le) hAV
  have hV (a : A) (v : V) : eV (Additive.ofMul (V.normalizerMonoidHom (inclusion hAV a) v)) =
      ρ a (eV (Additive.ofMul v)) := (b.conjugationAction_projection _ _ a v).symm
  have hW (a : A) (w : W) : e (Additive.ofMul (W.normalizerMonoidHom (inclusion hAW a) w)) =
      (ρ.prod ρ) a (e (Additive.ofMul w)) := by
    let aN : normalizer (W : Set G) := inclusion hAW a
    have ha : W.normalizerMonoidHom.rangeRestrict aN ∈ inducedAutomizer W L :=
      hI (mem_map_of_mem _ a.property)
    obtain ⟨l,hl,he⟩ := ha
    have hw (v : W) : W.normalizerMonoidHom (inclusion hAW a) v =
        W.normalizerMonoidHom (inclusion c.normalized ⟨l,hl⟩) v :=
      (congrArg (fun f : Automizer W => f.val v) he).symm
    have hv (v : V) : V.normalizerMonoidHom (inclusion hAV a) v =
        V.normalizerMonoidHom (inclusion D.normalizes ⟨l,hl⟩) v := by
      apply Subtype.ext
      exact congrArg (fun w : W => (w : G)) (hw (inclusion seed_le_fullModule v))
    have hρ (x : b.Space) : ρ a x = b.modelAction (b.quotientMap ⟨l,hl⟩) x := by
      obtain ⟨v,hv'⟩ := b.projection_surjective (Multiplicative.ofAdd x)
      have hh := b.conjugationAction_projection (hAW.trans (fullModule_normalizer d).le) hAV a v
      rw [hv,b.projection_component_conjugation,hv'] at hh
      exact hh
    have hh := c.equivariant ⟨l,hl⟩ w
    rw [hw]
    apply Prod.ext
    · exact (congrFun hh 0).trans (hρ _).symm
    · exact (congrFun hh 1).trans (hρ _).symm
  rw [← moved_card hAW (ρ.prod ρ) e hW]
  have ht : (⊤ : Submodule (ZMod 2) b.Space).prod (⊤ : Submodule (ZMod 2) b.Space) = ⊤ := by ext; simp
  rw [← ht, BinaryParabolicNatural.commutator_prod]
  have hcardprod (U Z : Submodule (ZMod 2) b.Space) :
      Nat.card (U.prod Z) = Nat.card U * Nat.card Z := by
    let q : U.prod Z ≃ U × Z :=
      { toFun := fun x => ⟨⟨x.1.1,x.2.1⟩,⟨x.1.2,x.2.2⟩⟩
        invFun := fun x => ⟨⟨x.1, x.2⟩, x.1.2, x.2.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    rw [Nat.card_congr q, Nat.card_prod]
  rw [hcardprod, moved_card hAV ρ eV hV, pow_two]

/-- An actor belonging to the literal L-induced automizer is field-linear
on the original chosen quotient, for any of its natural SL3 markings. -/
theorem action_linear (d : Coordinates D S)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {A : Subgroup G} (hAW : A ≤ normalizer (fullModule L V : Set G))
    (hAV : A ≤ normalizer (V : Set G))
    (hI : inducedAutomizer (fullModule L V) A ≤ inducedAutomizer (fullModule L V) L) :
    ∀ a : A, ∀ (r : S.field.Carrier) x,
      (LocalGeometry.Coordinates.sl3 m).conjugationAction
        (hAW.trans (fullModule_normalizer d).le) hAV a (r • x) =
      r • (LocalGeometry.Coordinates.sl3 m).conjugationAction
        (hAW.trans (fullModule_normalizer d).le) hAV a x := by
  let W := fullModule L V
  let b := LocalGeometry.Coordinates.sl3 m
  let ρ := b.conjugationAction (hAW.trans (fullModule_normalizer d).le) hAV
  intro a r x
  have ha : W.normalizerMonoidHom.rangeRestrict (inclusion hAW a) ∈ inducedAutomizer W L :=
    hI (mem_map_of_mem _ a.property)
  obtain ⟨l,hl,he⟩ := ha
  have hv (v : V) : V.normalizerMonoidHom (inclusion hAV a) v =
      V.normalizerMonoidHom (inclusion D.normalizes ⟨l,hl⟩) v := by
    apply Subtype.ext
    exact (congrArg (fun f : Automizer W => (f.val (inclusion seed_le_fullModule v) : G)) he).symm
  have hρ (x : b.Space) : ρ a x = b.modelAction (b.quotientMap ⟨l,hl⟩) x := by
    obtain ⟨v,hv'⟩ := b.projection_surjective (Multiplicative.ofAdd x)
    have hh := b.conjugationAction_projection (hAW.trans (fullModule_normalizer d).le) hAV a v
    rw [hv,b.projection_component_conjugation,hv'] at hh
    exact hh
  change ρ a (r • x) = r • ρ a x
  rw [hρ,hρ]
  exact map_smul _ _ _

end SeedCoordinates
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
