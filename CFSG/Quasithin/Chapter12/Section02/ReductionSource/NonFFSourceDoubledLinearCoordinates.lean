module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowLinearThree
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# Natural–dual coordinates on the original linear-three doubled orbit

The literal seed marking retains the full SL3 scalar center. Its actual
kernel in L is characteristic, so the original conjugation twist descends
to this same actor. The proved same-actor natural-or-dual comparison and
the marked nonisomorphism force the dual alternative. Multiplication then
identifies the whole source orbit with natural plus binary dual, retaining
both original conjugate seed axes. No coordinates on the whole orbit or
nonbinary weak-closure bounds are additional inputs.

Source: Aschbacher--Smith D.3.10, 7.1.1 and Table7.2.1, printed pp.201,696–698.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open Chapter7.NormalizedSource

private theorem linear_pair_coordinates (F : BinaryField)
    {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U)
    (q : J →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (e : U ≃ₗ[ZMod 2] (Fin 3 → F.Carrier))
    (he : ∀ j v, e (ρ j v) = linearNatural F 3 (q j) (e v))
    (α : MulAut J) (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    ∃ E : (U × U) ≃ₗ[ZMod 2]
      ((Fin 3 → F.Carrier) × Module.Dual (ZMod 2) (Fin 3 → F.Carrier)),
      (∀ j v, E ((ρ.prod (ρ.comp α.toMonoidHom)) j v) =
        ((linearNatural F 3).prod (linearNatural F 3).dual) (q j) (E v)) ∧
      (∀ v, (E v).1 = e v.1) ∧
      (∀ v, (E v).2 = 0 ↔ v.2 = 0) := by
  let τ := linearNatural F 3
  have ht : IsLinearNatural τ F 3 :=
    ⟨⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩⟩
  have ha' : IsLinearNatural (τ.comp a.toMonoidHom) F 3 :=
    ⟨⟨a,LinearEquiv.refl _ _,fun _ _ => rfl⟩⟩
  rcases linearThree_naturals_same_or_dual (τ.comp a.toMonoidHom) τ F F ha' ht with hs | hd
  · obtain ⟨b⟩ := hs
    let c := (e.trans b.symm.toLinearEquiv).trans e.symm
    apply (hne ?_).elim
    refine ⟨Representation.Equiv.mk c ?_⟩
    intro j
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (c (ρ j v)) = e (ρ (α j) (c v))
    rw [he]
    change e (e.symm (b.symm (e (ρ j v)))) =
      τ (q (α j)) (e (e.symm (b.symm (e v))))
    rw [e.apply_symm_apply,e.apply_symm_apply,he,←ha]
    exact LinearMap.congr_fun (b.symm.isIntertwining' (q j)) (e v)
  · obtain ⟨b⟩ := hd
    refine ⟨e.prodCongr (e.trans b.toLinearEquiv),?_,fun _ => rfl,?_⟩
    · intro j v
      apply Prod.ext
      · exact he j v.1
      · change b (e (ρ (α j) v.2)) = τ.dual (q j) (b (e v.2))
        rw [he,←ha]
        exact LinearMap.congr_fun (b.isIntertwining' (q j)) (e v.2)
    · intro v
      exact (e.trans b.toLinearEquiv).map_eq_zero_iff

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem seed_linear_three_marking [IsElementaryAbelian 2 V]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (F : BinaryField)
    (m : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)) :
    ∃ q : L →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier,
      Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ e : Additive V ≃ₗ[ZMod 2] (Fin 3 → F.Carrier),
      ∀ l v, e (doubledSeedAction L V D.normalizes l v) =
        linearNatural F 3 (q l) (e v) := by
  let q := m.groupEquiv.toMonoidHom.comp D.componentHom
  have hq : Function.Surjective q := m.groupEquiv.surjective.comp D.componentHom_surjective
  have hk := D.componentHom_kernel_characteristic_of_linearThree h.quasisimple F m.groupEquiv
  have hker : q.ker.Characteristic := by
    change (m.groupEquiv.toMonoidHom.comp D.componentHom).ker.Characteristic
    rw [MonoidHom.ker_comp_of_injective _ _ m.groupEquiv.injective]
    exact hk
  let e := (seedCoordinates D).symm.trans m.linearEquiv
  refine ⟨q,hq,hker,e,?_⟩
  intro l v
  obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
  rw [←seedCoordinates_action D]
  simp only [e,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  exact m.intertwines (D.componentHom l) w

/-- Same-actor coordinates retaining both original conjugate seed subgroups. -/
theorem sourceOrbit_linear_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier, Function.Surjective q ∧
      ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2] ((Fin 3 → F.Carrier) × Module.Dual (ZMod 2) (Fin 3 → F.Carrier)),
        (∀ l v, e (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) =
            ((linearNatural F 3).prod (linearNatural F 3).dual) (q l) (e v)) ∧
        (∀ v, (e v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (e v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let := D.elementary
  have hmark := @seed_linear_three_marking G _ _ T L V D D.elementary h F hmodel.some
  let q := hmark.choose
  have hq : Function.Surjective q := hmark.choose_spec.1
  let : q.ker.Characteristic := hmark.choose_spec.2.1
  let e := hmark.choose_spec.2.2.choose
  have he := hmark.choose_spec.2.2.choose_spec
  have hcoords := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let t := hcoords.choose
  have ht : t ∈ (T : Subgroup G) := hcoords.choose_spec.choose
  have hpair := hcoords.choose_spec.choose_spec
  have hne := hpair.2.1
  let c := hpair.2.2.choose
  have hc : ∀ l v, c (doubledPairAction L V D.normalizes t
      (D.sylow_normalizes_component ht) l v) = doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l (c v) := hpair.2.2.choose_spec.2
  have hmul : ∀ v w, ((c (v,w)).toMul : G) =
      (v.toMul : G) * (t * (w.toMul : G) * t⁻¹) := hpair.2.2.choose_spec.1
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  have haut := descend_twist q hq α
  have hmodel := linear_pair_coordinates F
    (doubledSeedAction L V D.normalizes) q e he α haut.choose haut.choose_spec hne
  let E := hmodel.choose
  have hE := hmodel.choose_spec.1
  have hzero := hmodel.choose_spec.2.2
  have hzero' (v : Additive V × Additive V) : (E v).1 = 0 ↔ v.1 = 0 := by
    rw [hmodel.choose_spec.2.1]
    exact e.map_eq_zero_iff
  let C := c.symm.trans E
  refine ⟨t,ht,hpair.1,q,hq,C,?_,?_,?_⟩
  · intro l v
    obtain ⟨w,rfl⟩ := c.surjective v
    rw [← hc]
    simp only [C, LinearEquiv.trans_apply, c.symm_apply_apply]
    exact hE l w
  · intro v
    change (E (c.symm v)).2 = 0 ↔ (v.toMul : G) ∈ V
    rw [hzero]
    have hc0 (w : Additive V) : ((c (w,0)).toMul : G) = (w.toMul : G) := by
      simpa using hmul w 0
    constructor
    · intro hz
      have hv : c ((c.symm v).1,0) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact (c.symm v).1.toMul.property
    · intro hv
      let w : Additive V := Additive.ofMul ⟨v.toMul,hv⟩
      have hw : c (w,0) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hc0 w
      rw [← hw, c.symm_apply_apply]
  · intro v
    change (E (c.symm v)).1 = 0 ↔ _
    rw [hzero']
    have hc0 (w : Additive V) : ((c (0,w)).toMul : G) =
        t * (w.toMul : G) * t⁻¹ := by
      simpa using hmul 0 w
    constructor
    · intro hz
      have hv : c (0,(c.symm v).2) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom (c.symm v).2.toMul.property
    · rintro ⟨w,hw,hv⟩
      let z : Additive V := Additive.ofMul ⟨w,hw⟩
      have hz : c (0,z) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hc0 z).trans hv
      rw [← hz, c.symm_apply_apply]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
