module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledFF
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# FF on the actual binary natural four- and five-space doubled orbit

The chosen seed marking identifies its faithful component image with GLₙ(2).
Since this image is centerless, the kernel in L is the inverse image of the
center of L/O₂(L), hence characteristic. The original inverse-conjugation
twist therefore descends to that same matrix actor. Its nonisomorphism,
retained in MarkedDoubled, forces the contragredient coordinate.

Multiplication coordinates then transport the checked radical offender to
the original orbit action and its full linear normalizer. No marking of
the entire orbit, FF premise, or ambient doubled-natural exclusion is used.
The two implementation imports are confined to verifying the literal
seed and orbit projection formulas; no public boundary is changed.

This discharges the FF input of `sourceOrbit_false_of_markedDoubled_inputs`.
The remaining non-FF row bounds stay explicit in that assembly.
Source: Aschbacher--Smith, D.3.10, 3.2.5 and 7.1, printed pp.201,580,696.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource BinaryLinear.OuterCyclic
private theorem imageFF_of_surjective {J P U W : Type*} [Group J] [Group P]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) J U) (σ : Representation (ZMod 2) P W)
    (q : J →* P) (hq : Function.Surjective q) (E : U ≃ₗ[ZMod 2] W)
    (hE : ∀ l v, σ (q l) (E v) = E (τ l v))
    (hp : IsFFModule (imageRepresentation τ)) : IsFFModule (normalizerRepresentation σ) := by
  have hE' : ∀ l w, τ l (E.symm w) = E.symm (σ (q l) w) := by
    intro l w
    apply E.injective
    rw [← hE, E.apply_symm_apply, E.apply_symm_apply]
  let ψ := equivariantActionImageEquiv τ σ q E.symm hq hE'
  have hσ : IsFFModule (imageRepresentation σ) := by
    apply hp.map_equivariant _ _ ψ.symm.toMonoidHom ψ.symm.injective E
    intro p v
    apply E.symm.injective
    rw [E.symm_apply_apply]
    have hh := congrArg (fun z : actionImage τ => z.val.val v) (ψ.apply_symm_apply p)
    exact hh.symm
  exact hσ.map_equivariant _ (normalizerRepresentation σ)
    (inclusion (actionImage σ).le_normalizer) (inclusion_injective _)
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem quotient_center_kernel {P : Type*} [Group P] [Nontrivial P]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (f : D.componentImage ≃* P) (hz : center P = ⊥) :
    ((f.toMonoidHom).comp D.componentHom).ker.Characteristic := by
  let := h.quasisimple
  let q := f.toMonoidHom.comp D.componentHom
  let r := f.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := f.surjective.comp D.componentQuotientHom_surjective
  have hk : r.ker = center (L ⧸ pCore 2 L) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [hz, MonoidHom.comap_bot] at hh
    exact hh
  have he : q.ker = (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
    rw [← hk]
    rfl
  rw [show ((f.toMonoidHom).comp D.componentHom).ker = q.ker from rfl, he]
  exact Subgroup.Characteristic.comap_quotient_mk inferInstance

private theorem descend_twist {J P : Type*} [Group J] [Group P]
    (q : J →* P) (hq : Function.Surjective q) [q.ker.Characteristic] (α : MulAut J) :
    ∃ a : MulAut P, ∀ j, a (q j) = q (α j) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let b := QuotientGroup.congr q.ker q.ker α (characteristic_iff_map_eq.mp inferInstance α)
  refine ⟨(e.symm.trans b).trans e, ?_⟩
  intro j
  have he (x : J) : e (QuotientGroup.mk' q.ker x) = q x := rfl
  change e (b (e.symm (q j))) = q (α j)
  rw [← he j, e.symm_apply_apply]
  exact he (α j)

private def seedCoordinates [IsElementaryAbelian 2 V] : D.space ≃ₗ[ZMod 2] Additive V :=
  (ReducedNormal.subspaceEquiv (L ⊔ (T : Subgroup G)) D.space).trans
    ((MulEquiv.subgroupCongr (show ReducedNormal.subspaceImage
      (L ⊔ (T : Subgroup G)) D.space = V from D.image_eq)).toAdditive.toLinearEquiv
        (ZMod.map_smul _))

omit [Finite G] in
private theorem seedCoordinates_apply [IsElementaryAbelian 2 V] (v : D.space) :
    ((seedCoordinates D v).toMul : G) = v.val.toMul.val := rfl

omit [Finite G] in
private theorem seedCoordinates_action [IsElementaryAbelian 2 V] (l : L) (v : D.space) :
    seedCoordinates D (D.seedRepresentation (D.componentHom l) v) =
      doubledSeedAction L V D.normalizes l (seedCoordinates D v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((seedCoordinates D (D.seedRepresentation (D.componentHom l) v)).toMul : G) =
    (l : G) * ((seedCoordinates D v).toMul : G) * (l : G)⁻¹
  exact (seedCoordinates_apply D (D.seedRepresentation (D.componentHom l) v)).trans
    (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹) (seedCoordinates_apply D v).symm)

private theorem seed_linear_marking [IsElementaryAbelian 2 V]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (m : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural BinaryField.two n)) :
    ∃ q : L →* LinearGroup n, Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ e : Additive V ≃ₗ[ZMod 2] Space n,
      ∀ l v, e (doubledSeedAction L V D.normalizes l v) = q l (e v) := by
  let f := m.groupEquiv.trans (slEquivLinear n)
  let q := f.toMonoidHom.comp D.componentHom
  have hq : Function.Surjective q := f.surjective.comp D.componentHom_surjective
  let : Nontrivial (LinearGroup n) := f.symm.toEquiv.nontrivial
  have hz : center (LinearGroup n) = ⊥ := by
    apply bot_unique
    intro z hz
    have hc : (slEquivLinear n).symm z ∈ center
        (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
      apply mem_center_iff.mpr
      intro g
      apply (slEquivLinear n).injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        mem_center_iff.mp hz ((slEquivLinear n) g)
    rw [binary_center_eq_bot (by omega), mem_bot] at hc
    exact (slEquivLinear n).symm.injective (hc.trans (map_one (slEquivLinear n).symm).symm)
  let : q.ker.Characteristic := quotient_center_kernel D h f hz
  let e := (seedCoordinates D).symm.trans m.linearEquiv
  let ρ := doubledSeedAction L V D.normalizes
  have he : ∀ l v, e (ρ l v) = q l (e v) := by
    intro l v
    obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
    rw [← seedCoordinates_action D]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact m.intertwines (D.componentHom l) w
  exact ⟨q,hq,inferInstance,e,he⟩

omit [Finite G] in
private theorem orbitFF_of_pair [IsElementaryAbelian 2 V]
    (τ : Representation (ZMod 2) L (Additive V × Additive V))
    (c : (Additive V × Additive V) ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hc : ∀ l v, c (τ l v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (c v))
    (hp : IsFFModule (imageRepresentation τ)) :
    IsFFModule D.sourceOrbitNormalizerRepresentation := by
  let σ := D.orbitRepresentation.comp D.orbitComponent.subtype
  let E := c.trans D.sourceOrbitCoordinates.symm
  have hE : ∀ l v, σ (D.orbitComponentHom l) (E v) =
      E (τ l v) := by
    intro l v
    apply D.sourceOrbitCoordinates.injective
    have haction (w : D.orbitSpace) :
        D.sourceOrbitCoordinates (σ (D.orbitComponentHom l) w) =
        doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l
          (D.sourceOrbitCoordinates w) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (D.sourceOrbitCoordinates_apply
        (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
          (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
            (D.sourceOrbitCoordinates_apply w).symm)
    rw [haction]
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    exact (hc l v).symm
  exact imageFF_of_surjective _ σ D.orbitComponentHom D.orbitComponentHom_surjective E hE hp

/-- The binary natural four- and five-space constituents force FF on the
literal whole-orbit normalizer. No pair marking is added as a hypothesis. -/
theorem sourceOrbit_isFF_of_markedDoubled_binaryNatural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural BinaryField.two n))) :
    IsFFModule D.sourceOrbitNormalizerRepresentation := by
  let := D.elementary
  let m := hmodel.some
  have hmark := @seed_linear_marking G _ _ T L V D D.elementary h n hn m
  let q := hmark.choose
  have hq : Function.Surjective q := hmark.choose_spec.1
  let : q.ker.Characteristic := hmark.choose_spec.2.1
  let e := hmark.choose_spec.2.2.choose
  have he : ∀ l v, e (doubledSeedAction L V D.normalizes l v) = q l (e v) :=
    hmark.choose_spec.2.2.choose_spec
  let ρ := doubledSeedAction L V D.normalizes
  have hcoords := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let t := hcoords.choose
  have ht : t ∈ (T : Subgroup G) := hcoords.choose_spec.choose
  have hpair := hcoords.choose_spec.choose_spec
  have hne := hpair.2.1
  let c := hpair.2.2.choose
  have hc := hpair.2.2.choose_spec.2
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  have haut := descend_twist q hq α
  let a := haut.choose
  have ha := haut.choose_spec
  have hp := doubledFF_pair_image hn ρ q hq e he α a ha hne
  exact orbitFF_of_pair D (ρ.prod (ρ.comp α.toMonoidHom)) c hc hp

/-- The actual non-FF chosen-module branch excludes both binary natural pairs. -/
theorem sourceOrbit_false_of_markedDoubled_binaryNatural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural BinaryField.two n))) : False :=
  hnon (D.sourceOrbit_isFF_of_markedDoubled_binaryNatural h hd hn hmodel)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
