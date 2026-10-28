module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFrattiniGeometry
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction

/-!
# The native M22 four-space on a literal active chief section

The moved quintet has explicit natural SL₂(4) coordinates. A chief interval
containing its literal seed and missing it in the denominator receives an
injective projection. A nontrivial commuting displacement confined to this
seed fills the projection, so it has dimension four and the original natural
action. Every normalizer of the seed preserves this exact displacement.

The internal imports share the native moved-space implementation without
exposing its private coordinate maps. Source: Aschbacher--Smith 8.2.9,
printed p.721, refs/quasithin.pdf, with the native H.14.3/H.16.3 quintet.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement MonoidAlgebra MatrixGroups
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
open M22ChapterH.Quintet
set_option backward.isDefEq.respectTransparency false

private def movedInnerCoordinates : Additive A0 ≃ₗ[ZMod 2] fiveMoved.toSubmodule :=
  (LinearEquiv.ofInjective innerInclusion innerInclusion_injective).trans
    (LinearEquiv.ofEq _ _ fiveMoved_eq_inner.symm)

@[expose] def fiveMovedSL2Marking : alternatingGroup (Fin 5) ≃* SL(2,GaloisField 2 2) :=
  (MulEquiv.subgroupCongr naturalFivePart_eq.symm).trans
    (naturalFivePartModelEquiv.trans SL2FourNatural.standardGroupEquiv)

def fiveMovedNaturalCoordinates :
    fiveMoved.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
  movedInnerCoordinates.symm.trans innerCoreStandardEquiv

private theorem fiveMovedSL2Marking_lift (a : alternatingGroup (Fin 5))
    (g : naturalActor) (hg : NaturalQuotient.q g.val = a.val) :
    fiveMovedSL2Marking a = naturalActorStandardEquiv (QuotientGroup.mk g) := by
  have hf : (MulEquiv.subgroupCongr naturalFivePart_eq.symm) a =
      naturalActorFivePartEquiv (QuotientGroup.mk g) := by
    apply Subtype.ext
    exact hg.symm
  change SL2FourNatural.standardGroupEquiv
    (naturalFivePartModelEquiv ((MulEquiv.subgroupCongr naturalFivePart_eq.symm) a)) = _
  rw [hf]
  change SL2FourNatural.standardGroupEquiv (naturalActorModelEquiv
    (naturalActorFivePartEquiv.symm (naturalActorFivePartEquiv (QuotientGroup.mk g)))) = _
  rw [naturalActorFivePartEquiv.symm_apply_apply]
  rfl

private theorem movedInnerCoordinates_equivariant (a : alternatingGroup (Fin 5))
    (g : naturalActor) (hg : NaturalQuotient.q g.val = a.val) (u : Additive A0) :
    fiveMoved.toRepresentation a (movedInnerCoordinates u) =
      movedInnerCoordinates (innerConjugation innerInputs g.val u) := by
  apply Subtype.ext
  change kernelS5Conjugation a.val (innerInclusion u) =
    innerInclusion (innerConjugation innerInputs g.val u)
  rw [←hg,kernelS5Conjugation_q,innerInclusion_equivariant]

private theorem fiveMovedNaturalCoordinates_apply_inner (u : Additive A0) :
    fiveMovedNaturalCoordinates (movedInnerCoordinates u) = innerCoreStandardEquiv u := by
  change innerCoreStandardEquiv (movedInnerCoordinates.symm (movedInnerCoordinates u)) = _
  rw [movedInnerCoordinates.symm_apply_apply]

theorem fiveMovedNaturalCoordinates_equivariant (a : alternatingGroup (Fin 5))
    (v : fiveMoved.toSubmodule) :
    fiveMovedNaturalCoordinates (fiveMoved.toRepresentation a v) =
      specialLinearNatural 2 (fiveMovedSL2Marking a) (fiveMovedNaturalCoordinates v) := by
  obtain ⟨g,hg⟩ := fivePart_lift a
  obtain ⟨u,rfl⟩ := movedInnerCoordinates.surjective v
  rw [movedInnerCoordinates_equivariant a g hg,
    fiveMovedNaturalCoordinates_apply_inner,fiveMovedNaturalCoordinates_apply_inner,
    fiveMovedSL2Marking_lift a g hg]
  exact innerCore_standard_natural g u

private theorem marked_chief_projection
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (j : X →* A) (hji : Function.Injective j) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (K C : NormalNode A) [IsElementaryAbelian 2 (Section K C)]
    (hWC : W ≤ C.val) (hWK : W ⊓ K.val = ⊥) :
    ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (Section K C),
      Function.Injective c ∧ Module.finrank (ZMod 2) c.range = 4 ∧
      (∀ x (v w : Coinvariants.ker σ), (w : Additive X) = σ x v →
        c w = binarySectionRepresentation K C (a x) (c v)) ∧
      (∀ v, ∃ b : C.val, (b : A) = j v.val.toMul ∧
        c v = Additive.ofMul (QuotientGroup.mk' (K.val.subgroupOf C.val) b)) := by
  let q := QuotientGroup.mk' (K.val.subgroupOf C.val)
  have hvW (v : Coinvariants.ker σ) : j v.val.toMul ∈ W := hW.le ⟨v.val.toMul,v.property,rfl⟩
  let b (v : Coinvariants.ker σ) : C.val := ⟨j v.val.toMul,hWC (hvW v)⟩
  let l : Coinvariants.ker σ →+ Additive (Section K C) := {
    toFun v := Additive.ofMul (q (b v))
    map_zero' := by
      change q (b 0) = 1
      have hb : b 0 = 1 := Subtype.ext j.map_one
      rw [hb,map_one]
    map_add' v w := by
      change q (b (v+w)) = q (b v) * q (b w)
      rw [←map_mul]
      congr 1
      exact Subtype.ext (j.map_mul _ _) }
  let c := l.toZModLinearMap 2
  have hci : Function.Injective c := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change c v = 0 at hv
    have hq : q (b v) = 1 := congrArg Additive.toMul hv
    have hvK : j v.val.toMul ∈ K.val := (QuotientGroup.eq_one_iff (b v)).mp hq
    have hj1 : j v.val.toMul = 1 := hWK.le ⟨hvW v,hvK⟩
    have hv1 : v.val.toMul = 1 := hji (hj1.trans j.map_one.symm)
    change v = 0
    apply Subtype.ext
    exact congrArg Additive.ofMul hv1
  obtain ⟨eS,_⟩ := moved_equiv_of_marking σ r hrs e he
  have hd : Module.finrank (ZMod 2) (Coinvariants.ker σ) = 4 :=
    eS.finrank_eq.trans fiveAction_moved_dim
  refine ⟨c,hci,(LinearMap.finrank_range_of_inj hci).trans hd,?_,fun v => ⟨b v,rfl,rfl⟩⟩
  intro x v w hw
  change q (b w) = NoncentralChiefRefinement.sectionAction K C (a x) (q (b v))
  rw [NoncentralChiefRefinement.sectionAction_mk]
  congr 1
  apply Subtype.ext
  change j w.val.toMul = a x * j v.val.toMul * (a x)⁻¹
  rw [hw]
  exact hjσ x v.val.toMul

private theorem marked_chief_displacement
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (j : X →* A) (hji : Function.Injective j) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (K C : NormalNode A) [IsElementaryAbelian 2 (Section K C)]
    (hWC : W ≤ C.val) (hWK : W ⊓ K.val = ⊥)
    (y : A) (hny : binarySectionRepresentation K C y ≠ 1)
    (hcomm : ∀ x, Commute (binarySectionRepresentation K C y)
      (binarySectionRepresentation K C (a x)))
    (hmove : ⁅C.val,zpowers y⁆ ≤ W) :
    let ρ := binarySectionRepresentation K C
    ∃ c : Coinvariants.ker σ →ₗ[ZMod 2] Additive (Section K C),
      Function.Injective c ∧ c.range = LinearMap.range (ρ y - 1) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) = 4 ∧
      (∀ x (v w : Coinvariants.ker σ), (w : Additive X) = σ x v → c w = ρ (a x) (c v)) ∧
      (∀ v, ∃ b : C.val, (b : A) = j v.val.toMul ∧
        c v = Additive.ofMul (QuotientGroup.mk' (K.val.subgroupOf C.val) b)) := by
  let ρ := binarySectionRepresentation K C
  let q := QuotientGroup.mk' (K.val.subgroupOf C.val)
  obtain ⟨c,hci,hcd,hc,hcq⟩ := marked_chief_projection σ r hrs e he j hji a hjσ W hW K C hWC hWK
  let S : Subrepresentation (ρ.comp a) := {
    toSubmodule := c.range
    apply_mem_toSubmodule x v hv := by
      obtain ⟨w,rfl⟩ := hv
      have hw : σ x w ∈ Coinvariants.ker σ := by
        simpa only [sub_add_cancel] using
          (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker x w.val) w.property
      exact ⟨⟨σ x w,hw⟩,hc x w ⟨σ x w,hw⟩ rfl⟩ }
  have hi : IsIrreducible S.toRepresentation :=
    marked_moved_range_irreducible σ r hrs e he (ρ.comp a) (MonoidHom.id R)
      Function.surjective_id c hci hc S rfl
  let D : Subrepresentation (ρ.comp a) := {
    toSubmodule := LinearMap.range (ρ y - 1)
    apply_mem_toSubmodule x v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨ρ (a x) w,?_⟩
      change ρ y (ρ (a x) w) - ρ (a x) w = ρ (a x) (ρ y w-w)
      rw [map_sub]
      exact congrArg (fun z => z-ρ (a x) w) (LinearMap.congr_fun (hcomm x).eq w) }
  have hDS : D ≤ S := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (K.val.subgroupOf C.val) z.toMul
    have hmv := hmove
    rw [commutator_comm] at hmv
    have hw := hmv (commutator_mem_commutator (mem_zpowers y) b.property)
    obtain ⟨x,hx,hxw⟩ := hW.ge hw
    let v : Coinvariants.ker σ := ⟨Additive.ofMul x,hx⟩
    refine ⟨v,?_⟩
    obtain ⟨d,hd,hdq⟩ := hcq v
    rw [hdq]
    have hz : z = Additive.ofMul (q b) := congrArg Additive.ofMul hb.symm
    rw [hz]
    apply Additive.toMul.injective
    change q d = NoncentralChiefRefinement.sectionAction K C y (q b) / q b
    rw [NoncentralChiefRefinement.sectionAction_mk,←map_div]
    congr 1
    apply Subtype.ext
    change (d : A) = y * (b : A) * y⁻¹ / (b : A)
    rw [hd]
    exact hxw.trans (by rw [commutatorElement_def,div_eq_mul_inv])
  have hDn : D ≠ ⊥ := by
    intro hd
    apply hny
    apply sub_eq_zero.mp
    apply LinearMap.range_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule hd
  have hDS' : D = S := by
    exact not_ne_iff.mp (fun hne => hDn
      (((Subrepresentation.irreducible_iff_isAtom S).mp hi).ne_iff_eq_bot hDS |>.mp hne))
  have hrange : c.range = LinearMap.range (ρ y-1) :=
    (congrArg Subrepresentation.toSubmodule hDS').symm
  exact ⟨c,hci,hrange,hrange ▸ hcd,hc,hcq⟩

private theorem natural_coordinates_of_fiveMoved_equiv
    {R Z : Type*} [Group R] [AddCommGroup Z] [Module (ZMod 2) Z]
    (τ : Representation (ZMod 2) R Z) (r : R →* alternatingGroup (Fin 5))
    (ep : fiveMoved.toSubmodule ≃ₗ[ZMod 2] Z)
    (hp : ∀ x u, τ x (ep u) = ep (fiveMoved.toRepresentation (r x) u)) :
    ∃ eN : Z ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      ∀ x v, eN (τ x v) =
        specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (eN v) := by
  refine ⟨ep.symm.trans fiveMovedNaturalCoordinates,?_⟩
  intro x v
  obtain ⟨u,rfl⟩ := ep.surjective v
  rw [hp]
  change fiveMovedNaturalCoordinates (ep.symm (ep (fiveMoved.toRepresentation (r x) u))) =
    specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (fiveMovedNaturalCoordinates (ep.symm (ep u)))
  rw [ep.symm_apply_apply,ep.symm_apply_apply]
  exact fiveMovedNaturalCoordinates_equivariant (r x) u

private theorem marked_moved_range_natural
    {R X Z : Type*} [Group R] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    (σ : Representation (ZMod 2) R X)
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (τ : Representation (ZMod 2) R Z)
    (c : Coinvariants.ker σ →ₗ[ZMod 2] Z) (hci : Function.Injective c)
    (hc : ∀ x (v w : Coinvariants.ker σ), (w : X) = σ x v → c w = τ x (c v))
    (S : Subrepresentation τ) (hS : S.toSubmodule = c.range) :
    ∃ eN : S.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      ∀ x v, eN (S.toRepresentation x v) =
        specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (eN v) := by
  obtain ⟨eS,heS⟩ := moved_equiv_of_marking σ r hrs e he
  have hes (v : fiveMoved.toSubmodule) : e (eS.symm v) = (v : Additive MathieuCode.M22Quintet.K) := by
    rw [←heS,eS.apply_symm_apply]
  let p : fiveMoved.toSubmodule →ₗ[ZMod 2] S.toSubmodule :=
    (c.comp eS.symm.toLinearMap).codRestrict S.toSubmodule (fun v => by
      rw [hS]; exact ⟨eS.symm v,rfl⟩)
  have hpi : Function.Injective p := by
    intro v w h
    exact eS.symm.injective (hci (congrArg Subtype.val h))
  have hps : Function.Surjective p := by
    intro w
    obtain ⟨v,hv⟩ := hS.le w.property
    refine ⟨eS v,?_⟩
    apply Subtype.ext
    change c (eS.symm (eS v)) = w.val
    rw [eS.symm_apply_apply,hv]
  let ep := LinearEquiv.ofBijective p ⟨hpi,hps⟩
  have hp (x : R) (u : fiveMoved.toSubmodule) :
      S.toRepresentation x (ep u) = ep (fiveMoved.toRepresentation (r x) u) := by
    apply Subtype.ext
    change τ x (c (eS.symm u)) = c (eS.symm (fiveMoved.toRepresentation (r x) u))
    symm
    apply hc x
    apply e.injective
    rw [he,hes,hes]
    rfl
  exact natural_coordinates_of_fiveMoved_equiv S.toRepresentation r ep hp

/-- A literal involution displacement is the original natural four-space,
with an irreducible residual action and explicit field-four coordinates. -/
@[expose] def M22NaturalChiefDisplacement
    {A R Z : Type*} [Group A] [Group R] [AddCommGroup Z] [Module (ZMod 2) Z]
    (ρ : Representation (ZMod 2) A Z) (a : R →* A)
    (r : R →* alternatingGroup (Fin 5)) (y : A) : Prop :=
  ∃ S : Subrepresentation (ρ.comp a),
    IsIrreducible S.toRepresentation ∧ S.toSubmodule = LinearMap.range (ρ y - 1) ∧
    Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) = 4 ∧
    ∃ eN : S.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      ∀ x v, eN (S.toRepresentation x v) =
        specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (eN v)

/-- The actual displacement is preserved by every normalizer of its literal seed. -/
@[expose] def M22ChiefDisplacementStable
    {A Z : Type*} [Group A] [AddCommGroup Z] [Module (ZMod 2) Z]
    (ρ : Representation (ZMod 2) A Z) (y : A) (W : Subgroup A) : Prop :=
  ∀ z ∈ normalizer (W : Set A),
    (LinearMap.range (ρ y - 1)).map (ρ z) = LinearMap.range (ρ y - 1)

private theorem chief_projection_range_stable
    {A X : Type*} [Group A] [Group X] [IsElementaryAbelian 2 X]
    (j : X →* A) (M : Submodule (ZMod 2) (Additive X)) (W : Subgroup A)
    (hW : M.toAddSubgroup.toSubgroup'.map j = W)
    (K C : NormalNode A) [IsElementaryAbelian 2 (Section K C)]
    (c : M →ₗ[ZMod 2] Additive (Section K C))
    (hcq : ∀ v, ∃ b : C.val, (b : A) = j v.val.toMul ∧
      c v = Additive.ofMul (QuotientGroup.mk' (K.val.subgroupOf C.val) b)) :
    ∀ z ∈ normalizer (W : Set A),
      c.range.map (binarySectionRepresentation K C z) = c.range := by
  let ρ := binarySectionRepresentation K C
  let q := QuotientGroup.mk' (K.val.subgroupOf C.val)
  have hstable (z : A) (hz : z ∈ normalizer (W : Set A))
      (w : Additive (Section K C)) (hw : w ∈ c.range) : ρ z w ∈ c.range := by
    obtain ⟨v,rfl⟩ := hw
    obtain ⟨b,hb,hcqv⟩ := hcq v
    have hbW : (b : A) ∈ W := hb ▸ hW.le ⟨v.val.toMul,v.property,rfl⟩
    have hzb : z * (b : A) * z⁻¹ ∈ W := (mem_normalizer_iff.mp hz (b : A)).mp hbW
    obtain ⟨u,hu,huj⟩ := hW.ge hzb
    let u' : M := ⟨Additive.ofMul u,hu⟩
    obtain ⟨d,hd,hcqu⟩ := hcq u'
    refine ⟨u',?_⟩
    rw [hcqv,hcqu]
    apply Additive.toMul.injective
    change q d = NoncentralChiefRefinement.sectionAction K C z (q b)
    rw [NoncentralChiefRefinement.sectionAction_mk]
    congr 1
    apply Subtype.ext
    exact hd.trans huj
  intro z hz
  apply le_antisymm
  · rintro _ ⟨w,hw,rfl⟩
    exact hstable z hz w hw
  · intro w hw
    exact ⟨ρ z⁻¹ w,hstable z⁻¹ ((normalizer (W : Set A)).inv_mem hz) w hw,
      ρ.self_inv_apply z w⟩

theorem marked_chief_natural_displacement
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (j : X →* A) (hji : Function.Injective j) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (K C : NormalNode A) [IsElementaryAbelian 2 (Section K C)]
    (hWC : W ≤ C.val) (hWK : W ⊓ K.val = ⊥)
    (y : A) (hny : binarySectionRepresentation K C y ≠ 1)
    (hcomm : ∀ x, Commute (binarySectionRepresentation K C y)
      (binarySectionRepresentation K C (a x)))
    (hmove : ⁅C.val,zpowers y⁆ ≤ W) :
    M22NaturalChiefDisplacement (binarySectionRepresentation K C) a r y ∧
      M22ChiefDisplacementStable (binarySectionRepresentation K C) y W := by
  let ρ := binarySectionRepresentation K C
  obtain ⟨c,hci,hcr,hcd,hc,hcq⟩ := marked_chief_displacement
    σ r hrs e he j hji a hjσ W hW K C hWC hWK y hny hcomm hmove
  let S : Subrepresentation (ρ.comp a) := {
    toSubmodule := c.range
    apply_mem_toSubmodule x v hv := by
      obtain ⟨w,rfl⟩ := hv
      have hw : σ x w ∈ Coinvariants.ker σ := by
        simpa only [sub_add_cancel] using
          (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker x w.val) w.property
      exact ⟨⟨σ x w,hw⟩,hc x w ⟨σ x w,hw⟩ rfl⟩ }
  have hi : IsIrreducible S.toRepresentation :=
    marked_moved_range_irreducible σ r hrs e he (ρ.comp a) (MonoidHom.id R)
      Function.surjective_id c hci hc S rfl
  refine ⟨⟨S,hi,hcr,hcd,marked_moved_range_natural σ r hrs e he (ρ.comp a) c hci hc S rfl⟩,?_⟩
  unfold M22ChiefDisplacementStable
  rw [←hcr]
  exact chief_projection_range_stable j (Coinvariants.ker σ) W hW K C c hcq

end MathieuCode.NormalizedShadowRows.M22CodeSection
