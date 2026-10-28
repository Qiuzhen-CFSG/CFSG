module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases.Linear

/-!
# The doubled reciprocal action equals the actual conjugated R₂ action

Move the original flag plane to the common reciprocal axis using an element
l of the original component L. The full-shear calculation identifies the
marked W image with the conjugated original R₂ image. Faithful coordinates
then give equality under the literal normalizer homomorphism on A, while
the same g*l carries V₂ onto [A,W]. The ambient actor is exactly R₂^(g*l),
so the correction is g*l*g⁻¹ in L^g; the originally selected g is preserved.

The preceding R₂ field-action and full-shear image are explicit inputs from
qt-d-1222-natural-flag-cartan. They involve only the original flag radical,
not W or the desired comparison. The final owner qt-d-1222-shadow-common-action
discharges them and the preceding natural/fixed-space inputs. The source
application below derives normalization from the source corank alternative.
Source: Aschbacher--Smith 11.3.7(4), case (ii), refs/quasithin.pdf, p.773.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] {V : Subgroup G}

def conjugateNormalizerHom (g : G) :
    normalizer (V : Set G) →* normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
  ((MulAut.conj g).toMonoidHom.comp (normalizer (V : Set G)).subtype).codRestrict _
    (fun v => V.le_normalizer_map (MulAut.conj g).toMonoidHom
      (mem_map_of_mem _ v.property))

def adjustedNormalizerHom (B : Subgroup G) (hBV : B ≤ normalizer (V : Set G))
    (g : G) (l : normalizer (V : Set G)) :
    B →* normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
  (conjugateNormalizerHom g).comp ((MulAut.conj l).toMonoidHom.comp (inclusion hBV))

theorem adjustedNormalizerHom_val (B : Subgroup G) (hBV : B ≤ normalizer (V : Set G))
    (g : G) (l : normalizer (V : Set G)) (b : B) :
    (adjustedNormalizerHom B hBV g l b : G) = (MulAut.conj (g * (l : G))) (b : G) := by
  change g * ((l : G) * (b : G) * (l : G)⁻¹) * g⁻¹ =
    (g * (l : G)) * (b : G) * (g * (l : G))⁻¹
  group

/-- The adjusted actor's ambient image is exactly the conjugate of the
original subgroup by g*l; no intersection or substitute actor is introduced. -/
theorem adjustedNormalizerHom_range (B : Subgroup G) (hBV : B ≤ normalizer (V : Set G))
    (g : G) (l : normalizer (V : Set G)) :
    (adjustedNormalizerHom B hBV g l).range.map
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).subtype =
      B.map (MulAut.conj (g * (l : G))).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨t,⟨b,rfl⟩,rfl⟩
    exact ⟨b,b.property,(adjustedNormalizerHom_val B hBV g l b).symm⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨adjustedNormalizerHom B hBV g l ⟨b,hb⟩,⟨⟨b,hb⟩,rfl⟩,
      adjustedNormalizerHom_val B hBV g l ⟨b,hb⟩⟩

private theorem marked_ranges_eq {A B C E : Type*} [Group A] [Group B] [Group C]
    [AddCommGroup E] {F : Type*} [Field F] [Module F E]
    (e : A ≃* Multiplicative E)
    (ρ : B →* MulAut A) (τ : C →* MulAut A)
    (α : B →* (E ≃ₗ[F] E)) (β : C →* (E ≃ₗ[F] E))
    (hα : ∀ b v, (e (ρ b v)).toAdd = α b (e v).toAdd)
    (hβ : ∀ c v, (e (τ c v)).toAdd = β c (e v).toAdd)
    (he : α.range = β.range) : ρ.range = τ.range := by
  apply le_antisymm
  · rintro _ ⟨b,rfl⟩
    obtain ⟨c,hc⟩ := he ▸ (show α b ∈ α.range from ⟨b,rfl⟩)
    refine ⟨c,?_⟩
    ext v
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hβ,hα,hc]
  · rintro _ ⟨c,rfl⟩
    obtain ⟨b,hb⟩ := he.symm ▸ (show β c ∈ β.range from ⟨c,rfl⟩)
    refine ⟨b,?_⟩
    ext v
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hβ,hα,hb]
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem conjugateCoordinates_mem (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (U : Submodule S.field.Carrier c.Space) (v : V.map (MulAut.conj g).toMonoidHom) :
    (v : G) ∈ (c.preimage U).map (MulAut.conj g).toMonoidHom ↔
      ((conjugateCoordinates c hfixed g) v).toAdd ∈ U := by
  let e := V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨u,rfl⟩ := e.surjective v
  change (MulAut.conj g) (u : G) ∈ (c.preimage U).map (MulAut.conj g).toMonoidHom ↔
    (c.projection (e.symm (e u))).toAdd ∈ U
  rw [Subgroup.mem_map_equiv,MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply]
  exact c.mem_preimage U u

private theorem conjugateCoordinates_normalizer (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (t : normalizer (V : Set G)) (v : V.map (MulAut.conj g).toMonoidHom) :
    ((conjugateCoordinates c hfixed g)
      ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom (conjugateNormalizerHom g t) v)).toAdd =
    c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl t
      ((conjugateCoordinates c hfixed g) v).toAdd := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let e : V ≃* A := V.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  change (c.projection (e.symm (A.normalizerMonoidHom (conjugateNormalizerHom g t) v))).toAdd =
    c.conjugationAction _ _ t (c.projection (e.symm v)).toAdd
  rw [c.conjugationAction_projection]
  congr 2
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  rw [coe_equivMapOfInjective_apply]
  change (g * (t : G) * g⁻¹) * (v : G) * (g * (t : G) * g⁻¹)⁻¹ =
    g * ((t : G) * (e.symm v : G) * (t : G)⁻¹) * g⁻¹
  have hv : g * (e.symm v : G) * g⁻¹ = (v : G) := congrArg Subtype.val (e.apply_symm_apply v)
  rw [←hv]
  group

private theorem component_action (c : Coordinates D S.field) (l : L) (v : c.Space) :
    c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl
      (inclusion D.normalizes l) v = c.modelAction (c.quotientMap l) v := by
  obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  rw [←show (c.projection u).toAdd=v from congrArg Multiplicative.toAdd hu,
    c.conjugationAction_projection]
  exact c.projection_component_conjugation l u

private theorem adjusted_intertwines
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) (l : L)
    (β : f.Ri 1 →* (c.Space ≃ₗ[S.field.Carrier] c.Space))
    (hβ : ∀ r v, β r v = c.sylowAction S (inclusion (localRadical_le_sylow _) r) v)
    (r : f.Ri 1) (v : V.map (MulAut.conj g).toMonoidHom) :
    ((conjugateCoordinates c hfixed g)
      ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom
        (adjustedNormalizerHom (f.Ri 1)
          ((localRadical_le_sylow _).trans S.sylow_normalizes) g (inclusion D.normalizes l) r) v)).toAdd =
      ((MulAut.conj (c.modelLinearEquiv (c.quotientMap l))) (β r))
        ((conjugateCoordinates c hfixed g) v).toAdd := by
  rw [show adjustedNormalizerHom (f.Ri 1) _ g (inclusion D.normalizes l) r =
    conjugateNormalizerHom g ((inclusion D.normalizes l) *
      inclusion ((localRadical_le_sylow _).trans S.sylow_normalizes) r *
        (inclusion D.normalizes l)⁻¹) from rfl,
    conjugateCoordinates_normalizer]
  rw [map_mul,map_mul]
  change c.conjugationAction _ _ (inclusion D.normalizes l)
    (c.conjugationAction _ _ (inclusion ((localRadical_le_sylow _).trans S.sylow_normalizes) r)
      (c.conjugationAction _ _ (inclusion D.normalizes l⁻¹)
        ((conjugateCoordinates c hfixed g) v).toAdd)) = _
  rw [component_action,component_action]
  have hr (r : f.Ri 1) (x : c.Space) :
      c.conjugationAction (WeakClosure.seed_normalizer_le D S) le_rfl
        (inclusion ((localRadical_le_sylow _).trans S.sylow_normalizes) r) x =
      c.sylowAction S (inclusion (localRadical_le_sylow _) r) x := by
    obtain ⟨u,hu⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    rw [←show (c.projection u).toAdd=x from congrArg Multiplicative.toAdd hu,
      c.conjugationAction_projection]
    change _ = c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes
      (inclusion (localRadical_le_sylow _) r) (c.projection u).toAdd
    rw [c.conjugationAction_projection]
    rfl
  rw [hr]
  change c.modelAction (c.quotientMap l)
    (c.sylowAction S (inclusion (localRadical_le_sylow _) r)
      (c.modelAction (c.quotientMap l⁻¹) ((conjugateCoordinates c hfixed g) v).toAdd)) = _
  rw [←hβ,map_inv]
  rfl

/-- The original doubled action equals the conjugated original R₂ action,
with the same adjustment carrying V₂ onto the literal full commutator. The
sole R₂ input is the preceding flag-radical shear-image theorem, produced by
qt-d-1222-natural-flag-cartan and discharged by qt-d-1222-shadow-common-action. -/
theorem source_sl3_doubled_action
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (β : f.Ri 1 →* ((Fin 3 → S.field.Carrier) ≃ₗ[S.field.Carrier] (Fin 3 → S.field.Carrier)))
    (hβ : ∀ r v, β r v = (Coordinates.sl3 a).sylowAction S
      (inclusion (localRadical_le_sylow _) r) v)
    (hβrange : β.range = Shear.group (f.space 1)) :
    ∃ l : L,
      (f.Vi 1).map (MulAut.conj (g * (l : G))).toMonoidHom =
        ⁅V.map (MulAut.conj g).toMonoidHom,omegaClosure T H⁆ ∧
      ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom.comp (inclusion hN)).range =
        ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom.comp
          (adjustedNormalizerHom (f.Ri 1)
            ((localRadical_le_sylow _).trans S.sylow_normalizes) g (inclusion D.normalizes l))).range := by
  let c := Coordinates.sl3 a
  let A := V.map (MulAut.conj g).toMonoidHom
  let α := sl3LinearReciprocal a f g n hN
  let e := conjugateCoordinates c hfixed g
  have hact : ∀ w v, (e (A.normalizerMonoidHom (inclusion hN w) v)).toAdd =
      α w (e v).toAdd := conjugateCoordinates_intertwines c hfixed g hN
  obtain ⟨hd,hfull⟩ := full_shears n e hN α hact
  obtain ⟨z,hz⟩ := sl3_plane_orbit (f.space 1) (commonAxis α) (f.dimension 1) hd
  obtain ⟨l,hl⟩ := c.quotientMap_surjective z
  let z' := c.modelLinearEquiv (c.quotientMap l)
  have hz' : (f.space 1).map z'.toLinearMap = commonAxis α := by
    change (f.space 1).map (c.modelAction (c.quotientMap l)) = _
    rw [hl]
    exact hz
  have haxis : (c.preimage (commonAxis α)).map (MulAut.conj g).toMonoidHom =
      A ⊓ centralizer (omegaClosure T H : Set G) := by
    apply le_antisymm
    · intro v hv
      have hvA : v ∈ A := map_mono (D.centralQuotientPreimage_le _) hv
      refine ⟨hvA,?_⟩
      exact (mem_axis_iff e hN α hact ⟨v,hvA⟩).mp
        ((conjugateCoordinates_mem c hfixed g _ ⟨v,hvA⟩).mp hv)
    · rintro v ⟨hvA,hv⟩
      exact (conjugateCoordinates_mem c hfixed g _ ⟨v,hvA⟩).mpr
        ((mem_axis_iff e hN α hact ⟨v,hvA⟩).mpr hv)
  refine ⟨l,?_,?_⟩
  · rw [←CFSG.Quasithin.ChapterE.offender_map_conj_map]
    change ((c.preimage (f.space 1)).map (MulAut.conj (l : G)).toMonoidHom).map _ = _
    rw [←c.preimage_map_action]
    change (c.preimage ((f.space 1).map z'.toLinearMap)).map _ = _
    rw [hz',haxis,source_sl3_doubled_commutator_eq_axis a hfixed g n hN]
  · let β' := (MulAut.conj z').toMonoidHom.comp β
    have himage : α.range = β'.range := by
      rw [MonoidHom.range_comp,hβrange,Shear.conj,hz',hfull]
    exact marked_ranges_eq e _ _ α β' hact
      (adjusted_intertwines c f hfixed g l β hβ) himage
/-- Source corank control supplies normalization in the doubled comparison.
Only the preceding natural, fixed-space, and original R₂-image inputs remain. -/
theorem source_sl3_doubled_action_of_parameters
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a))
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}
    (s : Hypothesis1131At D S U₁ H)
    (hline : U₁ = (Coordinates.sl3 a).binarySubspace (f.space 0))
    (hparameters : (S.field.degree : ℕ∞) < CFSG.Quasithin.ChapterE.globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        CFSG.Quasithin.ChapterE.globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field 2)
    (β : f.Ri 1 →* ((Fin 3 → S.field.Carrier) ≃ₗ[S.field.Carrier] (Fin 3 → S.field.Carrier)))
    (hβ : ∀ r v, β r v = (Coordinates.sl3 a).sylowAction S
      (inclusion (localRadical_le_sylow _) r) v)
    (hβrange : β.range = Shear.group (f.space 1)) :
    ∃ hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G),
    ∃ l : L,
      (f.Vi 1).map (MulAut.conj (g * (l : G))).toMonoidHom =
        ⁅V.map (MulAut.conj g).toMonoidHom,omegaClosure T H⁆ ∧
      ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom.comp (inclusion hN)).range =
        ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom.comp
          (adjustedNormalizerHom (f.Ri 1)
            ((localRadical_le_sylow _).trans S.sylow_normalizes) g (inclusion D.normalizes l))).range := by
  let hN := source_normalizes_of_natural_coordinates s (.sl3 a) f hline hparameters g
    (by decide : 0 < 2) n
  exact ⟨hN,source_sl3_doubled_action a f hfixed g n hN β hβ hβrange⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
