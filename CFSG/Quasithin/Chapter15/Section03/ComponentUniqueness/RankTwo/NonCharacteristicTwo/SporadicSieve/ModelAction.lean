module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The faithful action used by the sporadic sieve

The supplied equivalence from L/O₂(L) identifies the actual component image
in I/C_I(L), because the standing setup gives Z(L) = O₂(L). Perfectness of
L makes the centralizer of this image trivial. Conjugation therefore embeds
I/C_I(L) into the full automorphism group of the supplied carrier. Its
restriction to the component is exactly the inner action, and the preimage
of the inner automorphisms is exactly the component image.

When this action is surjective for the fixed ATLAS J₂ carrier, it constructs
both isomorphisms and their compatibility in `JankoTwoIdentification`.
Surjectivity is an explicit remaining premise, not a local classification
assertion. All normality is relative to I or its actual quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3f),
printed p.502, and 15.3.41--42, printed p.1138.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
variable {G : Type*} [Group G] {I L M Yplus S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- The image is normal in the centralizer quotient; no ambient normality of L is used. -/
instance componentImage_normal : (componentImage I L L).Normal :=
  (inferInstance : (L.subgroupOf I).Normal).map
    (centralizerQuotientMap (L.subgroupOf I)) (QuotientGroup.mk'_surjective _)

/-- Perfectness eliminates the centralizer of the component image. -/
theorem componentImage_faithful (d : ComponentSetup I L M Yplus S) :
    centralizer (componentImage I L L : Set (ComponentQuotient I L)) = ⊥ := by
  let : IsQuasisimple L := d.component_quasisimple
  let : IsQuasisimple (L.subgroupOf I) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe d.component_le).symm
  exact centralizerQuotientComponent_centralizer (L.subgroupOf I)

/-- The model marking transported through the actual quotient by the component centralizer. -/
noncomputable def componentModel {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A) :
    componentImage I L L ≃* A :=
  componentImageModelEquiv I L d.component_le
    ((QuotientGroup.quotientMulEquivOfEq d.center_eq).trans e)

/-- Conjugation on the component image, expressed in the supplied model coordinates. -/
noncomputable def modelAction {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A) :
    ComponentQuotient I L →* MulAut A :=
  (MulAut.congr (componentModel d e)).toMonoidHom.comp MulAut.conjNormal

/-- The full quotient acts faithfully on the model. -/
theorem modelAction_injective {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A) :
    Function.Injective (modelAction d e) :=
  (MulAut.congr (componentModel d e)).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _ (componentImage_faithful d))

/-- Compatibility with the component marking is built into the action. -/
theorem modelAction_inner {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A)
    (x : componentImage I L L) :
    modelAction d e x = MulAut.conj (componentModel d e x) := by
  change MulAut.congr (componentModel d e) (MulAut.conjNormal (x : ComponentQuotient I L)) = _
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

/-- The actual component maps onto all inner automorphisms. -/
theorem modelAction_map_component {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A) :
    (componentImage I L L).map (modelAction d e) = MulAut.innerSubgroup A := by
  ext α
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨componentModel d e ⟨x, hx⟩, (modelAction_inner d e ⟨x, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(componentModel d e).symm x, ((componentModel d e).symm x).property, ?_⟩
    rw [modelAction_inner, MulEquiv.apply_symm_apply]

/-- No element outside the actual component image acts by an inner automorphism. -/
theorem modelAction_comap_inner {A : Type*} [Group A]
    (d : ComponentSetup I L M Yplus S) (e : L ⧸ pCore 2 L ≃* A) :
    (MulAut.innerSubgroup A).comap (modelAction d e) = componentImage I L L := by
  rw [← modelAction_map_component d e, Subgroup.comap_map_eq,
    (MonoidHom.ker_eq_bot_iff _).mpr (modelAction_injective d e), sup_bot_eq]

/-- Construct the required compatible identification once the faithful action is onto. -/
noncomputable def identificationOfSurjective
    (d : ComponentSetup I L M Yplus S)
    (e : L ⧸ pCore 2 L ≃* Sporadic.LeechRelated.J2.Carrier)
    (hs : Function.Surjective (modelAction d e)) : JankoTwoIdentification I L where
  equivalence := MulEquiv.ofBijective (modelAction d e) ⟨modelAction_injective d e, hs⟩
  component := componentModel d e
  inner_compatible := modelAction_inner d e

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
