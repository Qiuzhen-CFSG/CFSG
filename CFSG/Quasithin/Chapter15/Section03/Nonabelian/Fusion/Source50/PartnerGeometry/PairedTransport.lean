module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PairedModel
public import Theory.Representation.BinaryPairedTransvections.Order

/-!
# The actual paired actor and its marked center

A faithful action identifies the original partner actor with the full
center transvections. Conjugation by the source summand-exchanging
isometry supplies the full axis transvections. Their join is therefore
the paired extraspecial group. The original image of `V` lies in both
root groups and has order two, so it is exactly the center.

This constructs the actor embedding and its center marking from the
actual action image. It supplies `RecognitionFields.extraspecial_product`
and the order-eight assertion in the smallest source-56 case, without
an additional group classification or center-identification hypothesis.

Source: Aschbacher--Smith, original Lemma 15.3.56(6), printed p. 1148.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition Recognition.NormalReduction BinaryPairedTransvections
variable {G : Type*} [Group G] {Z : Subgroup G}
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private noncomputable def pairEquivOfImage
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E)) (hρ : Function.Injective ρ)
    (c : E) (d : Module.Dual (ZMod 2) E) (P : Subgroup (ActorQuotient Z))
    (hP : P.map ρ = (pairGroup c d).map pairedAction) : pairGroup c d ≃* P :=
  ((pairGroup c d).equivMapOfInjective pairedAction pairedAction_injective).trans
    ((MulEquiv.subgroupCongr hP.symm).trans (P.equivMapOfInjective ρ hρ).symm)

private theorem pairEquivOfImage_apply
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E)) (hρ : Function.Injective ρ)
    (c : E) (d : Module.Dual (ZMod 2) E) (P : Subgroup (ActorQuotient Z))
    (hP : P.map ρ = (pairGroup c d).map pairedAction) (p : pairGroup c d) :
    ρ (pairEquivOfImage ρ hρ c d P hP p) = pairedAction p.val := by
  have he := (P.equivMapOfInjective ρ hρ).apply_symm_apply
    (MulEquiv.subgroupCongr hP.symm ((pairGroup c d).equivMapOfInjective
      pairedAction pairedAction_injective p))
  exact congrArg Subtype.val he

private theorem paired_actor_join_image
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E))
    (X : Subgroup (ActorQuotient Z)) (a : ActorQuotient Z)
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (hX : X.map ρ = (centerGroup c).map pairedAction)
    (hq : ∀ u, BinaryNaturalDual.quadratic (ρ a u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (ρ a (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (ρ a (0,f)).2 = 0)
    (htd : ρ a (0,d) = (c,0)) :
    (X.map (MulAut.conj a⁻¹).toMonoidHom).map ρ = (axisGroup d).map pairedAction ∧
    (X ⊔ X.map (MulAut.conj a⁻¹).toMonoidHom).map ρ = (pairGroup c d).map pairedAction := by
  have hx : (X.map (MulAut.conj a⁻¹).toMonoidHom).map ρ =
      (axisGroup d).map pairedAction := by
    rw [← centerGroup_conjugate_eq_axisGroup c hc d hd (ρ a) hq hE hD htd, ← hX]
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change ρ (a⁻¹ * x * (a⁻¹)⁻¹) = (ρ a)⁻¹ * ρ x * ((ρ a)⁻¹)⁻¹
    simp only [map_mul,map_inv]
  refine ⟨hx, ?_⟩
  rw [Subgroup.map_sup, hx, hX, pairGroup, Subgroup.map_sup]

/-- Faithful paired coordinates identify the actual generated actor with the
paired transvection group, and the original order-two common subgroup with
its marked center. -/
theorem paired_actor_realization
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E)) (hρ : Function.Injective ρ)
    (X : Subgroup (ActorQuotient Z)) (a : ActorQuotient Z) (V : Subgroup G)
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (hX : X.map ρ = (centerGroup c).map pairedAction)
    (hq : ∀ u, BinaryNaturalDual.quadratic (ρ a u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (ρ a (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (ρ a (0,f)).2 = 0)
    (htd : ρ a (0,d) = (c,0))
    (hVX : actorImage Z V ≤ X)
    (hVXt : actorImage Z V ≤ X.map (MulAut.conj a⁻¹).toMonoidHom)
    (hVcard : Nat.card (actorImage Z V) = 2) :
    ∃ f : pairGroup c d →* ActorQuotient Z, Function.Injective f ∧
      zpowers (f (pairedCenter c d hdc)) = actorImage Z V := by
  obtain ⟨hx,hP⟩ := paired_actor_join_image ρ X a c hc d hd hX hq hE hD htd
  let P := X ⊔ X.map (MulAut.conj a⁻¹).toMonoidHom
  let e := pairEquivOfImage ρ hρ c d P hP
  let f : pairGroup c d →* ActorQuotient Z := P.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfe (p : pairGroup c d) : ρ (f p) = pairedAction p.val :=
    pairEquivOfImage_apply ρ hρ c d P hP p
  let C := ((center (pairGroup c d)).map (pairGroup c d).subtype).map pairedAction
  have hCcard : Nat.card C = 2 := by
    rw [card_map_of_injective pairedAction_injective,
      card_map_of_injective (pairGroup c d).subtype_injective]
    exact center_pairGroup_card c hc d hd hdc
  have hVle : (actorImage Z V).map ρ ≤ C := by
    dsimp [C]
    rw [center_pairGroup_eq_inf c hc d hd hdc, Subgroup.map_inf _ _ pairedAction pairedAction_injective]
    exact le_inf (hX ▸ map_mono hVX) (hx ▸ map_mono hVXt)
  have hVC : (actorImage Z V).map ρ = C := by
    let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCcard]; decide)
    apply eq_of_le_of_card_ge hVle
    rw [hCcard,card_map_of_injective hρ,hVcard]
  refine ⟨f,hf,?_⟩
  apply map_injective hρ
  rw [MonoidHom.map_zpowers,hfe,hVC]
  dsimp [C]
  rw [center_pairGroup c hc d hd hdc,MonoidHom.map_zpowers]
  rfl

/-- The literal extraspecial-product recognition field follows from the
faithful action image and the original common actor line of order two. -/
theorem source_paired_extraspecial_product [FiniteDimensional (ZMod 2) E]
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E)) (hρ : Function.Injective ρ)
    (X : Subgroup (ActorQuotient Z)) (a : ActorQuotient Z) (V : Subgroup G)
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (hX : X.map ρ = (centerGroup c).map pairedAction)
    (hq : ∀ u, BinaryNaturalDual.quadratic (ρ a u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (ρ a (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (ρ a (0,f)).2 = 0)
    (htd : ρ a (0,d) = (c,0))
    (hVX : actorImage Z V ≤ X)
    (hVXt : actorImage Z V ≤ X.map (MulAut.conj a⁻¹).toMonoidHom)
    (hVcard : Nat.card (actorImage Z V) = 2)
    (s : ℕ) (hdim : Module.finrank (ZMod 2) E = s+2) :
    0 < s → ∃ P : Subgroup (ActorQuotient Z), IsExtraspecial 2 P ∧
      ∃ W : Subgroup P, IsElementaryAbelian 2 W ∧ Nat.card W = 2^(s+1) ∧
        (center P).map P.subtype = actorImage Z V := by
  obtain ⟨f,hf,hcenter⟩ := paired_actor_realization ρ hρ X a V c hc d hd hdc
    hX hq hE hD htd hVX hVXt hVcard
  exact paired_model_extraspecial_product V c hc d hd hdc s hdim f hf hcenter

/-- The order-eight paired actor required in the source's smallest case. -/
theorem source_paired_actor_pair_card [FiniteDimensional (ZMod 2) E]
    (ρ : ActorQuotient Z →* BinaryLinear.GL (PairedSpace E)) (hρ : Function.Injective ρ)
    (X : Subgroup (ActorQuotient Z)) (a : ActorQuotient Z)
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (hX : X.map ρ = (centerGroup c).map pairedAction)
    (hq : ∀ u, BinaryNaturalDual.quadratic (ρ a u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (ρ a (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (ρ a (0,f)).2 = 0)
    (htd : ρ a (0,d) = (c,0))
    (hdim : Module.finrank (ZMod 2) E = 3) :
    Nat.card ↥(X ⊔ X.map (MulAut.conj a⁻¹).toMonoidHom) = 8 := by
  have hP := (paired_actor_join_image ρ X a c hc d hd hX hq hE hD htd).2
  rw [← Nat.card_congr (pairEquivOfImage ρ hρ c d _ hP).toEquiv]
  exact pairGroup_card_of_exchange c hc d hd hdc (ρ a) hq hE hD htd 1 hdim

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
