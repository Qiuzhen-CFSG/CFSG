module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.FullXCoordinates
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed
public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction
public import Theory.SpecificGroups.SymplecticFour.QuadraticFixedSubgroup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates

/-!
# Fixed vectors of large actors in the full original X-layer

The original moved natural cover embeds in the full central omega module
when the complete residual-fixed subgroup is trivial. Its quotient is
trivial, so this is a natural dual cover. A quadratic actor of order at
least sixteen preserves no quadratic refinement over the field of four
elements. The dual-cover theorem therefore places every actor-fixed element
of X in the original moving subgroup U.

All coordinates use the original quotient, its full Q kernel and the
literal conjugation action. This does not identify X with U. The tensor
consumer applies it to its full edge mover to remove intermediate-seed
containment premises in the large critical-image branch.

Source: MS93 (1.5)(ii) and (5.3), the latter on printed p.915; Aschbacher--Smith 9.3.10,
printed pp.734--735.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

open scoped commutatorElement
/-- A large quadratic actor fixes only the natural submodule of the full
original central omega layer. The complete residual-fixed kernel is zero. -/
theorem original_large_quadratic_X_fixed_le_U
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false)
    (hfixed : X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (A : Subgroup (FreeAmalgam R)) (hAS : A ≤ stabilizer R a)
    (hlarge : 16 ≤ (Q R a).relIndex A)
    (hquad : ⁅A,U R a⁆ ≤ centralizer (A : Set (FreeAmalgam R))) :
    X R a ⊓ centralizer (A : Set (FreeAmalgam R)) ≤ U R a := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 H)) q hq hk
  let B := (pResidual 2 H).map q
  let s := MovedSection.ofNormal ρ B
  obtain ⟨F,hF,e,he⟩ := centralOmega_initial_cover R hms hp hne hQR hself hfaith
    q hq hcore B hc hC hsq
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  obtain ⟨j,hj,hjr,hjUr,κ,_hκ,hκQ,_hκC,_hκL,hfull,f,_hf,hfconj⟩ :=
    fullX_coordinates_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq ha F e
  let σ := ρ.comp (B.subtype.comp e.groupEquiv.symm.toMonoidHom)
  let W : Subrepresentation σ :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule _g _v hv := s.space.apply_mem_toSubmodule _ hv }
  have hσfixed : OneCohomology.fixed σ = ⊥ := by
    apply bot_unique
    intro v hv
    have hm : j (Multiplicative.ofAdd v) ∈ X R a ⊓ centralizer (Ltilde R a : Set _) := by
      refine ⟨hjr ▸ ⟨_,rfl⟩,?_⟩
      intro g hg
      have hh := hfconj ⟨g,hg⟩ v
      change j (Multiplicative.ofAdd (σ (f ⟨g,hg⟩) v)) = _ at hh
      rw [hv] at hh
      have hm := congrArg (fun z : FreeAmalgam R => z*g) hh
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hm.symm
    rw [hfixed] at hm
    exact Multiplicative.ofAdd.injective (hj ((mem_bot.mp hm).trans j.map_one.symm))
  let p : W.toRepresentation.IntertwiningMap (binaryNatural (K := F.Carrier)) :=
    MovedSection.coverProjection s e
  have hpj : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    apply Subtype.ext
    apply hσfixed.le
    intro g
    exact congrArg Subtype.val (he.2.1 hw g)
  let ep : W.toSubmodule ≃ₗ[ZMod 2] Vector F.Carrier :=
    LinearEquiv.ofBijective p.toLinearMap ⟨hpj,he.1⟩
  let i : (binaryNatural (K := F.Carrier)).IntertwiningMap σ :=
    (W.toSubmodule.subtype.comp ep.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change (ep.symm (binaryNatural g v)).val = (W.toRepresentation g (ep.symm v)).val
      apply congrArg Subtype.val
      apply ep.injective
      change ep (ep.symm (binaryNatural g v)) = ep (W.toRepresentation g (ep.symm v))
      rw [ep.apply_symm_apply]
      change _ = p (W.toRepresentation g (ep.symm v))
      rw [p.isIntertwining]
      change _ = binaryNatural g (ep (ep.symm v))
      rw [ep.apply_symm_apply])
  have hirange : i.toLinearMap.range = W.toSubmodule := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩; exact (ep.symm v).property
    · intro v hv
      exact ⟨ep ⟨v,hv⟩,congrArg Subtype.val (ep.symm_apply_apply ⟨v,hv⟩)⟩
  have hi : Function.Injective i := Subtype.val_injective.comp ep.symm.injective
  have hdual : IsDualCover i.range := by
    refine ⟨?_,hσfixed⟩
    intro g v
    change σ g v-v ∈ i.toLinearMap.range
    rw [hirange]
    change ρ (e.groupEquiv.symm g).val v-v ∈ s.space.toSubmodule
    apply s.space_eq.ge
    exact Submodule.subset_span ⟨_,(e.groupEquiv.symm g).property,v,Submodule.mem_top,rfl⟩
  let jU := j.comp W.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
  have hjU : Function.Injective jU := by
    intro x y h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hj h)
  let δ := κ.comp (inclusion hAS)
  have hδfull (x : A) (v : Additive (omegaCenterIn (pCore 2 H))) :
      j (Multiplicative.ofAdd (ρ (δ x) v)) = x.val*j (Multiplicative.ofAdd v)*x.val⁻¹ :=
    hfull (inclusion hAS x) v
  have hδc : 16 ≤ Nat.card δ.range := by
    rw [quotient_image_card _ _ _ hAS κ hκQ]
    exact hlarge
  have hδq : IsQuadratic s.space.toRepresentation δ.range := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    apply Multiplicative.ofAdd.injective
    apply hjU
    have hd : jU (Multiplicative.ofAdd (s.space.toRepresentation (δ y) v-v)) =
        ⁅y.val,jU (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv]
      change j (Multiplicative.ofAdd (ρ (δ y) v.val))*_ = _
      rw [hδfull y]
      rfl
    have hc := hquad (commutator_mem_commutator y.property
      (show jU (Multiplicative.ofAdd v) ∈ U R a from hjUr ▸ ⟨_,rfl⟩)) x.val x.property
    change j (Multiplicative.ofAdd (ρ (δ x) (s.space.toRepresentation (δ y) v-v).val)) = _
    rw [hδfull x]
    change x.val*jU (Multiplicative.ofAdd (s.space.toRepresentation (δ y) v-v))*x.val⁻¹ = _
    rw [hd,hc,mul_inv_cancel_right]
  have hδnat : IsQuadratic (MovedSection.ambientAction s e) δ.range := by
    intro x hx y hy v
    obtain ⟨w,rfl⟩ := he.1 v
    have hh := congrArg (MovedSection.coverProjection s e) (hδq x hx y hy w)
    simpa only [map_sub,MovedSection.coverProjection_ambient] using hh
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
        (by omega : 2 < Nat.card F.Carrier))).trans Subgroup.topEquiv
  have hδB : δ.range ≤ B :=
    SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card hFc B
      (hC ▸ bot_le) (e.groupEquiv.trans d) (MovedSection.ambientAction s e)
      (MovedSection.ambientAction_faithful s e binaryNatural_injective hC)
      (fun b v => MovedSection.ambientAction_component s e b v) δ.range hδnat (by omega)
  let A' := (δ.range.subgroupOf B).map e.groupEquiv.toMonoidHom
  have hA'c : 16 ≤ Nat.card A' := by
    rw [card_map_of_injective e.groupEquiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe hδB).toEquiv]
    exact hδc
  have hA'q : IsQuadratic (binaryNatural (K := F.Carrier)) A' := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    simpa only [MovedSection.ambientAction_component,MulEquiv.coe_toMonoidHom] using
      hδnat x.val hx y.val hy v
  have hno : ¬ ∃ c : Natural (K := F.Carrier), ∀ a : A', ∀ v,
      Plane.OrthogonalActors.refinement c (binaryNatural a.val v) =
        Plane.OrthogonalActors.refinement c v := by
    have hn := no_refinement_of_large_quadratic (by omega : 2 < Nat.card F.Carrier)
      (A'.map (commutator (Sp F.Carrier)).subtype)
      (by rw [card_map_of_injective Subtype.val_injective,hFc]; exact hA'c)
      (by
        rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
        exact hA'q x hx y hy v)
    rintro ⟨c,hc⟩
    apply hn
    refine ⟨c,?_⟩
    rintro ⟨_,⟨x,hx,rfl⟩⟩ v
    exact hc ⟨x,hx⟩ v
  rintro x ⟨hx,hcent⟩
  obtain ⟨v,rfl⟩ := (show x ∈ j.range from hjr.symm ▸ hx)
  have hv : v.toAdd ∈ OneCohomology.fixed (σ.comp A'.subtype) := by
    rintro ⟨_,⟨b,hb,rfl⟩⟩
    obtain ⟨a,ha⟩ := hb
    change δ a = (b:J) at ha
    apply Multiplicative.ofAdd.injective
    apply hj
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (e.groupEquiv b)) v.toAdd)) = _
    rw [e.groupEquiv.symm_apply_apply,←ha,hδfull a,ofAdd_toAdd,
      hcent a.val a.property,mul_inv_cancel_right]
  have hvW := dualCover_fixed_le_natural_of_no_refinement i hi hdual A' hno hv
  rw [hirange] at hvW
  rw [←hjUr]
  exact ⟨Multiplicative.ofAdd ⟨v.toAdd,hvW⟩,rfl⟩

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
