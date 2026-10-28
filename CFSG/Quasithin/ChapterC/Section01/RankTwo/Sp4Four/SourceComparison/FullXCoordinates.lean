module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# Whole central-omega coordinates at an original Sp₄(4) vertex

The original vertex embedding sends the entire central omega subgroup to X,
and its canonical moved subspace to U. Transport the original quotient through
that same embedding to retain its exact Q = C(Z) kernel and its component image.
Both the whole vertex action and the marked symplectic component act by literal
conjugation on X, including its fixed central attachment.

Source: MS93 (3.2)(vi) and (3.3)(ii)(2), printed pp.866–867. These coordinates
supply the whole-X realization used in the original critical decomposition.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Any given natural marking of the canonical moved section extends to the
original whole-X coordinates, with the same quotient and conjugation formulas. -/
theorem fullX_coordinates_at_vertex
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
    {a : Vertex R} (ha : color R a = false) :
    let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
    let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 H)) q hq
      (hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm)
    let s := MovedSection.ofNormal ρ ((pResidual 2 H).map q)
    ∀ (F : BinaryField)
      (e : ActionEquiv (s.action.comp ((pResidual 2 H).map q).subtype)
          (binaryNatural (K := F.Carrier))),
      ∃ j : Multiplicative (Additive (omegaCenterIn (pCore 2 H))) →* FreeAmalgam R,
        Function.Injective j ∧ j.range = X R a ∧
        (j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative).range = U R a ∧
      ∃ κ : stabilizer R a →* J, Function.Surjective κ ∧
        κ.ker.map (stabilizer R a).subtype = Q R a ∧
        κ.ker.map (stabilizer R a).subtype = C R a ∧
        ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = (pResidual 2 H).map q ∧
        (∀ (g : stabilizer R a) (v : Additive (omegaCenterIn (pCore 2 H))),
          j (Multiplicative.ofAdd (ρ (κ g) v)) =
            (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) ∧
      ∃ f : Ltilde R a →* L (K := F.Carrier), Function.Surjective f ∧
        (∀ (g : Ltilde R a) (v : Additive (omegaCenterIn (pCore 2 H))),
          j (Multiplicative.ofAdd
            (ρ (((pResidual 2 H).map q).subtype (e.groupEquiv.symm (f g))) v)) =
            (g : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam R)⁻¹) := by
  dsimp only
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 H)) q hq hk
  let s := MovedSection.ofNormal ρ ((pResidual 2 H).map q)
  intro F e
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel R hp hQR ha
  let j₀ : Multiplicative (Additive (omegaCenterIn (pCore 2 H))) →* H :=
    { toFun := fun v => v.toAdd.toMul.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j := i.comp j₀
  have hj₀ : Function.Injective j₀ := by
    intro x y h
    exact Multiplicative.toAdd.injective (Additive.toMul.injective (Subtype.ext h))
  have hj₀r : j₀.range = omegaCenterIn (pCore 2 H) := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact v.toAdd.toMul.property
    · intro hx
      exact ⟨Multiplicative.ofAdd (Additive.ofMul ⟨x,hx⟩),rfl⟩
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,hcore]
    exact hiQ
  refine ⟨j,hi.comp hj₀,?_,?_,κ,
    ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,?_,?_⟩
  · rw [MonoidHom.range_comp,hj₀r]
    change (omegaCenter (pCore 2 H)).map i = omegaCenter (Q R a)
    rw [←hiQ,omegaCenter_map _ _ hi]
  · change (i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H))
      (pResidual 2 H) q hq hk)).range = U R a
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,
      ←initialCore_eq R hms hp hne hQR hself hfaith q hq hcore
        (pResidual 2 H) ((pResidual 2 H).map q) rfl hc hC hsq]
    exact hiU
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q R hp hQR hfaith a ha).symm
  · rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  · intro g v
    let d := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
    have hd : i (d.symm g) = (g : FreeAmalgam R) :=
      congrArg Subtype.val (d.apply_symm_apply g)
    have hh := congrArg i (NormalElementaryQuotient.representation_apply
      (omegaCenterIn (pCore 2 H)) q hq hk (d.symm g) v)
    change i ((ρ (q (d.symm g)) v).toMul.val) =
      (g : FreeAmalgam R) * i v.toMul.val * (g : FreeAmalgam R)⁻¹
    simpa only [map_mul,map_inv,hd] using hh
  · let d : pResidual 2 H ≃* Ltilde R a :=
      ((pResidual 2 H).equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hiL)
    let f : Ltilde R a →* L (K := F.Carrier) := e.groupEquiv.toMonoidHom.comp
      ((q.subgroupMap (pResidual 2 H)).comp d.symm.toMonoidHom)
    refine ⟨f,e.groupEquiv.surjective.comp
      ((q.subgroupMap_surjective _).comp d.symm.surjective),?_⟩
    intro g v
    change i ((ρ (e.groupEquiv.symm (e.groupEquiv
      (q.subgroupMap (pResidual 2 H) (d.symm g)))).val v).toMul.val) =
        (g : FreeAmalgam R) * i v.toMul.val * (g : FreeAmalgam R)⁻¹
    rw [e.groupEquiv.symm_apply_apply]
    change i ((ρ (q (d.symm g)) v).toMul.val) =
      (g : FreeAmalgam R) * i v.toMul.val * (g : FreeAmalgam R)⁻¹
    have hd : i (d.symm g) = (g : FreeAmalgam R) :=
      congrArg Subtype.val (d.apply_symm_apply g)
    have hh := congrArg i (NormalElementaryQuotient.representation_apply
      (omegaCenterIn (pCore 2 H)) q hq hk (d.symm g) v)
    change i ((ρ (q (d.symm g)) v).toMul.val) = _ at hh
    simpa only [map_mul,map_inv,hd] using hh

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
