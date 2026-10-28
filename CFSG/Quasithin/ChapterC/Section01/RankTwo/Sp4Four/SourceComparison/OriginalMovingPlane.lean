module
public import Theory.SpecificGroups.SymplecticFour.QuadraticMovingPlane
public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# Strict movement on the original natural seed

The natural cover with trivial fixed kernel is an actual isomorphism on
its moving layer. Transport the moving-index fixed-plane theorem through
that isomorphism and the literal full neighborhood-kernel quotient.
A subactor moving more than four cosets has the full quadratic overactor's
fixed subgroup, provided the latter has more than two action images.

Source: MS93 (5.6), (5.9)--(5.11), pp.917--924. The application in
GenerationTwoSymplecticIntermediateSeeds identifies full seed intersections;
no original central kernel or conjugation map is replaced.
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

/-- Strict movement on the original seed saturates the quadratic overactor's fixed subgroup. -/
theorem original_moving_quadratic_subactor_fixed_eq
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
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥)
    (A E : Subgroup (FreeAmalgam R)) (hAE : A ≤ E) (hES : E ≤ stabilizer R a)
    (hlarge : 2 < (Q R a).relIndex E)
    (hmove : 4 < (centralizer (A : Set (FreeAmalgam R))).relIndex (U R a))
    (hquad : ⁅E,U R a⁆ ≤ centralizer (E : Set (FreeAmalgam R))) :
    U R a ⊓ centralizer (A : Set (FreeAmalgam R)) =
      U R a ⊓ centralizer (E : Set (FreeAmalgam R)) := by
  have hAS := hAE.trans hES
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq ha
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  let p := (MovedSection.coverProjection s e).toLinearMap
  have hpj : Function.Injective p := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro w hw
    have hwc := (hker w).mp hw
    have hwu : j (Multiplicative.ofAdd w) ∈ U R a := hjr ▸
      (show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩)
    have hz : j (Multiplicative.ofAdd w) = 1 := mem_bot.mp (hfixed ▸ ⟨hwu,hwc⟩)
    exact Multiplicative.ofAdd.injective (hj (hz.trans j.map_one.symm))
  let ep : s.space.toSubmodule ≃ₗ[ZMod 2] Vector F.Carrier :=
    LinearEquiv.ofBijective p ⟨hpj,he.1⟩
  let j' := j.comp ep.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  have hj' : Function.Injective j' := hj.comp (fun v w h =>
    Multiplicative.toAdd.injective (ep.symm.injective (congrArg Multiplicative.toAdd h)))
  have hjr' : j'.range = U R a := by
    rw [MonoidHom.range_comp]
    have hep : Function.Surjective ep.symm.toLinearMap.toAddMonoidHom.toMultiplicative := by
      intro v
      obtain ⟨w,hw⟩ := ep.symm.surjective v.toAdd
      exact ⟨Multiplicative.ofAdd w,congrArg Multiplicative.ofAdd hw⟩
    rw [MonoidHom.range_eq_top_of_surjective _ hep,←MonoidHom.range_eq_map,hjr]
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by omega : 2 < Nat.card F.Carrier))).trans
      Subgroup.topEquiv
  let := finite_stabilizer R a
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  let V₀ := (U R a).subgroupOf S
  let A₀ := A.subgroupOf S
  let E₀ := E.subgroupOf S
  let jS := j'.codRestrict S (fun v => hUS (hjr' ▸ (show j' v ∈ j'.range from ⟨v,rfl⟩)))
  have hjS : Function.Injective jS := fun v w h => hj' (congrArg Subtype.val h)
  have hjSr : jS.range = V₀ := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      change j' v ∈ U R a
      exact hjr' ▸ (show j' v ∈ j'.range from ⟨v,rfl⟩)
    · intro hx
      obtain ⟨v,hv⟩ := (show x.val ∈ j'.range from hjr'.symm ▸ hx)
      exact ⟨v,Subtype.ext hv⟩
  have hact (x : S) v : jS (Multiplicative.ofAdd (MovedSection.ambientAction s e (κ x) v)) =
      x*jS (Multiplicative.ofAdd v)*x⁻¹ := by
    apply Subtype.ext
    have hh : ep.symm (MovedSection.ambientAction s e (κ x) v) =
        s.space.toRepresentation (κ x) (ep.symm v) := by
      apply ep.injective
      rw [ep.apply_symm_apply]
      change _ = MovedSection.coverProjection s e (s.space.toRepresentation (κ x) (ep.symm v))
      rw [MovedSection.coverProjection_ambient]
      change _ = MovedSection.ambientAction s e (κ x) (ep (ep.symm v))
      rw [ep.apply_symm_apply]
    change j (Multiplicative.ofAdd (ep.symm (MovedSection.ambientAction s e (κ x) v))) = _
    rw [hh]
    exact hconj x (ep.symm v)
  have hκker : κ.ker = (Q R a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1)]
  have hEc : 2 < Nat.card (E₀.map κ) := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at hh
    rwa [←hh]
  have hqE : ⁅E₀,V₀⁆ ≤ centralizer (E₀ : Set S) := by
    intro z hz b hb
    apply Subtype.ext
    have hm := mem_map_of_mem S.subtype hz
    rw [map_commutator,map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hUS] at hm
    exact hquad hm b.val hb
  have hAm : 4 < (centralizer (A₀ : Set S)).relIndex V₀ := by
    have hi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective V₀ A₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS] at hi
    rwa [hi] at hmove
  have hi := moving_quadratic_embedded_subactor_fixed_eq hFc
    ((pResidual 2 H).map q) (hC ▸ bot_le) (e.groupEquiv.trans d)
    (MovedSection.ambientAction s e) hψ
    (fun b v => MovedSection.ambientAction_component s e b v)
    V₀ A₀ E₀ (fun _ hx => hAE hx) κ jS hjS hjSr hact hqE hEc hAm
  have hh := congrArg (Subgroup.map S.subtype) hi
  rw [←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
    ←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS,
    map_subgroupOf_eq_of_le hES] at hh
  exact hh
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
