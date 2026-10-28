module
public import Theory.SpecificGroups.SymplecticFour.SelectedMovement
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction

/-!
# The original small mover centralizes small displacements

The field-four small-mover calculation is lifted through the original
faithful natural action, keeping its full kernel and the bijective marking
of the whole seed. Thus the canonical edge mover fixes the commutator of
an actor of moving index at most four in its two-group.

Source: MS93 (5.7), printed p.919. The literal tensor application is
GenerationTwoSymplecticSelectedMovement.
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

/-- A large small mover centralizes every small displacement in the
original natural layer, with the literal quotient kernel retained. -/
theorem original_large_small_mover_centralizes_commutator
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
    (T E A : Subgroup (FreeAmalgam R)) (hT : IsPGroup 2 T)
    (hTS : T ≤ stabilizer R a) (hET : E ≤ T) (hAT : A ≤ T)
    (hEc : (Q R a).relIndex E = 64)
    (hEm : (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) ≤ 16)
    (hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R a) ≤ 4 ∨ A ≤ E) :
    ⁅A,U R a⁆ ≤ centralizer (E : Set (FreeAmalgam R)) := by
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
  have hAS := hAT.trans hTS
  let V₀ := (U R a).subgroupOf S
  let T₀ := T.subgroupOf S
  let E₀ := E.subgroupOf S
  have hES := hET.trans hTS
  let A₀ := A.subgroupOf S
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
  have hEcard : Nat.card (E₀.map κ) = 64 := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm.trans hEc
  have hiE : (centralizer (E₀ : Set S)).relIndex V₀ ≤ 16 := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective V₀ E₀,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES]
    exact hEm
  have hiA : (centralizer (A₀ : Set S)).relIndex V₀ ≤ 4 ∨ A₀ ≤ E₀ := by
    rcases hsmall with hsmall | hAE
    · apply Or.inl
      rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective V₀ A₀,
        map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS]
      exact hsmall
    · exact Or.inr (comap_mono hAE)
  have hn := SelectedGeneration.large_small_mover_centralizes_commutator hFc
    ((pResidual 2 H).map q) (hC ▸ bot_le) (e.groupEquiv.trans d)
    (MovedSection.ambientAction s e) hψ
    (fun b v => MovedSection.ambientAction_component s e b v)
    V₀ T₀ E₀ A₀ hT.comap_subtype (comap_mono hET) (comap_mono hAT)
    κ hEcard jS hjS hjSr hact hiE hiA
  have hm := (map_mono (f := S.subtype) hn).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [map_commutator,map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS] at hm
  change ⁅A,U R a⁆ ≤ centralizer (E₀.map S.subtype : Set (FreeAmalgam R)) at hm
  rwa [map_subgroupOf_eq_of_le hES] at hm
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
