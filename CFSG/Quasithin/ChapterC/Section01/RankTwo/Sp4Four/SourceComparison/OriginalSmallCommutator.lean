module
public import Theory.SpecificGroups.SymplecticFour.SmallNaturalCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.AmbientAction
/-!
# Small commutators on the original natural layer

The original moved cover becomes a bijective natural marking when its
literal residual centralizer is trivial. Its full ambient action remains
faithful and semilinear. The small-natural-commutator calculation therefore
bounds the actual centralizer index of an elementary subgroup of the vertex
stabilizer by four, without an assumed inner marking.

The original neighboring-seed application is in
GenerationTwoSymplecticSelectedKernel. Source: MS93 (3.3)(ii) and (5.7),
printed pp.867 and919.
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

/-- A small commutator in the original center-free natural layer gives the
literal centralizer index, without assuming an inner marking of the actor. -/
theorem original_small_commutator_centralizer_index
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
    (A : Subgroup (FreeAmalgam R)) [IsElementaryAbelian 2 A]
    (hA : A ≤ stabilizer R a)
    (hsmall : Nat.card (⁅A,U R a⁆ : Subgroup (FreeAmalgam R)) ≤ 4) :
    (centralizer (A : Set (FreeAmalgam R))).relIndex (U R a) ≤ 4 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,_hκQ,_hκC,_hκL,hψ,hconj,hproj,hker⟩ :=
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
  let α := κ.comp (inclusion hA)
  have hact (x : A) v : j' (Multiplicative.ofAdd (MovedSection.ambientAction s e (α x) v)) =
      x.val*j' (Multiplicative.ofAdd v)*x.val⁻¹ := by
    have hh : ep.symm (MovedSection.ambientAction s e (α x) v) =
        s.space.toRepresentation (α x) (ep.symm v) := by
      apply ep.injective
      rw [ep.apply_symm_apply]
      change _ = MovedSection.coverProjection s e (s.space.toRepresentation (α x) (ep.symm v))
      rw [MovedSection.coverProjection_ambient]
      change _ = MovedSection.ambientAction s e (α x) (ep (ep.symm v))
      rw [ep.apply_symm_apply]
    change j (Multiplicative.ofAdd (ep.symm (MovedSection.ambientAction s e (α x) v))) = _
    rw [hh]
    exact hconj (inclusion hA x) (ep.symm v)
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by omega : 2 < Nat.card F.Carrier))).trans
      Subgroup.topEquiv
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let : Finite (⁅A,U R a⁆ : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion (le_normalizer_iff_commutator_le_right.mp (hA.trans (U_normalized a))))
    (inclusion_injective _)
  exact centralizer_index_le_four_of_small_natural_commutator hFc ((pResidual 2 H).map q)
    (hC ▸ bot_le) (e.groupEquiv.trans d) (MovedSection.ambientAction s e) hψ
    (fun b v => MovedSection.ambientAction_component s e b v)
    (U R a) A j' hj' hjr' α hact hsmall
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
