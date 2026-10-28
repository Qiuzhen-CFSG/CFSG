module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallActor

/-!
# The full critical seed in the original residual preimage

Quadraticity and the critical index bound place the natural image of the
full seed in the symplectic component. Pulling back through the original
ambient action gives its containment in the residual joined with the entire
endpoint kernel. This is used by the original radius chief-factor argument.

Source: MS93 (3.3) and (5.2)(i), printed pp.867 and914.
-/

open scoped IsMulCommutative
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- The original full critical seed lies over the residual component image. -/
theorem original_critical_seed_le_residual_sup_kernel
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
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R) :
    Z R a ≤ Ltilde R z ⊔ Q R z := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,hκL,_hψ,hconj,_hproj,_hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  have hlarge := (original_critical_indices_ge_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb).1
  obtain ⟨β,_hβcard,hβmark,_hβ⟩ := critical_inner_model_actor path hb hFc s e he hC
    j hj hjr δ (fun x v => hconj (inclusion hAZ x) v) (by rw [hδcard]; omega)
  have hB : (Z R a).subgroupOf (stabilizer R z) ≤
      (((Ltilde R z).subgroupOf (stabilizer R z)).map κ).comap κ := by
    intro x hx
    change κ x ∈ ((Ltilde R z).subgroupOf (stabilizer R z)).map κ
    rw [hκL]
    have hh := hβmark ⟨x.val,hx⟩
    exact hh ▸ (e.groupEquiv.symm (β ⟨x.val,hx⟩)).property
  rw [comap_map_eq] at hB
  have hm := map_mono (f := (stabilizer R z).subtype) hB
  rwa [map_subgroupOf_eq_of_le hAZ,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (Ltilde_le_stabilizer z),hκQ] at hm

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
