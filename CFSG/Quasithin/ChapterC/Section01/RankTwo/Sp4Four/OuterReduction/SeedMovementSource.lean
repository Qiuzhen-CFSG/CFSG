module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates
/-!
# The original bad star moves the critical endpoint intersection

The literal bad-star choice gives a full component Sylow seed whose join
with Z_start escapes normalization by Z_endpoint. The original small-image
comparison identifies the critical image with an order-four root, including
its natural fixed hyperplane. If the chosen seed fixed Z_endpoint intersect
Q_start, its action would belong to that same root and its displacement
would lie in the critical commutator, contradicting the chosen escape.

All marked covers, action kernels and root dimensions are constructed from
the original H, R and q. This is the movement step of MS93 (3.4), printed
p.868; the subsequent path contradiction and star cut remain separate.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- A source seed escaping the critical join must move the actual intersection
Z_endpoint ∩ Q_start. The root image and its fixed hyperplane are constructed
from the original source data. -/
theorem original_seed_moves_critical_intersection
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
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z) (hYQ : Y ≤ Q R a)
    (hn : ¬ Z R z ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    ¬ Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro hfix
  obtain ⟨hz,ha⟩ := original_critical_indices_eq_four_of_core_seed R hms hp hne hQR
    hself hfaith q hq hcore hc hC hsq path hb Y hYZ hYQ hn
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFc : Nat.card F.Carrier=4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range=4 := (quotient_image_card _ _ _ hAZ κ hκQ).trans hz
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := C_eq_Q R hp hQR hfaith a path.start_color
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor path hb hCa hFc
    s e he hC j hj hjr δ hδ hδcard ha
  exact critical_escape_of_seed_join_nonnormalization path Y hn
    (critical_seed_displacement_le_of_fixed_intersection path hb hCa (by omega)
      s e he hC j hj hjr κ hκC hconj β hAZ hβmark hβ hd
      (hβcard.trans hFc.symm) Y hYZ hfix)

/-- The original bad-star witness has nontrivial action on the endpoint
intersection, with the same edges, component Sylow and transported seed. -/
theorem original_bad_star_moving_seed
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hgen : pResidual 2 H ⊔ R = ⊤)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hbad : ¬ ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤ Z R (alpha R)) :
    ∃ d t : Vertex R, ∃ P' : Sylow 2 (Ltilde R d),
      color R d=false ∧ Adjacent R (alpha R) t ∧ Adjacent R d t ∧
      Q R t ≤ normalizer (componentSylowSeed R d P' : Set (FreeAmalgam R)) ∧
      componentSylowSeed R d P' ≤ sourceStarAlpha R Y ∧
      ¬ Z R z ≤ normalizer ((componentSylowSeed R d P' ⊔ Z R (alpha R) :
        Subgroup (FreeAmalgam R)) : Set _) ∧
      ¬ componentSylowSeed R d P' ≤ centralizer
        ((Z R z ⊓ Q R (alpha R) : Subgroup (FreeAmalgam R)) : Set _) := by
  obtain ⟨d,t,P',hd,hat,hdt,hn',hseed,hnot⟩ := original_bad_star_critical_seed R hms hp hne hQR
    hgen hself hfaith q hq hcore hc hC hsq geometry hb path Y P hY hn hbad
  refine ⟨d,t,P',hd,hat,hdt,hn',hseed,hnot,?_⟩
  exact original_seed_moves_critical_intersection R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb (componentSylowSeed R d P')
    (hseed.trans (original_sourceStarAlpha_le_critical_endpoint_stabilizer R hms hp hne hQR
      hself hfaith q hq hcore hc hC hsq geometry hb path Y P hY hn))
    (hseed.trans (original_sourceStarAlpha_le_own_core R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq geometry hb Y P hY hn)) hnot

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
