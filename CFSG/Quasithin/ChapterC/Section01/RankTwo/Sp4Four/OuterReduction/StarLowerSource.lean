module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarLower
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedMovementSource
/-!
# The original noncritical star actor has fixed index at least four

The original critical comparison constructs the order-four root and its
three-dimensional natural fixed hyperplane. An actor containing the moving
seed must move that hyperplane, since a pointwise fixer matches an original
start-layer element modulo the literal endpoint centralizer. The semilinear
fixed-index estimate then gives index at least four in the original endpoint
intersection, including all its central attachments.

This is the lower estimate for the noncritical branch of Meierfrankenfeld--
Stellmacher (1993), (3.4), printed p.868. The independent upper estimate
contradicts it in the original star argument.
-/
public section
noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- Every endpoint actor containing the original escaping seed has centralizer
index at least four in the actual critical endpoint intersection. -/
theorem original_seed_actor_centralizer_index_four
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
    ∀ (D : Subgroup (FreeAmalgam R)), Y ≤ D → D ≤ stabilizer R z →
      4 ≤ (centralizer (D : Set (FreeAmalgam R))).relIndex (Z R z ⊓ Q R a) := by
  intro D hYD hDZ
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
  have hmove := original_seed_moves_critical_intersection R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y hYZ hYQ hn
  exact four_le_critical_intersection_centralizer_index path hb hCa hFc
    s e he hC j hj hjr κ hκC hconj β hAZ hβmark hβ hd
    (hβcard.trans hFc.symm) D hDZ (fun hfix => hmove (hYD.trans hfix))

/-- The literal full-Sylow seed at the noncritical vertex forces index at least
four for the action of its whole Z-layer on the critical intersection. -/
theorem original_noncritical_seed_centralizer_index_four
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
    (d : Vertex R) (P : Sylow 2 (Ltilde R d))
    (hDZ : Z R d ≤ stabilizer R z)
    (hYQ : componentSylowSeed R d P ≤ Q R a)
    (hn : ¬ Z R z ≤ normalizer ((componentSylowSeed R d P ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _)) :
    4 ≤ (centralizer (Z R d : Set (FreeAmalgam R))).relIndex (Z R z ⊓ Q R a) := by
  have hYD : componentSylowSeed R d P ≤ Z R d := inf_le_left.trans (U_le_Z d)
  exact original_seed_actor_centralizer_index_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb (componentSylowSeed R d P) (hYD.trans hDZ)
    hYQ hn (Z R d) hYD hDZ

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
