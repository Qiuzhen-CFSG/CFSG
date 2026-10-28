module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.LargeActor

/-!
# The original large critical-index exclusion

Starting from the original finite local group and its two-core quotient, we
construct the embedded initial symplectic cover, its ambient quotient action,
and the inner model homomorphism of the critical seed. The model image order
is the literal critical relative index. The large-actor comparison therefore
bounds that original index by sixteen whenever the source comparison fails.

The inner-plane centralizer identities are kept as explicit earlier geometric
inputs. No cover, actor marking, plane, or invariant refinement is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (3.3), printed p.867.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- The source's actual critical quotient has index below sixteen in the bad
comparison branch. The original initial cover and the critical model actor
are constructed here; only the separately produced inner-plane centralizer
identities remain explicit. -/
theorem original_large_critical_index_lt_sixteen
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
    (hinner : Y ≤ Ltilde R z ⊔ centralizer (Z R z : Set (FreeAmalgam R)))
    (hcomm : ⁅Z R a,Y⁆ ≤ centralizer (Z R z : Set (FreeAmalgam R)))
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    (Q R z).relIndex (Z R a) < 16 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFcard : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hcard : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  apply Nat.lt_of_not_ge
  intro hlarge
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  obtain ⟨β,hβcard,hβmark,hβ⟩ := critical_inner_model_actor path hb hFcard s e he hC
    j hj hjr δ hδ (by omega)
  exact CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_large_actor_excluded_of_card_four
    path hb Y (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
    j hj hjr β hβ hker hinner hcomm hcentral hbad hFcard (by omega)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
