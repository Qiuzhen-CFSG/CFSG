module
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallActor

/-!
# The original fixed Sylow seed lies in the distant core

Every critical image has order at least four over F4 and is therefore inner.
Its quadratic action on the natural cover fixes a normalized full-Sylow
seed pointwise. The original faithful centralizer identifies its fixed core
with Q. Critical minimality then puts the seed in every core within distance
b whose endpoint seed lies in the common normalizing edge. The two-edge
consumer is the first radius step in MS93 (3.4), printed p.868.

All natural coordinates, inner-actor and quotient-image bounds are derived
from the original source hypotheses. The seed uses an actual component
Sylow; no fullness of the replacement radical or central splitting is used.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_critical_centralizes_normalized_sylow_seed
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
    (P : Sylow 2 (Ltilde R z))
    (hn : Z R a ≤ normalizer ((U R z ⊓ centralizer
      ((P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    Z R a ≤ centralizer (U R z ⊓ centralizer
      ((P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype : Set (FreeAmalgam R)) :
        Set (FreeAmalgam R)) := by
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
  have hδc : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hlarge := (original_critical_indices_ge_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb).1
  obtain ⟨β,_,hβmark,hβ⟩ := critical_inner_model_actor path hb hFc s e he hC j hj hjr δ hδ
    (by rw [hδc]; omega)
  let f₀ : Ltilde R z →* J := κ.comp (inclusion (Ltilde_le_stabilizer z))
  have hf₀ : f₀.range=(pResidual 2 H).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hκL
  let f := e.groupEquiv.toMonoidHom.comp
    (f₀.codRestrict ((pResidual 2 H).map q) (fun x => hf₀ ▸ ⟨x,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := (show (e.groupEquiv.symm x : J) ∈ f₀.range from hf₀.symm ▸ (e.groupEquiv.symm x).property)
    refine ⟨y,?_⟩
    change e.groupEquiv ⟨f₀ y,_⟩=x
    rw [show (⟨f₀ y,_⟩ : (pResidual 2 H).map q)=e.groupEquiv.symm x from Subtype.ext hy,
      e.groupEquiv.apply_symm_apply]
  have hfmark (x : Ltilde R z) : (e.groupEquiv.symm (f x) : J)=f₀ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨f₀ x,_⟩) : J)=f₀ x
    rw [e.groupEquiv.symm_apply_apply]
  have hfact (x : Ltilde R z) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (f x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (f x)) v))=_
    rw [hfmark]
    exact hconj (inclusion (Ltilde_le_stabilizer z) x) v
  let T := (P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype
  let d : (P : Subgroup (Ltilde R z)) ≃* T :=
    (P : Subgroup (Ltilde R z)).equivMapOfInjective (Ltilde R z).subtype (Ltilde R z).subtype_injective
  let π : T →* L (K := F.Carrier) :=
    (f.comp (P : Subgroup (Ltilde R z)).subtype).comp d.symm.toMonoidHom
  let := finite_stabilizer R z
  let : Finite (Ltilde R z) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer z)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range=(S : Subgroup (L (K := F.Carrier))) := by
    change π.range = (P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective d.symm.toMonoidHom d.symm.surjective,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : T) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v)) =
        (t : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(t : FreeAmalgam R)⁻¹ := by
    have hh := hfact (d.symm t) v
    have hval : ((d.symm t : P) : FreeAmalgam R)=(t : FreeAmalgam R) :=
      congrArg Subtype.val (d.apply_symm_apply t)
    exact hval ▸ hh
  exact quadratic_centralizes_normalized_embedded_sylow_seed (U R z) (Z R a) T
    j hj hjr π S hπ β (MovedSection.coverAction s e) hT hβ
    (MovedSection.coverProjection s e) he
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
      path hb (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he j hj hjr β hβ) hn

theorem original_sylow_seed_le_core_of_distance
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
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {d c t : Vertex R} (hd : color R d = false) (hcc : color R c = false)
    (hdc : (cosetGraph R).dist d c ≤ geometry.b R)
    (hct : (cosetGraph R).dist c t < geometry.b R)
    (P : Sylow 2 (Ltilde R d))
    (hn : Q R t ≤ normalizer ((U R d ⊓ centralizer
      ((P : Subgroup (Ltilde R d)).map (Ltilde R d).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    U R d ⊓ centralizer
      ((P : Subgroup (Ltilde R d)).map (Ltilde R d).subtype : Set (FreeAmalgam R)) ≤ Q R c := by
  by_cases hz : Z R d ≤ Q R c
  · exact (inf_le_left.trans (U_le_Z d)).trans hz
  have hcrit : CriticalPair R d c (geometry.exists_critical d hd) := by
    refine ⟨le_antisymm ?_ (criticalDistance_le R d _ hz),hz⟩
    rwa [geometry.distance_constant d hd]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith
  have hrev := critical_reverse R geometry hedge d hd
    (by rwa [geometry.distance_constant d hd]) c hcc hcrit
  obtain ⟨walk,hwalk⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c d
  let path : CriticalPath R geometry c d := ⟨hcc,walk,hwalk,hrev⟩
  have hZt : Z R c ≤ Q R t := Z_le_Q_of_dist_lt R c (geometry.exists_critical c hcc)
    (by rwa [geometry.distance_constant c hcc])
  have hcentral := original_critical_centralizes_normalized_sylow_seed R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb P (hZt.trans hn)
  rw [←MSCentralOrbit.C_eq_Q R hp hQR hfaith c hcc]
  exact le_inf
    ((inf_le_left.trans (U_le_Z d)).trans
      (Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd) hcrit.1.le))
    (le_centralizer_iff.mp hcentral)

theorem original_two_edge_sylow_seed_le_distant_core
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
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {a d c t : Vertex R} (hd : color R d = false) (hcc : color R c = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hac : (cosetGraph R).dist a c + 2 ≤ geometry.b R)
    (P : Sylow 2 (Ltilde R d))
    (hn : Q R t ≤ normalizer ((U R d ⊓ centralizer
      ((P : Subgroup (Ltilde R d)).map (Ltilde R d).subtype : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set _)) :
    U R d ⊓ centralizer
      ((P : Subgroup (Ltilde R d)).map (Ltilde R d).subtype : Set (FreeAmalgam R)) ≤ Q R c := by
  have hdt1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
  have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have htac := (cosetGraph_connected R).dist_triangle (u := t) (v := a) (w := c)
  have hdtc := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := c)
  have hta1 : (cosetGraph R).dist t a = 1 := by rwa [SimpleGraph.dist_comm]
  rw [hta1] at htac
  have hdc : (cosetGraph R).dist d c ≤ geometry.b R := by omega
  have hct : (cosetGraph R).dist c t < geometry.b R := by
    rw [SimpleGraph.dist_comm]
    omega
  exact original_sylow_seed_le_core_of_distance R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq geometry hb hd hcc hdc hct P hn

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
