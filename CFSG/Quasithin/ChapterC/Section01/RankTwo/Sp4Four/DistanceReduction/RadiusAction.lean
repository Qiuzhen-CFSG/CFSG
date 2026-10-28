module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallActor

/-!
# The original radius action inside the symplectic component

A seed within critical distance either lies in the endpoint kernel or gives
an original critical pair. The reciprocal critical-index bound makes the
latter image inner. Taking the actual radius join therefore constructs a
homomorphism to Sp4(4), with kernel exactly its intersection with the endpoint
two-core. The natural cover, its full central kernel, and conjugation formula
are retained. This does not bound the critical distance.

Source: MS93 (3.3), p.867, and the first paragraph of (5.2), p.914.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

omit [Finite H] in
/-- Every radius seed reaches the endpoint stabilizer by critical minimality. -/
theorem radius_le_stabilizer_of_distance (R : Subgroup H)
    (geometry : Geometry R) {a z : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a z + 2 ≤ geometry.b R) :
    V R a ≤ stabilizer R z := by
  apply (V_le_iff R ha _).mpr
  intro d hdc hda
  apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hdc)
  rw [geometry.distance_constant d hdc]
  change (cosetGraph R).dist d z ≤ geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := z)
  omega

/-- The whole original radius acts through the symplectic component, on the
same natural cover and with its exact two-core kernel. -/
theorem original_radius_inner_action
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
    {a z : Vertex R} (ha : color R a = false) (hz : color R z = false)
    (hd : (cosetGraph R).dist a z + 2 ≤ geometry.b R) :
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ f : V R a →* Sp F.Carrier,
        f.ker = (Q R z).subgroupOf (V R a) ∧
      ∃ π : U R z →* Multiplicative (Vector F.Carrier), Function.Surjective π ∧
        (∀ u : U R z, π u = 1 ↔
          (u : FreeAmalgam R) ∈ centralizer (Ltilde R z : Set (FreeAmalgam R))) ∧
        (∀ (v : V R a) (u : U R z),
          π ⟨v.val*u.val*v.val⁻¹,
            (mem_normalizer_iff.mp (U_normalized z
              (radius_le_stabilizer_of_distance R geometry ha hd v.property)) u.val).mp u.property⟩ =
            Multiplicative.ofAdd (f v • (π u).toAdd)) := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,_hκ,hκQ,_hκC,_hκL,_hψ,hconj,_hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq hz
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hV := radius_le_stabilizer_of_distance R geometry ha hd
  have hκker : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
    rw [←hκQ,subgroupOf_map_subtype_eq]
  have hinner : V R a ≤ (((pResidual 2 H).map q).comap κ).map (stabilizer R z).subtype := by
    apply (V_le_iff R ha _).mpr
    intro d hdc hda
    have hdz : (cosetGraph R).dist d z ≤ geometry.b R := by
      have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := z)
      omega
    have hDZ : Z R d ≤ stabilizer R z := Z_le_stabilizer_of_dist_le d
      (geometry.exists_critical d hdc) (by rwa [geometry.distance_constant d hdc])
    intro x hx
    refine ⟨inclusion hDZ ⟨x,hx⟩,?_,rfl⟩
    change κ (inclusion hDZ ⟨x,hx⟩) ∈ (pResidual 2 H).map q
    by_cases hDQ : Z R d ≤ Q R z
    · have hkx : inclusion hDZ ⟨x,hx⟩ ∈ κ.ker := by rw [hκker]; exact hDQ hx
      rw [show κ (inclusion hDZ ⟨x,hx⟩) = 1 from hkx]
      exact one_mem _
    · have hcrit : CriticalPair R d z (geometry.exists_critical d hdc) := by
        refine ⟨le_antisymm ?_ (criticalDistance_le R d _ hDQ),hDQ⟩
        rwa [geometry.distance_constant d hdc]
      obtain ⟨walk,hwalk⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d z
      let path : CriticalPath R geometry d z := ⟨hdc,walk,hwalk,hcrit⟩
      let δ : Z R d →* J := κ.comp (inclusion hDZ)
      have hcard : Nat.card δ.range = (Q R z).relIndex (Z R d) :=
        quotient_image_card _ _ _ hDZ κ hκQ
      have hδ : ∀ x : Z R d, ∀ v : s.space.toSubmodule,
          j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
            (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
        fun x v => hconj (inclusion hDZ x) v
      have hlarge := (original_critical_indices_ge_four R hms hp hne hQR hself hfaith
        q hq hcore hc hC hsq path hb).1
      obtain ⟨β,_,hβ,_⟩ := critical_inner_model_actor path hb hFc s e he hC
        j hj hjr δ hδ (by rw [hcard]; omega)
      exact hβ ⟨x,hx⟩ ▸ (e.groupEquiv.symm (β ⟨x,hx⟩)).property
  let δ : V R a →* J := κ.comp (inclusion hV)
  have hδB (v : V R a) : δ v ∈ (pResidual 2 H).map q := by
    obtain ⟨w,hw,hwv⟩ := hinner v.property
    have heq : w = inclusion hV v := Subtype.ext hwv
    change κ w ∈ (pResidual 2 H).map q at hw
    simpa only [heq,δ,MonoidHom.comp_apply] using hw
  let f : V R a →* Sp F.Carrier := (commutator (Sp F.Carrier)).subtype.comp
    (e.groupEquiv.toMonoidHom.comp (δ.codRestrict _ hδB))
  have hfker : f.ker = (Q R z).subgroupOf (V R a) := by
    ext v
    change (e.groupEquiv ⟨δ v,hδB v⟩ : Sp F.Carrier) = 1 ↔ v.val ∈ Q R z
    have hh : (e.groupEquiv ⟨δ v,hδB v⟩ : Sp F.Carrier) = 1 ↔ δ v = 1 := by
      constructor
      · intro hx
        have hx' : e.groupEquiv ⟨δ v,hδB v⟩ = 1 := Subtype.ext hx
        exact congrArg Subtype.val ((e.groupEquiv.map_eq_one_iff).mp hx')
      · intro hx
        have hx' : (⟨δ v,hδB v⟩ : (pResidual 2 H).map q) = 1 := Subtype.ext hx
        rw [hx',map_one]
        rfl
    rw [hh]
    change inclusion hV v ∈ κ.ker ↔ v.val ∈ Q R z
    rw [hκker]
    rfl
  have hVU : V R a ≤ normalizer (U R z : Set (FreeAmalgam R)) := hV.trans (U_normalized z)
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection
    (U R z) (V R a) hVU s.space.toRepresentation (MovedSection.ambientAction s e) j hj hjr
    (MovedSection.coverProjection s e).toLinearMap he.1
    (MovedSection.coverProjection_ambient s e) δ (fun v w => hconj (inclusion hV v) w)
  refine ⟨F,hF,f,hfker,π,hπ,?_,?_⟩
  · intro u
    obtain ⟨w,hw⟩ := (show u.val ∈ j.range from hjr.symm ▸ u.property)
    have heq : (⟨j (Multiplicative.ofAdd w.toAdd),by rw [←hjr]; exact ⟨_,rfl⟩⟩ : U R z) = u :=
      Subtype.ext hw
    have hπw := hπj w.toAdd
    rw [heq] at hπw
    rw [hπw]
    change MovedSection.coverProjection s e w.toAdd = 0 ↔ _
    rw [hker]
    exact hw ▸ Iff.rfl
  · intro v u
    rw [hπact]
    have hh := MovedSection.ambientAction_component s e (⟨δ v,hδB v⟩ : (pResidual 2 H).map q)
      (π u).toAdd
    exact congrArg Multiplicative.ofAdd hh

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H : Type*} [Group H] [Finite H] {R : Subgroup H} {geometry : Geometry R}
  {a z : Vertex R}

/-- The radius kernel at the penultimate same-color vertex fixes the endpoint. -/
theorem truncated_radius_le_endpoint_stabilizer
    (path : CriticalPath R geometry a z) (hb : 2 ≤ geometry.b R) :
    V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) ≤ stabilizer R z := by
  have htwo : 2 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hc : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  apply inf_le_right.trans
  apply Q_le_stabilizer_of_dist_two R _ z hc
  rw [path.dist_end]
  omega

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
