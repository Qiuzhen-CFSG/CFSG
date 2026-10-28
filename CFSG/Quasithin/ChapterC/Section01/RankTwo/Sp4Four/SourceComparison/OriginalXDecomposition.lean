module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.XDecomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.FullXCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootCoordinates

/-!
# The original symplectic critical X-decomposition

The two original critical indices become four. The opposite root bounds
movement of the whole X-layer; its reciprocal root has four generating
conjugates. Canonical coordinates on the full central omega subgroup retain
the natural moving cover and its fixed attachment, so saturation gives
X = U C_X(Ltilde). Since Q centralizes X, this is the printed center form
inside the residual-core product Q Ltilde.

The local-actor and adjacent-core consumers derive the index bound from
the original failed commutator comparison. No action, root, cover, index
budget, or decomposition premise is added to that source statement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii)(2), printed p.867.
The subsequent iterated-commutator conclusions remain separate.
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

omit [Finite H] in
/-- The fixed factor is the literal center intersection in the residual-core product. -/
theorem X_inf_component_centralizer_eq_local_center (R : Subgroup H) (a : Vertex R) :
    X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      X R a ⊓ centerIn (Q R a ⊔ Ltilde R a) := by
  have hXQ : X R a ≤ Q R a := omegaCenter_le (Q R a)
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    refine ⟨hx,⟨show x ∈ Q R a ⊔ Ltilde R a from (show Q R a ≤ Q R a ⊔ Ltilde R a from le_sup_left) (hXQ hx),?_⟩⟩
    have hN : Q R a ⊔ Ltilde R a ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
      apply sup_le
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (Q_le_centralizer_X R a hy x hx).symm
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (hc y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hN hy)
  · rintro ⟨hx,hc⟩
    exact ⟨hx,centralizer_le (show Ltilde R a ≤ Q R a ⊔ Ltilde R a from le_sup_right) hc.2⟩

/-- The original critical comparison decomposes the full X-layer, including
its entire component-fixed factor. -/
theorem original_small_critical_X_decomposition
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
    (hsmall : (Q R z).relIndex (Z R a) < 16) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 H)) q hq hk
  let s := MovedSection.ofNormal ρ ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he⟩ := centralOmega_initial_cover R hms hp hne hQR hself hfaith
    q hq hcore ((pResidual 2 H).map q) hc hC hsq
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  obtain ⟨j,hj,hjr,hjUr,κ,_hκ,hκQ,_hκC,_hκL,hfull,f,_hf,hfconj⟩ :=
    fullX_coordinates_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq
      path.start_color F e
  let jU := j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
  have hjU : Function.Injective jU := by
    intro x y h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hj h)
  obtain ⟨ha4,hz4⟩ := original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb hsmall
  have hedge := MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith
  let rev : CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge a path.start_color
        (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δ : Z R z →* J := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = 4 :=
    (quotient_image_card _ _ _ hZA κ hκQ).trans hz4
  have hδ : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      jU (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * jU (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hfull (inclusion hZA x) v.val
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := critical_inner_root_actor rev hb
    (MSCentralOrbit.C_eq_Q R hp hQR hfaith z path.end_color) hFc s e he hC
    jU hjU hjUr δ hδ hδcard ha4
  let σ : Representation (ZMod 2) (L (K := F.Carrier))
      (Additive (omegaCenterIn (pCore 2 H))) :=
    ρ.comp (((pResidual 2 H).map q).subtype.comp e.groupEquiv.symm.toMonoidHom)
  let W : Subrepresentation σ :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule _g _v hv := s.space.apply_mem_toSubmodule _ hv }
  have hβfull (x : Z R z) (v : Additive (omegaCenterIn (pCore 2 H))) :
      j (Multiplicative.ofAdd (σ (β x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (β x)) v)) = _
    rw [hβmark]
    exact hfull (inclusion hZA x) v
  have hbound := original_small_critical_X_movement_le_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb hsmall
  exact X_eq_moving_sup_centralizer_of_movement (by omega) σ W
    (MovedSection.coverProjection s e) he (Z R z) β (hβcard.trans hFc.symm)
    hβdim hβquad j hj hjr hjUr hβfull (by rwa [hFc]) f hfconj

/-- The failed original local comparison supplies its own critical-index
premise, giving the printed X-decomposition directly. -/
theorem original_critical_X_decomposition_of_local_actor
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
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  apply original_small_critical_X_decomposition R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen_of_local_actor R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y hYZ hcentral hbad

/-- The literal adjacent-core version of the original X-decomposition. -/
theorem original_critical_X_decomposition_of_adjacent_core
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
    {t : Vertex R} (ht : Adjacent R z t) (hYQ : Y ≤ Q R t)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    X R a = U R a ⊔ (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) := by
  apply original_small_critical_X_decomposition R hms hp hne hQR hself hfaith q hq hcore
    hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen_of_adjacent_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y ht hYQ hcentral hbad

/-- The center form in source (3.3), with the literal residual-core product. -/
theorem original_critical_X_decomposition_center_form
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
    {t : Vertex R} (ht : Adjacent R z t) (hYQ : Y ≤ Q R t)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    X R a = U R a ⊔ (X R a ⊓ centerIn (Q R a ⊔ Ltilde R a)) := by
  rw [←X_inf_component_centralizer_eq_local_center]
  exact original_critical_X_decomposition_of_adjacent_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y ht hYQ hcentral hbad

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
