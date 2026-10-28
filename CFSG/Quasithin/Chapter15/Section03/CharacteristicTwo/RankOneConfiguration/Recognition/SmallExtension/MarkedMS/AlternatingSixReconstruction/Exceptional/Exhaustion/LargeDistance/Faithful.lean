module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.DistanceTwoComplete
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.FromCentralizer
public import Theory.GroupTheory.PResidual.PrimeSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# Faithful exceptional critical estimates and the remaining radius

In the original small MS pair with cubic quotient center, suppose the
initial X-action has kernel Q. Literal hexacode coordinates at each vertex
show that neither critical endpoint is a strict offender. Their displacement
indices are therefore equal and are exactly four. Uniqueness of the
hexacode offender inside an edge two-group gives a common edge-normal
critical commutator; the source Frattini premise gives the full actor bound.

Normal generation retains the cubic extension kernel E: an escaping
two-subgroup cannot disappear in E/Q. This proves failure of vertex
normality and supplies every premise of MS93 (2.3). Any critical distance
larger than two is consequently four. At its midpoint the commutator is
fixed by the local residual. Applying this to the radius generators yields
an actual nonabelian radius with residual-fixed derived subgroup.

The final applications retain the entire original commutator core and the
literal C.1.32 conclusion as alternatives to this concrete remaining radius.
The radius contradiction, the cubic initial-action kernel at larger distance,
and final natural-or-exceptional reconstruction remain with this owner.
No Sylow assumption on the radical or splitting of the fixed attachment is used.

The radius-generation proofs adapt the group-independent arguments in
BinaryCoreBound/MS93/Reduction/SectionThree/NaturalStructure/Exclusion/Radius.
Source: Meierfrankenfeld--Stellmacher (1993), (2.3), pp.857--859,
and (3.8), pp.877--879; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
namespace LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R

/-- The full hexacode action has no strict offender, including the odd coset. -/
theorem hexacode_not_strong : ¬ IsStrongFFModule Hexacode.action := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hstrong⟩ := hA.exists_bestOffender Hexacode.action
  have hcard := Hexacode.bestOffender_card B hB
  have hr : rank B = 2 := by
    have hp := hB.1.card_eq_two_pow_rank
    rw [hcard] at hp
    exact (Nat.pow_right_injective (by decide : 1 < 2)) (by simpa using hp.symm)
  have hdim := fixedCodim_add_finrank Hexacode.action B
  rw [Hexacode.bestOffender_fixedSpace_finrank B hB,Atlas.Codes.hexacode_finrank] at hdim
  have hlt := hstrong.2
  omega

/-- Coordinates on a literal moved subgroup of a finite vertex stabilizer. -/
structure HexacodeChart (a : Vertex T) where
  projection : stabilizer T a →* Atlas.Codes.HexAutomorphisms
  space : Subgroup (stabilizer T a)
  normal : space.Normal
  elementary : IsElementaryAbelian 2 space
  le_X : space.map (stabilizer T a).subtype ≤ X T a
  kernel : projection.ker = (Q T a).subgroupOf (stabilizer T a)
  equiv : letI := elementary; Additive space ≃ₗ[ZMod 2] Atlas.Codes.hexacode
  compatible : letI := normal; letI := elementary
    ∀ (g : stabilizer T a) (v : space),
      equiv (Additive.ofMul (MulAut.conjNormal g v)) =
        Hexacode.action (projection g) (equiv (Additive.ofMul v))

attribute [instance] HexacodeChart.normal HexacodeChart.elementary

/-- Every original vertex has these coordinates in the faithful-kernel branch. -/
theorem hexacodeChart_nonempty
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
    (a : Vertex T) (ha : color T a = false) : Nonempty (HexacodeChart (L := L) (R := R) a) := by
  obtain ⟨f,W,hWN,hWE,hWX,hker,φ,hφ⟩ := vertex_hexacode_model h e hz hk a ha
  exact ⟨⟨f,W,hWN,hWE,hWX,hker,φ,hφ⟩⟩

namespace HexacodeChart
variable {a : Vertex (edge L R)} (c : HexacodeChart (L := L) (R := R) a)

/-- The image uses the actual inclusion into this vertex stabilizer. -/
def image (A : Subgroup (FreeAmalgam T)) : Subgroup Atlas.Codes.HexAutomorphisms :=
  (A.subgroupOf (stabilizer T a)).map c.projection

omit [Finite G] in
theorem image_card (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    Nat.card (c.image A) = (Q T a).relIndex A := by
  rw [image,←relIndex_ker,c.kernel]
  have hi := relIndex_map_map_of_injective
    ((Q T a).subgroupOf (stabilizer T a)) (A.subgroupOf (stabilizer T a))
    (stabilizer T a).subtype_injective
  rw [map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le (show Q T a ≤ stabilizer T a from fun _ hx => hx.1)] at hi
  exact hi.symm

/-- Restricting to the recognized moved subgroup cannot increase displacement. -/
theorem fixed_index_le (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    2 ^ fixedCodim Hexacode.action (c.image A) ≤
      Offenders.displacement (X T a) A := by
  let := finite_stabilizer T a
  let H := stabilizer T a
  let E := A.subgroupOf H
  let V := (X T a).subgroupOf H
  let ρ := NormalElementaryQuotient.originalAction c.space
  have he : ∀ g v, c.equiv (ρ g v) = Hexacode.action (c.projection g) (c.equiv v) := by
    intro g v
    have hh : ρ g v = Additive.ofMul (MulAut.conjNormal g v.toMul) :=
      Additive.toMul.injective (Subtype.ext
        (NormalElementaryQuotient.originalAction_apply c.space g v))
    rw [hh,c.compatible,ofMul_toMul]
  have hd := fixedCodim_map_equivariant ρ Hexacode.action c.projection c.equiv he E
  have hi := NormalElementaryQuotient.original_fixed_index c.space E
  rw [inf_relIndex_left] at hi
  have hidx : (centralizer (E : Set H)).relIndex V =
      Offenders.displacement (X T a) A := by
    have hh := relIndex_map_map_of_injective
      (V ⊓ centralizer (E : Set H)) V H.subtype_injective
    rw [←map_inf_centralizer_of_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le (show X T a ≤ H from
        (omegaCenter_le _).trans (fun _ hx => hx.1)),
      inf_relIndex_left,inf_relIndex_left] at hh
    exact hh.symm
  have hWV : c.space ≤ V := fun v hv => c.le_X (mem_map_of_mem H.subtype hv)
  change 2 ^ fixedCodim Hexacode.action (E.map c.projection) ≤ _
  rw [←hd,←hi,←hidx]
  exact relIndex_le_of_le_right hWV
    (by exact ((centralizer (E : Set H)).subgroupOf V).index_ne_zero_of_finite)

/-- The literal opposite endpoint has a nontrivial elementary image. -/
theorem critical_image_elementary
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    IsElementaryTwo (c.image (X T b)) := by
  let : IsElementaryAbelian 2 (X T b) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((X T b).subgroupOf (stabilizer T a)) :=
    IsElementaryAbelian.comap_of_injective (stabilizer T a).subtype
      (stabilizer T a).subtype_injective _
  refine ⟨?_,IsElementaryAbelian.map c.projection⟩
  intro hbot
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hi : (Q T a).relIndex (X T b) = 1 := by
    rw [←c.image_card (X T b) hA,hbot,Nat.card_unique]
  apply hr.2
  exact ((sourceGeometry h).omega_bound b hbcol (by
    rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h)).trans
    (relIndex_eq_one.mp hi)

include c in
/-- No strict offender on the moved section gives the first displacement inequality. -/
theorem critical_displacement_le
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    Offenders.displacement (X T b) (X T a) ≤
      Offenders.displacement (X T a) (X T b) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hel := c.critical_image_elementary h e ha b hc
  have hlo : rank (c.image (X T b)) ≤ fixedCodim Hexacode.action (c.image (X T b)) :=
    Nat.le_of_not_gt (fun hlt => hexacode_not_strong ⟨_,hel,hlt⟩)
  rw [critical_displacement_eq_core_index h e a ha b hc,←c.image_card _ hA,
    hel.card_eq_two_pow_rank]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hlo).trans (c.fixed_index_le _ hA)

end HexacodeChart
variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
include h e hz hk

/-- Both actual endpoint displacements agree at every positive critical distance. -/
theorem faithful_critical_displacement_eq
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    Offenders.displacement (X T a) (X T b) =
      Offenders.displacement (X T b) (X T a) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  obtain ⟨ca⟩ := hexacodeChart_nonempty h e hz hk a ha
  obtain ⟨cb⟩ := hexacodeChart_nonempty h e hz hk b hbcol
  exact le_antisymm (cb.critical_displacement_le h e hbcol a hr)
    (ca.critical_displacement_le h e ha b hc)

/-- Every critical endpoint is the best hexacode offender, not just a selected one. -/
theorem HexacodeChart.critical_best {a : Vertex T} (c : HexacodeChart (L := L) (R := R) a)
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    IsBestOffender Hexacode.action (c.image (X T b)) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hel := c.critical_image_elementary h e ha b hc
  have hhi := c.fixed_index_le (X T b) hA
  rw [faithful_critical_displacement_eq h e hz hk a ha b hc,
    critical_displacement_eq_core_index h e a ha b hc,
    ←c.image_card _ hA,hel.card_eq_two_pow_rank] at hhi
  have hdim : fixedCodim Hexacode.action (c.image (X T b)) = rank (c.image (X T b)) :=
    le_antisymm ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hhi)
      (Nat.le_of_not_gt (fun hlt => hexacode_not_strong ⟨_,hel,hlt⟩))
  exact (isBestOffender_iff_of_not_strong _ hexacode_not_strong _).mpr ⟨hel,hdim⟩

/-- The full X displacements and both original Q-indices are four. -/
theorem faithful_critical_indices
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    (Q T a).relIndex (X T b) = 4 ∧
      (Q T b).relIndex (X T a) = 4 ∧
      Offenders.displacement (X T a) (X T b) = 4 := by
  obtain ⟨c⟩ := hexacodeChart_nonempty h e hz hk a ha
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hi : (Q T a).relIndex (X T b) = 4 := by
    rw [←c.image_card _ hA]
    exact Hexacode.bestOffender_card _ (c.critical_best h e hz hk ha b hc)
  have heq := faithful_critical_displacement_eq h e hz hk a ha b hc
  have hd : Offenders.displacement (X T a) (X T b) = 4 := heq.trans
    ((critical_displacement_eq_core_index h e a ha b hc).trans hi)
  exact ⟨hi,(critical_displacement_eq_core_index h e b hbcol a hr).symm.trans hd,hd⟩

omit hz hk in
/-- The endpoint X lies in the first edge kernel of its critical path. -/
theorem critical_X_le_first_edge
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (_hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    X T b ≤ Q T t := by
  have hbcol := critical_endpoint_color T a ha _ hc
  apply X_le_Q_of_dist_lt T (sourceGeometry h) (sourceEdgeCentralizer h e) b hbcol t
  rw [SimpleGraph.dist_comm,(sourceGeometry h).distance_constant b hbcol]
  have hd := hc.1.trans ((sourceGeometry h).distance_constant a ha)
  change (cosetGraph T).dist t b < sourceDistance h
  change (cosetGraph T).dist a b = sourceDistance h at hd
  omega

omit e hz hk in
/-- The edge kernel is a two-group without requiring the radical to be Sylow. -/
theorem edge_twoGroup
    {a t : Vertex T} (ha : color T a = false) (hat : Adjacent T a t) :
    IsPGroup 2 (Q T t) := by
  obtain ⟨g,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common T a t).mp hat
  · have he := Q_act T g (beta T)
    simp only [beta,act_hVertex,one_mul] at he
    rw [he]
    change IsPGroup 2 ((Q T (beta T)).map _)
    rw [Q_beta]
    exact (h.relative_radical.isPGroup.map (embedM T)).map _
  · cases ha

/-- The original source-(3.3) actor bound at arbitrary critical distance.
Only its literal placement and centralization premises are used. -/
theorem faithful_critical_actor_bound
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hbt : Adjacent T b t)
    (ht : (cosetGraph T).dist a t + 1 = (cosetGraph T).dist a b)
    (Y : Subgroup (FreeAmalgam T)) (hY : Y ≤ Q T t)
    (hYX : Y ≤ centralizer (X T a : Set (FreeAmalgam T))) :
    ⁅Y,X T b⁆ ≤ ⁅X T a,X T b⁆ := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  obtain ⟨c⟩ := hexacodeChart_nonempty h e hz hk b hbcol
  let H := stabilizer T b
  let j := H.subtype
  let E := (X T a).subgroupOf H
  let Y₀ := Y.subgroupOf H
  let P := (Q T t).subgroupOf H
  let V := (X T b).subgroupOf H
  have hPt : Q T t ≤ H := CriticalCriterion.edge_le_stabilizer T hbcol hbt
  have hYS : Y ≤ H := hY.trans hPt
  have hXP : X T a ≤ Q T t := critical_X_le_first_edge h e b hbcol a hr t hbt
    (by simpa only [SimpleGraph.dist_comm] using ht)
  have hXS := hXP.trans hPt
  have hVS : X T b ≤ H := (omegaCenter_le _).trans (fun _ hx => hx.1)
  have hP : IsPGroup 2 P := (edge_twoGroup h hbcol hbt).comap_subtype
  have hEY : Y₀ ≤ centralizer (E : Set H) := by
    intro y hy x hx
    exact Subtype.ext (hYX hy x hx)
  have hcomm : Y₀ ≤ centralizer ((⁅E,c.space⁆ : Subgroup H) : Set H) := by
    intro y hy z hz'
    apply Subtype.ext
    apply hYX hy
    have hh := mem_map_of_mem j hz'
    rw [map_commutator,show E.map j = X T a from map_subgroupOf_eq_of_le hXS] at hh
    exact ((commutator_mono le_rfl c.le_X).trans
      ((critical_X_commutator_le h e a ha b hc).trans inf_le_left)) hh
  have hker : c.projection.ker ≤ centralizer (V : Set H) := by
    rw [c.kernel]
    intro y hy x hx
    exact Subtype.ext ((Q_le_centralizer_X T b hy) x hx)
  have hh := HexacodeLocal.commutator_le_of_hexacode_offender
    c.projection c.space c.equiv c.compatible E Y₀ P V hP
    (fun _ hx => hXP hx) (fun _ hy => hY hy) hEY hcomm
    ((c.critical_best h e hz hk hbcol a hr).isOffender _) hker
  have hm := map_mono (f := j) hh
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hYS,
    map_subgroupOf_eq_of_le hXS,map_subgroupOf_eq_of_le hVS] at hm
  exact hm

omit hz hk in
/-- The printed Frattini condition forces centralization on the full X layer. -/
theorem critical_frattini_centralizes
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hbt : Adjacent T b t)
    (ht : (cosetGraph T).dist a t + 1 = (cosetGraph T).dist a b)
    (Y : Subgroup (FreeAmalgam T)) (hY : Y ≤ Q T t)
    (hPhi : frattini (Y ⊔ X T a : Subgroup (FreeAmalgam T)) = ⊥) :
    Y ≤ centralizer (X T a : Set (FreeAmalgam T)) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hX := critical_X_le_first_edge h e b hbcol a hr t hbt
    (by simpa only [SimpleGraph.dist_comm] using ht)
  have hJ : Y ⊔ X T a ≤ Q T t := sup_le hY hX
  let := finite_stabilizer T t
  let : Finite (Y ⊔ X T a : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion (hJ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Y ⊔ X T a : Subgroup (FreeAmalgam T))) :=
    ⟨(edge_twoGroup h hbcol hbt).to_le hJ⟩
  let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhi
  intro y hy x hx
  exact congrArg Subtype.val (mul_comm
    (⟨x,mem_sup_right hx⟩ : (Y ⊔ X T a : Subgroup (FreeAmalgam T)))
    ⟨y,mem_sup_left hy⟩)

/-- The complete source-(2.3)(c) premise in the faithful-cover case. -/
theorem faithful_commutatorControl :
    CriticalCriterion.CommutatorControl T (sourceGeometry h) := by
  intro a ha b hc
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  refine ⟨Z T b,⟨(sourceGeometry h).omega_bound b hbcol (by
    rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h),hr.2,?_⟩⟩
  intro t ht Y hY hPhi
  have hZ := (sourceGeometry h).omega_bound b hbcol (by
    rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h)
  exact ((commutator_mono le_rfl hZ).trans
    (faithful_critical_actor_bound h e hz hk a ha b hc t ht.1 ht.2 Y hY
      (critical_frattini_centralizes h e a ha b hc t ht.1 ht.2 Y hY hPhi))).trans le_sup_left

omit h e hz hk
namespace HexacodeChart
variable {a : Vertex (edge L R)} (c : HexacodeChart (L := L) (R := R) a)

omit [Finite G] in
/-- Pulling back the same marked image retains the entire vertex kernel. -/
theorem image_preimage (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    ((c.image A).comap c.projection).map (stabilizer T a).subtype = A ⊔ Q T a := by
  rw [image,comap_map_eq,Subgroup.map_sup,c.kernel,
    map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le (show Q T a ≤ stabilizer T a from fun _ hx => hx.1)]

end HexacodeChart
include h e hz hk

/-- Every endpoint through one oriented edge has the same literal kernel join. -/
theorem faithful_critical_join_common
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b)
    (d : Vertex T)
    (hd : CriticalPair T a d ((sourceGeometry h).exists_critical a ha))
    (htd : (cosetGraph T).dist t d + 1 = (cosetGraph T).dist a d) :
    X T b ⊔ Q T a = X T d ⊔ Q T a := by
  obtain ⟨c⟩ := hexacodeChart_nonempty h e hz hk a ha
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hD := critical_X_le_first_edge h e a ha d hd t hat htd
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hp : IsPGroup 2 (c.image (Q T t)) :=
    (edge_twoGroup h ha hat).comap_subtype.map c.projection
  have he := Hexacode.bestOffender_unique_in_pgroup (c.image (Q T t)) hp
    (map_mono (subgroupOf_mono _ hB)) (map_mono (subgroupOf_mono _ hD))
    (c.critical_best h e hz hk ha b hc) (c.critical_best h e hz hk ha d hd)
  have hh := congrArg (fun A : Subgroup Atlas.Codes.HexAutomorphisms =>
    (A.comap c.projection).map (stabilizer T a).subtype) he
  change ((c.image (X T b)).comap c.projection).map (stabilizer T a).subtype =
    ((c.image (X T d)).comap c.projection).map (stabilizer T a).subtype at hh
  rw [c.image_preimage _ (hB.trans hTS),c.image_preimage _ (hD.trans hTS)] at hh
  exact hh

/-- Uniqueness of the marked offender makes its whole kernel preimage edge-normal. -/
theorem faithful_critical_join_normalized
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    Q T t ≤ normalizer (X T b ⊔ Q T a : Subgroup (FreeAmalgam T)) := by
  obtain ⟨c⟩ := hexacodeChart_nonempty h e hz hk a ha
  let A := c.image (X T b)
  let P := c.image (Q T t)
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hp : IsPGroup 2 P := (edge_twoGroup h ha hat).comap_subtype.map c.projection
  have hAP : A ≤ P := map_mono (subgroupOf_mono _ hB)
  have hA := c.critical_best h e hz hk ha b hc
  have hn : P ≤ normalizer (A : Set Atlas.Codes.HexAutomorphisms) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    exact Hexacode.bestOffender_unique_in_pgroup P hp
      ((map_mono hAP).trans_eq (mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hg)))
      hAP (hA.map_conj _ g) hA
  have hn₀ : (Q T t).subgroupOf (stabilizer T a) ≤
      normalizer (A.comap c.projection : Set (stabilizer T a)) :=
    (map_le_iff_le_comap.mp hn).trans (le_normalizer_comap _)
  have hh := (map_mono (f := (stabilizer T a).subtype) hn₀).trans
    (le_normalizer_map (stabilizer T a).subtype)
  rw [map_subgroupOf_eq_of_le hTS,c.image_preimage _ (hB.trans hTS)] at hh
  exact hh

omit hz hk in
private theorem critical_commutator_join
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    ⁅X T a,X T b⁆ = ⁅X T a,X T b ⊔ Q T a⁆ := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  exact commutator_eq_of_centralizing_sup (sup_comm _ _) (Q_le_centralizer_X T a)
    ((critical_X_le_vertex h e b hbcol a hr).trans (X_normalized T a))

/-- The auxiliary commutator is normal relative to the actual edge kernel. -/
theorem faithful_critical_commutator_normal_edge
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    ((⁅X T a,X T b⁆).subgroupOf (Q T t)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [critical_commutator_join h e a ha b hc]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (faithful_critical_join_normalized h e hz hk a ha b hc t hat ht hg),
    mem_normalizer_iff_map_conj_eq.mp
      (X_normalized T a (CriticalCriterion.edge_le_stabilizer T ha hat hg))]

/-- The actual auxiliary commutators agree along each oriented critical edge. -/
theorem faithful_critical_commutator_common
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b)
    (d : Vertex T)
    (hd : CriticalPair T a d ((sourceGeometry h).exists_critical a ha))
    (htd : (cosetGraph T).dist t d + 1 = (cosetGraph T).dist a d) :
    ⁅X T a,X T b⁆ = ⁅X T a,X T d⁆ := by
  rw [critical_commutator_join h e a ha b hc,
    faithful_critical_join_common h e hz hk a ha b hc t hat ht d hd htd,
    ←critical_commutator_join h e a ha d hd]

omit hk in
/-- An escaping quadratic actor cannot have vertex-normal displacement.
The normal-generation argument retains E/Q of order three. -/
theorem initial_quadratic_not_normal
    (A : Subgroup (L ⊔ R : Subgroup G)) (hA : IsPGroup 2 A)
    (hout : ¬ A ≤ pCore 2 (L ⊔ R : Subgroup G))
    (hquad : ⁅centralOmega L R,A⁆ ≤ centralizer (A : Set (L ⊔ R : Subgroup G))) :
    ¬ (⁅centralOmega L R,A⁆).Normal := by
  intro hD
  let M := (L ⊔ R : Subgroup G)
  let K := L.subgroupOf (L ⊔ R)
  let Q := pCore 2 M
  let W := centralOmega L R
  let D := ⁅W,A⁆
  let : D.Normal := hD
  have hQW : Q ≤ centralizer (W : Set M) := by
    intro q hq w hw
    exact (((mem_omegaCenterIn_iff Q w).mp hw).2.1 q hq).symm
  have hKC : K ≤ centralizer (D : Set M) :=
    component_le_normal_of_two_subgroup h e hz _ A
      (hQW.trans (centralizer_le (commutator_le_left W A))) hA hout
      (le_centralizer_iff.mp hquad)
  let q := QuotientGroup.mk' D
  let C := (centralizer (W.map q : Set (M ⧸ D))).comap q
  let : (W.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective D)
  have hC (B : Subgroup M) : B ≤ C ↔ ⁅W,B⁆ ≤ D := by
    change B ≤ (centralizer (W.map q : Set (M ⧸ D))).comap q ↔ _
    rw [←map_le_iff_le_comap,←le_centralizer_iff,
      ←commutator_eq_bot_iff_le_centralizer,←map_commutator,
      Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hQC : Q ≤ C := (hC Q).mpr (by
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hQW]
    exact bot_le)
  have hWK : ⁅W,K⁆ ≤ D := (hC K).mp
    (component_le_normal_of_two_subgroup h e hz C A hQC hA hout ((hC A).mpr le_rfl))
  have hzero : ⁅W,K⁆ = ⊥ := by
    have hid := commutator_isPPerfect_idempotent K W h.relative_twoPerfect
      (IsElementaryAbelian.isPGroup 2 W) le_normalizer_of_normal
    apply le_bot_iff.mp
    rw [←hid]
    exact (commutator_mono hWK le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKC)).le
  have hcent : K ≤ centralizer (W : Set M) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  apply ChapterC.MSCentralOrbit.component_not_centralizes_omegaOrbit K (edge L R)
    h.relative_radical.isPGroup h.relative_radical_ne_bot h.relative_product
    h.relative_characteristic
  exact hcent.trans (centralizer_le
    (ChapterC.MSCentralOrbit.omegaOrbit_le_centralOmega _ h.relative_radical.twoCore_le
      h.relative_self_centralizing))

omit hk in
private theorem critical_not_normal_base
    (b : Vertex T)
    (hc : CriticalPair T (alpha T) b ((sourceGeometry h).exists_critical (alpha T) rfl)) :
    ¬ ((⁅X T (alpha T),X T b⁆).subgroupOf (stabilizer T (alpha T))).Normal := by
  intro hD
  let M := (L ⊔ R : Subgroup G)
  let f := embedM T
  let A := (X T b).comap f
  let D := ⁅centralOmega L R,A⁆
  have hbcol := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) b hbcol hc
  have hAS := critical_X_le_vertex h e b hbcol (alpha T) hr
  have hAm : A.map f = X T b := map_comap_eq_self (hAS.trans_eq (stabilizer_m_base T))
  have hDm : D.map f = ⁅X T (alpha T),X T b⁆ := by
    rw [map_commutator,hAm,←graph_X h]
  have hDn : D.Normal := by
    constructor
    intro x hx m
    apply (mem_map_iff_mem (f := f) (embedM_injective T)).mp
    rw [hDm]
    have hn := (normal_subgroupOf_iff_le_normalizer
      (((critical_X_commutator_le h e (alpha T) rfl b hc).trans inf_le_left).trans
        ((omegaCenter_le _).trans (fun _ hx => hx.1)))).mp hD
    have hh := le_normalizer_iff.mp hn (f m)
      ((stabilizer_m_base T).symm ▸ ⟨m,rfl⟩) (f x)
      (hDm ▸ mem_map_of_mem f hx)
    simpa only [map_mul,map_inv] using hh
  have hA : IsPGroup 2 A := by
    let : IsElementaryAbelian 2 (X T b) := omegaCenter_elementary _
    let : IsElementaryAbelian 2 A :=
      IsElementaryAbelian.comap_of_injective f (embedM_injective T) _
    exact IsElementaryAbelian.isPGroup 2 A
  have hout : ¬ A ≤ pCore 2 M := by
    intro hh
    apply hr.2
    have hm := map_mono (f := f) hh
    rw [hAm,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hm
    exact ((sourceGeometry h).omega_bound b hbcol (by
      rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h)).trans hm
  have hquad : D ≤ centralizer (A : Set M) := by
    intro d hd x hx
    apply embedM_injective T
    have hdX : f d ∈ X T b :=
      ((critical_X_commutator_le h e (alpha T) rfl b hc).trans inf_le_right)
        (hDm ▸ mem_map_of_mem f hd)
    let : IsElementaryAbelian 2 (X T b) := omegaCenter_elementary _
    have hh := congrArg Subtype.val
      (mul_comm (⟨f x,hx⟩ : X T b) (⟨f d,hdX⟩ : X T b))
    change f x * f d = f d * f x at hh
    simpa only [f,map_mul] using hh
  exact initial_quadratic_not_normal h e hz A hA hout hquad hDn

omit hk in
/-- The critical X-commutator fails vertex normality with either action kernel. -/
theorem critical_commutator_not_normal_vertex
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    ¬ ((⁅X T a,X T b⁆).subgroupOf (stabilizer T a)).Normal := by
  intro hN
  obtain ⟨g,hga⟩ := exists_mVertex_of_color T ha
  have hg : act T g⁻¹ a = alpha T := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have hgc : color T (act T g⁻¹ a) = false := by rw [hg]; rfl
  have hc' := (criticalPair_act_iff T g⁻¹ a b
    ((sourceGeometry h).exists_critical a ha)
    ((sourceGeometry h).exists_critical (act T g⁻¹ a) hgc)).mpr hc
  have hnorm := (normal_subgroupOf_iff_le_normalizer
    (((critical_X_commutator_le h e a ha b hc).trans inf_le_left).trans
      ((omegaCenter_le _).trans (fun _ hx => hx.1)))).mp hN
  have hm := (map_mono (f := (MulAut.conj g).toMonoidHom) hnorm).trans
    (le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hgg : (g⁻¹)⁻¹ = g := inv_inv g
  rw [map_commutator,←hgg,←stabilizer_act,←X_act,←X_act,hg] at hm
  apply critical_not_normal_base h e hz (act T g⁻¹ b) (by simpa only [hg] using hc')
  exact normal_subgroupOf_of_le_normalizer hm

omit hk in
/-- Source (2.3)(b) with the original radical and cubic kernel retained. -/
theorem generation : CriticalCriterion.Generation T := by
  apply CriticalCriterion.Generation.of_edge T (alpha T) (beta T) rfl (base_adjacent T)
  intro x hx hout
  let M := (L ⊔ R : Subgroup G)
  let N := NormalizerTransfer.conjugatesIn (zpowers x) (Mbar T)
  have hxR : x ∈ (edge L R).map (embedM T) := by simpa only [Q_beta] using hx
  have hNM : N ≤ Mbar T := NormalizerTransfer.conjugatesIn_le _ _
    ((zpowers_le.mpr hxR).trans (map_le_range _ _))
  have hxN : x ∈ N := by
    apply le_iSup (fun g : Mbar T => NormalizerTransfer.rightConjugate (zpowers x) g) (1 : Mbar T)
    exact ⟨x,mem_zpowers x,by simp⟩
  have hnN : Mbar T ≤ normalizer (N : Set (FreeAmalgam T)) :=
    NormalizerTransfer.conjugatesIn_normalized _ _
  let N₀ := N.comap (embedM T)
  let : N₀.Normal := by
    constructor
    intro n hn m
    show embedM T (m*n*m⁻¹) ∈ N
    simpa only [map_mul,map_inv] using
      le_normalizer_iff.mp hnN
        (embedM T m) ⟨m,rfl⟩ (embedM T n) hn
  obtain ⟨y,hy,rfl⟩ := hxR
  have hQ : y ∉ pCore 2 M := by
    intro hyQ
    apply hout
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact mem_map_of_mem (embedM T) hyQ
  have hK : L.subgroupOf (L ⊔ R) ≤ N₀ ⊔ pCore 2 M := by
    apply component_le_normal_of_two_subgroup h e hz _ (zpowers y) le_sup_right
    · exact h.relative_radical.isPGroup.to_le (zpowers_le.mpr hy)
    · exact fun hh => hQ (hh (mem_zpowers y))
    · exact (zpowers_le.mpr (show y ∈ N₀ from hxN)).trans le_sup_left
  have htop : N₀ ⊔ edge L R = ⊤ := by
    apply top_unique
    rw [←(codisjoint_subgroupOf_sup L R).eq_top]
    exact sup_le (hK.trans (sup_le_sup_left h.relative_radical.twoCore_le N₀)) le_sup_right
  have hm := congrArg (Subgroup.map (embedM T)) htop
  rw [Subgroup.map_sup,map_comap_eq_self (show N ≤ (embedM T).range from hNM),
    ←MonoidHom.range_eq_map] at hm
  rw [show stabilizer T (alpha T) = Mbar T from stabilizer_m_base T,Q_beta]
  exact hm

/-- Every literal clause of source (2.3)(d) is now discharged in the faithful branch. -/
theorem faithful_edgeWitness
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    CriticalCriterion.EdgeWitness T (sourceGeometry h) a t ⁅X T a,X T b⁆ := by
  refine ⟨(critical_X_commutator_le h e a ha b hc).trans inf_le_left,
    faithful_critical_commutator_normal_edge h e hz hk a ha b hc t hat ht,
    critical_commutator_not_normal_vertex h e hz a ha b hc,?_⟩
  intro ha' d hd htd
  exact (faithful_critical_commutator_common h e hz hk a ha b hc t hat ht d hd (by
    rw [hd.1,(sourceGeometry h).distance_constant a ha']
    exact htd)).le

/-- In the faithful hexacode branch a distance exceeding two is exactly four. -/
theorem faithful_distance_eq_four (hb : 2 < sourceDistance h) : sourceDistance h = 4 := by
  obtain ⟨b,hc⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one T (alpha T) b (by
    rw [hc.1,(sourceGeometry h).distance_constant (alpha T) rfl]
    exact sourceDistance_pos h)
  exact CriticalCriterion.FromCentralizer.distance_eq_four T (sourceEdgeCentralizer h e)
    (sourceGeometry h) hb (generation h e hz) (faithful_commutatorControl h e hz hk)
    (alpha T) rfl b hc t hat ht _ (faithful_edgeWitness h e hz hk (alpha T) rfl b hc t hat ht)

/-- The same actual auxiliary commutator is normal in the midpoint stabilizer. -/
theorem faithful_critical_commutator_normal_midpoint
    (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hac : (cosetGraph T).dist a c = 2)
    (hcb : (cosetGraph T).dist c b = 2) :
    ⁅X T a,X T b⁆ ≤ stabilizer T c ∧
      ((⁅X T a,X T b⁆).subgroupOf (stabilizer T c)).Normal := by
  have hd : (cosetGraph T).dist a b = 4 :=
    (hc.1.trans ((sourceGeometry h).distance_constant a ha)).trans
      (faithful_distance_eq_four h e hz hk hb)
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two T a c hac
  have ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := b)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := b)
    omega
  exact CriticalCriterion.FromCentralizer.normal_at_second T (sourceEdgeCentralizer h e)
    (sourceGeometry h) hb (generation h e hz) (faithful_commutatorControl h e hz hk)
    a ha b hc t c hat hct hac (by omega) _ (faithful_edgeWitness h e hz hk a ha b hc t hat ht)

/-- All other distances already give exhaustion of the entire original core.
The distance-four radius contradiction remains with this reconstruction owner. -/
theorem faithful_coreExhaustion_or_distance_four : CoreExhaustion L R ∨ sourceDistance h = 4 := by
  by_cases hb : 2 < sourceDistance h
  · exact Or.inr (faithful_distance_eq_four h e hz hk hb)
  · exact Or.inl (coreExhaustion_of_distanceTwo h e hz
      (sourceDistance_eq_two h (Nat.le_of_not_gt hb)))

/-- Literal C.1.32 application: the only remaining faithful exceptional case
is the original distance-four graph, with no action-estimate premises. -/
theorem faithful_rankTwo_or_distance_four : RankTwoAlternatives L R ∨ sourceDistance h = 4 :=
  (faithful_coreExhaustion_or_distance_four h e hz hk).imp (rankTwo_of_exhaustion h e hz) id

omit hk in
/-- Perfectness removes the two-core from normal generation; the cubic
extension quotient is excluded only for the escaping two-subgroup. -/
theorem component_le_normal_of_escaping_two_subgroup
    (N A : Subgroup (L ⊔ R : Subgroup G)) [N.Normal]
    (hA : IsPGroup 2 A) (hout : ¬ A ≤ pCore 2 (L ⊔ R : Subgroup G))
    (hAN : A ≤ N) : L.subgroupOf (L ⊔ R) ≤ N := by
  have hgen := component_le_normal_of_two_subgroup h e hz
    (N ⊔ pCore 2 (L ⊔ R : Subgroup G)) A le_sup_right hA hout
    (hAN.trans le_sup_left)
  exact le_normal_of_isPPerfect_of_le_sup_pGroup _ N (pCore 2 (L ⊔ R : Subgroup G))
    h.relative_twoPerfect pCore_isPGroup hgen

omit hk in
/-- Relative normality and an escaping two-subgroup force the literal
local residual into the normal subgroup, at every original graph vertex. -/
theorem residual_le_normal_of_escaping_two_subgroup
    (a : Vertex T) (ha : color T a = false)
    (N A : Subgroup (FreeAmalgam T)) (hNS : N ≤ stabilizer T a)
    (hn : (N.subgroupOf (stabilizer T a)).Normal)
    (hA : IsPGroup 2 A) (hout : ¬ A ≤ Q T a) (hAN : A ≤ N) :
    Ltilde T a ≤ N := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective.comp (embedM_injective T)
  have hrange : f.range = stabilizer T (mVertex T g) := by
    rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex T g).symm
  have hQ : (pCore 2 (L ⊔ R : Subgroup G)).map f = Q T (mVertex T g) := by
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    simpa only [alpha,act_mVertex,one_mul] using (Q_act T g (alpha T)).symm
  have hK : (L.subgroupOf (L ⊔ R)).map f = Ltilde T (mVertex T g) := by
    rw [←map_map,←graph_component h]
    simpa only [alpha,act_mVertex,one_mul] using (Ltilde_act T g (alpha T)).symm
  let N₀ := N.comap f
  let A₀ := A.comap f
  have hNm : N₀.map f = N := map_comap_eq_self (hNS.trans_eq hrange.symm)
  have hAm : A₀.map f = A := map_comap_eq_self ((hAN.trans hNS).trans_eq hrange.symm)
  let : N₀.Normal := by
    constructor
    intro n hn₀ m
    have hn' := (normal_subgroupOf_iff_le_normalizer hNS).mp hn
    change f (m*n*m⁻¹) ∈ N
    simpa only [map_mul,map_inv] using le_normalizer_iff.mp hn' (f m)
      (hrange ▸ ⟨m,rfl⟩) (f n) hn₀
  have hA₀ : IsPGroup 2 A₀ := hA.of_injective (f.subgroupComap A)
    (fun _ _ hh => Subtype.ext (hf (congrArg Subtype.val hh)))
  have hout₀ : ¬ A₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    intro hh
    apply hout
    have hm := map_mono (f := f) hh
    rwa [hAm,hQ] at hm
  have hh := map_mono (f := f)
    (component_le_normal_of_escaping_two_subgroup h e hz N₀ A₀ hA₀ hout₀ (comap_mono hAN))
  rwa [hK,hNm] at hh

/-- Midpoint normality makes the auxiliary commutator fixed by the original
midpoint residual, retaining the relative centralizer convention. -/
theorem faithful_critical_commutator_fixed_midpoint
    (hb : 2 < sourceDistance h)
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hcCol : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    ⁅X T a,X T b⁆ ≤ fixedCore T c := by
  let A := ⁅X T a,X T b⁆
  let S := stabilizer T c
  obtain ⟨hAS,hAn⟩ := faithful_critical_commutator_normal_midpoint h e hz hk hb a ha b hc c hac hcb
  have hAX : A ≤ X T a := (critical_X_commutator_le h e a ha b hc).trans inf_le_left
  have hAQ : A ≤ Q T c := hAX.trans
    (X_le_Q_of_dist_lt T (sourceGeometry h) (sourceEdgeCentralizer h e) a ha c (by
      rw [(sourceGeometry h).distance_constant a ha]
      change _ < sourceDistance h
      omega))
  let C := S ⊓ centralizer (A : Set (FreeAmalgam T))
  have hCn : (C.subgroupOf S).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hg),
      mem_normalizer_iff_map_conj_eq.mp
        ((((normal_subgroupOf_iff_le_normalizer hAS).mp hAn).trans
          (normalizer_le_normalizer_centralizer A)) hg)]
  have hQC : Q T a ≤ C := le_inf
    (Q_le_stabilizer_of_dist_two T a c ha hac)
    ((Q_le_centralizer_X T a).trans (centralizer_le hAX))
  have hQnot : ¬ Q T a ≤ Q T c := by
    intro hle
    let := finite_stabilizer T c
    let : Finite (Q T c) := Finite.of_injective
      (inclusion (show Q T c ≤ S from fun _ hx => hx.1)) (inclusion_injective _)
    have hcard : Nat.card (Q T c) = Nat.card (Q T a) := by
      obtain ⟨ga,rfl⟩ := exists_mVertex_of_color T ha
      obtain ⟨gc,rfl⟩ := exists_mVertex_of_color T hcCol
      have hqa := Q_act T ga (alpha T)
      have hqc := Q_act T gc (alpha T)
      simp only [alpha,act_mVertex,one_mul] at hqa hqc
      rw [hqa,hqc,card_map_of_injective (MulAut.conj gc⁻¹).injective,
        card_map_of_injective (MulAut.conj ga⁻¹).injective]
    have heq := eq_of_le_of_card_ge hle hcard.le
    have hX : X T a = X T c := congrArg omegaCenter heq
    have hZ := (sourceGeometry h).omega_bound a ha (by
      rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    apply hc.2
    rw [hX] at hZ
    exact hZ.trans (X_le_Q_of_dist_lt T (sourceGeometry h) (sourceEdgeCentralizer h e)
      c hcCol b (by
        rw [(sourceGeometry h).distance_constant c hcCol]
        change (cosetGraph T).dist c b < sourceDistance h
        omega))
  have hLC := residual_le_normal_of_escaping_two_subgroup h e hz c hcCol C (Q T a)
    inf_le_left hCn (Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le a ha)
    hQnot hQC
  exact le_inf hAQ (le_centralizer_iff.mp (hLC.trans inf_le_right))


omit h e hz hk
open scoped commutatorElement
omit [Finite G] in
private theorem adjacent_Z_le {a t : Vertex T} (ha : color T a = false)
    (hat : Adjacent T a t) : Z T t ≤ Z T a := by
  have ht : color T t ≠ false := fun ht => adjacent_color_ne T hat (ha.trans ht.symm)
  rw [Z, if_neg ht, Z, if_pos ha]
  exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)

omit [Finite G] in
/-- The odd-color generators of the radius group are redundant. -/
private theorem radius_le_of_m_ball {a : Vertex T} (ha : color T a = false)
    (K : Subgroup (FreeAmalgam T))
    (hK : ∀ d, color T d = false → (cosetGraph T).dist d a ≤ 2 → Z T d ≤ K) :
    V T a ≤ K := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  by_cases hc : color T d = false
  · exact hK d hc hd
  · obtain ⟨w, hw⟩ := (cosetGraph_connected T).exists_walk_length_eq_dist d a
    have hn : ¬ Even ((cosetGraph T).dist d a) := by
      rw [← hw, walk_even_iff_color_eq, ha]
      exact hc
    rw [Nat.even_iff] at hn
    have hd' : (cosetGraph T).dist d a = 1 := by omega
    have hadj : Adjacent T a d := adjacent_symm T
      ((cosetGraph_adj T _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hd'))
    exact (adjacent_Z_le ha hadj).trans (hK a ha (by simp))


omit [Finite G] in
private theorem fixedCore_normalized (a : Vertex T) :
    stabilizer T a ≤ normalizer (fixedCore T a : Set (FreeAmalgam T)) := by
  have heq : (fixedCore T a).subgroupOf (stabilizer T a) =
      (Q T a).subgroupOf (stabilizer T a) ⊓
        centralizer (pResidual 2 (stabilizer T a) : Set (stabilizer T a)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro l hl
      apply Subtype.ext
      exact hx.2 l (mem_map_of_mem (stabilizer T a).subtype hl)
    · rintro ⟨hx,hc⟩
      refine ⟨hx, ?_⟩
      rintro _ ⟨l,hl,rfl⟩
      exact congrArg Subtype.val (hc l hl)
  apply (normal_subgroupOf_iff_le_normalizer
    (show fixedCore T a ≤ stabilizer T a from inf_le_left.trans (fun _ hx => hx.1))).mp
  rw [heq]
  let := Q_normal T a
  infer_instance

omit [Finite G] in
private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer D) (hc : ∀ i, ⁅A i,Y⁆ ≤ D) :
    ⁅⨆ i, A i,Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)


include h e hz hk

/-- All derived radius generators lie in the original residual-fixed core.
Only pairs at the critical distance can contribute a nontrivial commutator. -/
theorem faithful_radius_derived_le_fixed
    (hb : 2 < sourceDistance h) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,V T a⁆ ≤ fixedCore T a := by
  have hfour := faithful_distance_eq_four h e hz hk hb
  let geometry := sourceGeometry h
  let I := {d : Vertex T // color T d = false ∧ (cosetGraph T).dist d a ≤ 2}
  have heq : V T a = ⨆ d : I, Z T d.val := by
    apply le_antisymm
    · apply radius_le_of_m_ball ha
      intro d hd hdist
      exact le_iSup_of_le (⟨d,hd,hdist⟩ : I) le_rfl
    · apply iSup_le
      intro d
      exact le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
  have hn : V T a ≤ normalizer (fixedCore T a : Set (FreeAmalgam T)) :=
    ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)).trans (fixedCore_normalized a)
  rw [heq] at hn ⊢
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro d
  rw [commutator_comm]
  apply commutator_iSup_le_of_normalizes _ _ _ hn
  intro f
  by_cases hZQ : Z T f.val ≤ Q T d.val
  · exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hZQ.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp
          (geometry.centralizes d.val d.property.1))))).le.trans bot_le
  have hmin := criticalDistance_le T f.val (geometry.exists_critical f.val f.property.1) hZQ
  have hfcrit : criticalDistance T f.val (geometry.exists_critical f.val f.property.1) = 4 :=
    (geometry.distance_constant f.val f.property.1).trans hfour
  have hdcrit : criticalDistance T d.val (geometry.exists_critical d.val d.property.1) = 4 :=
    (geometry.distance_constant d.val d.property.1).trans hfour
  rw [hfcrit] at hmin
  have hda : (cosetGraph T).dist a d.val ≤ 2 := by
    simpa only [SimpleGraph.dist_comm] using d.property.2
  have htri := (cosetGraph_connected T).dist_triangle (u := f.val) (v := a) (w := d.val)
  have hd : (cosetGraph T).dist f.val d.val = 4 := by omega
  have hc : CriticalPair T f.val d.val (geometry.exists_critical f.val f.property.1) :=
    ⟨by rw [hfcrit]; exact hd,hZQ⟩
  have hZXf := geometry.omega_bound f.val f.property.1 (by rw [hfcrit]; decide)
  have hZXd := geometry.omega_bound d.val d.property.1 (by rw [hdcrit]; decide)
  exact (commutator_mono hZXf hZXd).trans
    (faithful_critical_commutator_fixed_midpoint h e hz hk hb f.val f.property.1 d.val hc
      a ha (by omega) (by omega))

omit hz hk in
/-- The literal critical midpoint radius is nonabelian. This is the
remaining radius contradiction's nontriviality premise, not an assumed model. -/
theorem faithful_midpoint_radius_not_commutative
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) (c : Vertex T)
    (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    ¬ IsMulCommutative (V T c) := by
  intro hcomm
  have hZa : Z T a ≤ V T c := le_iSup_of_le a (le_iSup_of_le hac.le le_rfl)
  have hZb : Z T b ≤ V T c := le_iSup_of_le b (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcb]) le_rfl)
  exact critical_noncommutation T (sourceGeometry h) (sourceEdgeCentralizer h e) a ha
    (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h) hc
    (commutator_eq_bot_iff_le_centralizer.mpr (hZa.trans
      ((le_centralizer_iff_isMulCommutative.mpr hcomm).trans (centralizer_le hZb))))

/-- The remaining faithful branch supplies an actual nonabelian radius
whose derived subgroup is fixed by the same literal local residual. -/
theorem faithful_nonabelian_radius
    (hb : 2 < sourceDistance h) :
    ∃ c : Vertex T, color T c = false ∧
      ¬ IsMulCommutative (V T c) ∧ ⁅V T c,V T c⁆ ≤ fixedCore T c := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (faithful_distance_eq_four h e hz hk hb)
  have hle : 2 ≤ p.walk.length := by omega
  let c := p.walk.getVert 2
  have hc : color T c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph T).dist (alpha T) c = 2 := p.dist_start hle
  have hcb : (cosetGraph T).dist c b = 2 := by rw [p.dist_end,hl]
  exact ⟨c,hc,faithful_midpoint_radius_not_commutative h e (alpha T) rfl b hcrit c hac hcb,
    faithful_radius_derived_le_fixed h e hz hk hb c hc⟩

/-- Whole-core exhaustion or the concrete radius obstruction for the faithful
exceptional branch. Final exclusion of that radius remains in this task. -/
theorem faithful_coreExhaustion_or_nonabelian_radius :
    CoreExhaustion L R ∨ ∃ c : Vertex T, color T c = false ∧
      ¬ IsMulCommutative (V T c) ∧ ⁅V T c,V T c⁆ ≤ fixedCore T c := by
  by_cases hb : 2 < sourceDistance h
  · exact Or.inr (faithful_nonabelian_radius h e hz hk hb)
  · exact Or.inl (coreExhaustion_of_distanceTwo h e hz
      (sourceDistance_eq_two h (Nat.le_of_not_gt hb)))

/-- The unchanged rank-two conclusion or its literal outstanding radius case. -/
theorem faithful_rankTwo_or_nonabelian_radius :
    RankTwoAlternatives L R ∨ ∃ c : Vertex T, color T c = false ∧
      ¬ IsMulCommutative (V T c) ∧ ⁅V T c,V T c⁆ ≤ fixedCore T c :=
  (faithful_coreExhaustion_or_nonabelian_radius h e hz hk).imp
    (rankTwo_of_exhaustion h e hz) id

end LargeDistance
end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
