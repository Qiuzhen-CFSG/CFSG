module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Centralizer

/-!
# Critical estimates and the cubic even-action radius

Retain the original extension kernel E, with E/Q of order three, and suppose
its natural quotient actor is A₆. The natural four-space has no strict even
offender. Critical reciprocity therefore gives exact full-X displacement
four. Uniqueness and self-centralization of that offender supply the actual
source-(2.3)(c,d) controls. Inverse images throughout this proof retain E;
the kernel is removed only from commutators because it centralizes all of X.

The original critical distance is four. Its auxiliary commutator is normal
at the midpoint and fixed by the local residual. Radius generation then
places the full radius derived group in the residual-fixed core, while
critical noncommutation proves that the radius itself is nonabelian.
The whole-core and literal rank-two applications retain this concrete
radius case and the full symmetric larger-distance case as alternatives.
Their exclusion, and final natural/exceptional assembly, remain with
qt-e-ms-small-a6-reconstruction; no additional callback is introduced.

The graph argument adapts the existing Natural.Exhaustion derived-action
estimates and the faithful exceptional radius calculation, preserving the
cubic initial kernel and the entire intrinsic blockU.
Source: Meierfrankenfeld--Stellmacher (1993), (2.3), printed pp.857--859,
and (3.8), printed pp.877--879; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEven
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "ρ" => BinaryPermutation.naturalRepresentation (Fin 6)

/-- Coordinates retain the actual embedding of the original vertex group. -/
structure Chart (a : Vertex T) where
  embedding : M →* FreeAmalgam T
  injective : Function.Injective embedding
  range_eq : embedding.range = stabilizer T a
  map_X : (centralOmega L R).map embedding = X T a

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "π" => CubicAction.projection h e hz hk

include h in
theorem chart_nonempty (a : Vertex T) (ha : color T a = false) :
    Nonempty (Chart (L := L) (R := R) a) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T ha
  let f := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
  refine ⟨⟨f,(MulAut.conj g⁻¹).injective.comp (embedM_injective T),?_,?_⟩⟩
  · rw [MonoidHom.range_comp]
    change (Mbar T).map _ = _
    rw [←stabilizer_m_base T]
    simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act T g (alpha T)).symm
  · rw [←map_map,←graph_X h]
    simpa only [alpha,act_mVertex,one_mul] using (X_act T g (alpha T)).symm

namespace Chart
variable {a : Vertex (edge L R)} (c : Chart (L := L) (R := R) a)
@[expose] def image (A : Subgroup (FreeAmalgam T)) : Subgroup (Equiv.Perm (Fin 6)) :=
  (A.comap c.embedding).map π
@[expose] def kernel : Subgroup (FreeAmalgam T) := (extensionKernel h).map c.embedding

include c in
omit [Finite G] in
private theorem centralizer_comap (A : Subgroup (FreeAmalgam T))
    (hA : A ≤ stabilizer T a) :
    (centralizer (A : Set (FreeAmalgam T))).comap c.embedding =
      centralizer (A.comap c.embedding : Set M) := by
  have hm : (A.comap c.embedding).map c.embedding = A :=
    map_comap_eq_self (hA.trans_eq c.range_eq.symm)
  ext x
  constructor
  · intro hx y hy
    apply c.injective
    simpa only [map_mul] using hx _ hy
  · intro hx y hy
    rw [←hm] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [map_mul] using congrArg c.embedding (hx z hz)

/-- Image order measures displacement on the whole X, including its fixed attachment. -/
theorem image_card (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    Nat.card (c.image h e hz hk A) = Offenders.displacement A (X T a) := by
  have hm : (A.comap c.embedding).map c.embedding = A :=
    map_comap_eq_self (hA.trans_eq c.range_eq.symm)
  have hX : (X T a).comap c.embedding = centralOmega L R := by
    rw [←c.map_X,comap_map_eq_self_of_injective c.injective]
  have hcent := c.centralizer_comap (X T a)
    ((omegaCenter_le _).trans (fun _ hx => hx.1))
  rw [hX] at hcent
  rw [image,←relIndex_ker,CubicAction.projection_kernel,←hk]
  change (centralizer (centralOmega L R : Set M)).relIndex (A.comap c.embedding) = _
  rw [←hcent,relIndex_comap,hm]
  rfl

/-- The literal natural quotient cannot increase full-X displacement. -/
theorem fixed_index_le (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    2 ^ fixedCodim ρ (c.image h e hz hk A) ≤ Offenders.displacement (X T a) A := by
  have hi := CubicAction.natural_index_le h e hz hk (A.comap c.embedding)
  rw [←c.centralizer_comap A hA,relIndex_comap,c.map_X] at hi
  exact hi

include hk in
omit [Finite G] in
/-- The original cubic kernel centralizes the entire X-layer. -/
theorem kernel_centralizes : c.kernel h ≤ centralizer (X T a : Set (FreeAmalgam T)) := by
  rw [kernel,←hk,←c.map_X]
  exact map_centralizer_le_centralizer_image _ _

/-- The preimage retains E, including its odd quotient over Q. -/
theorem image_preimage (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    ((c.image h e hz hk A).comap π).map c.embedding = A ⊔ c.kernel h := by
  rw [image,comap_map_eq,Subgroup.map_sup,CubicAction.projection_kernel,
    map_comap_eq_self (hA.trans_eq c.range_eq.symm)]
  rfl

/-- A noncommuting critical endpoint has a nonzero elementary image. -/
theorem critical_image_elementary (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    IsElementaryTwo (c.image h e hz hk (X T b)) := by
  let : IsElementaryAbelian 2 (X T b) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 ((X T b).comap c.embedding) :=
    IsElementaryAbelian.comap_of_injective c.embedding c.injective _
  refine ⟨?_,IsElementaryAbelian.map π⟩
  intro hbot
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hi : (Q T a).relIndex (X T b) = 1 := by
    rw [←critical_displacement_eq_core_index h e a ha b hc,←c.image_card h e hz hk _ hA,hbot,card_bot]
  exact hr.2 (((sourceGeometry h).omega_bound b hbcol (by
    rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h)).trans
    (relIndex_eq_one.mp hi))

private theorem even_rank_le_codim (A : Subgroup (Equiv.Perm (Fin 6)))
    (ha : A ≤ alternatingGroup (Fin 6)) (he : IsElementaryTwo A) :
    rank A ≤ fixedCodim ρ A := by
  by_contra hh
  have ho : IsOffender ρ A := ⟨he,(lt_of_not_ge hh).le⟩
  have hc := ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_card ha ho
  have hd := ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_codim ha ho
  have hr : rank A = 2 := by change Nat.log 2 (Nat.card A) = 2; rw [hc]; decide
  exact hh (hr.trans hd.symm).le

include c in
/-- Even natural images cannot be strict offenders on the full initial layer. -/
theorem critical_displacement_le (himage : (π).range = alternatingGroup (Fin 6))
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    Offenders.displacement (X T b) (X T a) ≤ Offenders.displacement (X T a) (X T b) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hel := c.critical_image_elementary h e hz hk ha b hc
  have heven : c.image h e hz hk (X T b) ≤ alternatingGroup (Fin 6) := by
    rw [←himage]; exact map_le_range _ _
  rw [←c.image_card h e hz hk _ hA,hel.card_eq_two_pow_rank]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2)
    (even_rank_le_codim _ heven hel)).trans (c.fixed_index_le h e hz hk _ hA)
end Chart

include h e hz hk in
/-- Reciprocal critical indices are equal with the cubic initial kernel retained. -/
theorem critical_displacement_eq (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    Offenders.displacement (X T a) (X T b) = Offenders.displacement (X T b) (X T a) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  obtain ⟨ca⟩ := chart_nonempty h a ha
  obtain ⟨cb⟩ := chart_nonempty h b hbcol
  exact le_antisymm (cb.critical_displacement_le h e hz hk himage hbcol a hr)
    (ca.critical_displacement_le h e hz hk himage ha b hc)

namespace Chart
variable {a : Vertex (edge L R)} (c : Chart (L := L) (R := R) a)

/-- Every critical image is an offender in the same original even marking. -/
theorem critical_offender (himage : (π).range = alternatingGroup (Fin 6))
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    IsOffender ρ (c.image h e hz hk (X T b)) := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have hel := c.critical_image_elementary h e hz hk ha b hc
  refine ⟨hel,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ?_⟩
  rw [←hel.card_eq_two_pow_rank,c.image_card h e hz hk _ hA,
    ←critical_displacement_eq h e hz hk himage a ha b hc]
  exact c.fixed_index_le h e hz hk _ hA

include hk in
omit [Finite G] in
/-- The odd kernel contributes no commutator on X. -/
theorem commutator_join (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a) :
    ⁅X T a,A⁆ = ⁅X T a,A ⊔ c.kernel h⁆ :=
  commutator_eq_of_centralizing_sup (sup_comm _ _) (c.kernel_centralizes h hk)
    (hA.trans (X_normalized T a))

end Chart

include h e hz hk in
/-- Both full-X displacements and both literal Q-indices are exactly four. -/
theorem critical_indices (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha)) :
    (Q T a).relIndex (X T b) = 4 ∧ (Q T b).relIndex (X T a) = 4 ∧
      Offenders.displacement (X T a) (X T b) = 4 := by
  obtain ⟨c⟩ := chart_nonempty h a ha
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hA := critical_X_le_vertex h e b hbcol a hr
  have heven : c.image h e hz hk (X T b) ≤ alternatingGroup (Fin 6) := by
    rw [←himage]; exact map_le_range _ _
  have hi : (Q T a).relIndex (X T b) = 4 := by
    rw [←critical_displacement_eq_core_index h e a ha b hc,←c.image_card h e hz hk _ hA]
    exact ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_card heven
      (c.critical_offender h e hz hk himage ha b hc)
  have hd : Offenders.displacement (X T a) (X T b) = 4 :=
    (critical_displacement_eq h e hz hk himage a ha b hc).trans
      ((critical_displacement_eq_core_index h e a ha b hc).trans hi)
  exact ⟨hi,(critical_displacement_eq_core_index h e b hbcol a hr).symm.trans hd,hd⟩

include h e hz hk in
/-- The self-centralizer of the even critical image bounds the full source actor. -/
theorem critical_actor_bound (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (Y : Subgroup (FreeAmalgam T)) (hY : Y ≤ stabilizer T b)
    (hYX : Y ≤ centralizer (X T a : Set (FreeAmalgam T))) :
    ⁅Y,X T b⁆ ≤ ⁅X T a,X T b⁆ := by
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hAS := critical_X_le_vertex h e a ha b hc
  obtain ⟨c⟩ := chart_nonempty h b hbcol
  have heven : c.image h e hz hk (X T a) ≤ alternatingGroup (Fin 6) := by
    rw [←himage]; exact map_le_range _ _
  have hself := Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.conjugate_evenPart_centralizer
    ((ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_iff _ heven).mp
      (c.critical_offender h e hz hk himage hbcol a hr))
  have hle : c.image h e hz hk Y ≤ c.image h e hz hk (X T a) := by
    rw [←hself]
    refine le_inf ?_ ?_
    · rw [←himage]; exact map_le_range _ _
    · rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩
      have hh : x*y = y*x := c.injective (by simpa only [map_mul] using hYX hy _ hx)
      simpa only [map_mul] using congrArg π hh
  have hjoin : Y ≤ X T a ⊔ c.kernel h := by
    have hh := map_mono (f := c.embedding) (map_le_iff_le_comap.mp hle)
    rw [map_comap_eq_self (hY.trans_eq c.range_eq.symm),c.image_preimage h e hz hk _ hAS] at hh
    exact hh
  rw [commutator_comm Y,commutator_comm (X T a),c.commutator_join h hk _ hAS]
  exact commutator_mono le_rfl hjoin

include h e hz hk in
/-- All source-(2.3)(c) clauses for the cubic even-action branch. -/
theorem commutatorControl (himage : (π).range = alternatingGroup (Fin 6)) :
    CriticalCriterion.CommutatorControl T (sourceGeometry h) := by
  intro a ha b hc
  have hbcol := critical_endpoint_color T a ha _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a ha (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    b hbcol hc
  have hZ := (sourceGeometry h).omega_bound b hbcol (by
    rw [(sourceGeometry h).distance_constant b hbcol]; exact sourceDistance_pos h)
  refine ⟨Z T b,⟨hZ,hr.2,?_⟩⟩
  intro t ht Y hY hPhi
  exact ((commutator_mono le_rfl hZ).trans
    (critical_actor_bound h e hz hk himage a ha b hc Y
      (hY.trans (CriticalCriterion.edge_le_stabilizer T hbcol ht.1))
      (critical_frattini_centralizes h e a ha b hc t ht.1 ht.2 Y hY hPhi))).trans le_sup_left

namespace Chart
variable {a : Vertex (edge L R)} (c : Chart (L := L) (R := R) a)

private theorem edge_image_twoGroup {t : Vertex T} (ha : color T a = false)
    (hat : Adjacent T a t) : IsPGroup 2 (c.image h e hz hk (Q T t)) := by
  apply IsPGroup.map
  exact (edge_twoGroup h ha hat).of_injective (c.embedding.subgroupComap _)
    (fun _ _ he => Subtype.ext (c.injective (congrArg Subtype.val he)))

/-- The common image gives the common full-kernel join; E is not replaced by Q. -/
theorem critical_join_common (himage : (π).range = alternatingGroup (Fin 6))
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b)
    (d : Vertex T) (hd : CriticalPair T a d ((sourceGeometry h).exists_critical a ha))
    (htd : (cosetGraph T).dist t d + 1 = (cosetGraph T).dist a d) :
    X T b ⊔ c.kernel h = X T d ⊔ c.kernel h := by
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hD := critical_X_le_first_edge h e a ha d hd t hat htd
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hp := c.edge_image_twoGroup h e hz hk ha hat
  have he := ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_unique hp
    (show c.image h e hz hk (Q T t) ≤ alternatingGroup (Fin 6) by
      rw [←himage]; exact map_le_range _ _)
    (map_mono (comap_mono hB)) (map_mono (comap_mono hD))
    (c.critical_offender h e hz hk himage ha b hc) (c.critical_offender h e hz hk himage ha d hd)
  have hh := congrArg (fun A : Subgroup (Equiv.Perm (Fin 6)) =>
    (A.comap π).map c.embedding) he
  change ((c.image h e hz hk (X T b)).comap π).map c.embedding =
    ((c.image h e hz hk (X T d)).comap π).map c.embedding at hh
  rw [c.image_preimage h e hz hk _ (hB.trans hTS),c.image_preimage h e hz hk _ (hD.trans hTS)] at hh
  exact hh

/-- The whole-kernel preimage of the unique offender is normalized by the edge. -/
theorem critical_join_normalized (himage : (π).range = alternatingGroup (Fin 6))
    (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    Q T t ≤ normalizer (X T b ⊔ c.kernel h : Subgroup (FreeAmalgam T)) := by
  let A := c.image h e hz hk (X T b)
  let P := c.image h e hz hk (Q T t)
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  have hp : IsPGroup 2 P := c.edge_image_twoGroup h e hz hk ha hat
  have hAP : A ≤ P := map_mono (comap_mono hB)
  have hA := c.critical_offender h e hz hk himage ha b hc
  have hn : P ≤ normalizer (A : Set (Equiv.Perm (Fin 6))) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    apply ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_unique hp
      (show P ≤ alternatingGroup (Fin 6) by rw [←himage]; exact map_le_range _ _)
      ((map_mono hAP).trans_eq (mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hg))) hAP
    · refine ⟨hA.1.map_conj g,?_⟩
      change fixedCodim ρ (A.map (MulAut.conj g).toMonoidHom) ≤ rank (A.map (MulAut.conj g).toMonoidHom)
      rw [fixedCodim_map_conj,rank_map_conj]
      exact hA.2
    · exact hA
  have hn₀ : (Q T t).comap c.embedding ≤ normalizer (A.comap π : Set M) :=
    (map_le_iff_le_comap.mp hn).trans (le_normalizer_comap _)
  have hh := (map_mono (f := c.embedding) hn₀).trans (le_normalizer_map c.embedding)
  rw [map_comap_eq_self (hTS.trans_eq c.range_eq.symm),c.image_preimage h e hz hk _ (hB.trans hTS)] at hh
  exact hh
end Chart

include h e hz hk in
/-- The literal critical commutator is normal relative to the first edge kernel. -/
theorem critical_commutator_normal_edge (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    ((⁅X T a,X T b⁆).subgroupOf (Q T t)).Normal := by
  obtain ⟨c⟩ := chart_nonempty h a ha
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  apply normal_subgroupOf_of_le_normalizer
  rw [c.commutator_join h hk _ (hB.trans hTS)]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (c.critical_join_normalized h e hz hk himage ha b hc t hat ht hg),
    mem_normalizer_iff_map_conj_eq.mp (X_normalized T a (hTS hg))]

include h e hz hk in
/-- All critical endpoints through one oriented edge have the same commutator. -/
theorem critical_commutator_common (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b)
    (d : Vertex T) (hd : CriticalPair T a d ((sourceGeometry h).exists_critical a ha))
    (htd : (cosetGraph T).dist t d + 1 = (cosetGraph T).dist a d) :
    ⁅X T a,X T b⁆ = ⁅X T a,X T d⁆ := by
  obtain ⟨c⟩ := chart_nonempty h a ha
  have hB := critical_X_le_first_edge h e a ha b hc t hat ht
  have hD := critical_X_le_first_edge h e a ha d hd t hat htd
  have hTS := CriticalCriterion.edge_le_stabilizer T ha hat
  rw [c.commutator_join h hk _ (hB.trans hTS),
    c.critical_join_common h e hz hk himage ha b hc t hat ht d hd htd,
    ←c.commutator_join h hk _ (hD.trans hTS)]

include h e hz hk in
/-- Every source-(2.3)(d) clause holds on the original graph in the cubic even case. -/
theorem edgeWitness (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (t : Vertex T) (hat : Adjacent T a t)
    (ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b) :
    CriticalCriterion.EdgeWitness T (sourceGeometry h) a t ⁅X T a,X T b⁆ := by
  refine ⟨(critical_X_commutator_le h e a ha b hc).trans inf_le_left,
    critical_commutator_normal_edge h e hz hk himage a ha b hc t hat ht,
    critical_commutator_not_normal_vertex h e hz a ha b hc,?_⟩
  intro ha' d hd htd
  exact (critical_commutator_common h e hz hk himage a ha b hc t hat ht d hd (by
    rw [hd.1,(sourceGeometry h).distance_constant a ha']; exact htd)).le

include h e hz hk in
/-- The original cubic even-action branch has critical distance exactly four. -/
theorem distance_eq_four (himage : (π).range = alternatingGroup (Fin 6)) : sourceDistance h = 4 := by
  have hb : 2 < sourceDistance h := by
    by_contra! hh
    exact cubic_distanceTwo_impossible h e hz hk (sourceDistance_eq_two h hh)
  obtain ⟨b,hc⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one T (alpha T) b (by
    rw [hc.1,(sourceGeometry h).distance_constant (alpha T) rfl]; exact sourceDistance_pos h)
  exact CriticalCriterion.FromCentralizer.distance_eq_four T (sourceEdgeCentralizer h e)
    (sourceGeometry h) hb (generation h e hz) (commutatorControl h e hz hk himage)
    (alpha T) rfl b hc t hat ht _ (edgeWitness h e hz hk himage (alpha T) rfl b hc t hat ht)

include h e hz hk in
/-- The original auxiliary commutator is normal in the midpoint stabilizer. -/
theorem critical_commutator_normal_midpoint (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    ⁅X T a,X T b⁆ ≤ stabilizer T c ∧
      ((⁅X T a,X T b⁆).subgroupOf (stabilizer T c)).Normal := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  have hd : (cosetGraph T).dist a b = 4 :=
    (hc.1.trans ((sourceGeometry h).distance_constant a ha)).trans (distance_eq_four h e hz hk himage)
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two T a c hac
  have ht : (cosetGraph T).dist t b + 1 = (cosetGraph T).dist a b := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := b)
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := b)
    omega
  exact CriticalCriterion.FromCentralizer.normal_at_second T (sourceEdgeCentralizer h e)
    (sourceGeometry h) hb (generation h e hz) (commutatorControl h e hz hk himage)
    a ha b hc t c hat hct hac (by omega) _ (edgeWitness h e hz hk himage a ha b hc t hat ht)

open scoped commutatorElement
include h e hz hk in
/-- Midpoint normality makes the auxiliary commutator fixed by the original
midpoint residual, retaining the relative centralizer convention. -/
theorem critical_commutator_fixed_midpoint
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex T) (ha : color T a = false) (b : Vertex T)
    (hc : CriticalPair T a b ((sourceGeometry h).exists_critical a ha))
    (c : Vertex T) (hcCol : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcb : (cosetGraph T).dist c b = 2) :
    ⁅X T a,X T b⁆ ≤ fixedCore T c := by
  have hb : 2 < sourceDistance h := by rw [distance_eq_four h e hz hk himage]; decide
  let A := ⁅X T a,X T b⁆
  let S := stabilizer T c
  obtain ⟨hAS,hAn⟩ := critical_commutator_normal_midpoint h e hz hk himage a ha b hc c hac hcb
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


include h e hz hk in
/-- All derived radius generators lie in the original residual-fixed core.
Only pairs at the critical distance can contribute a nontrivial commutator. -/
theorem radius_derived_le_fixed
    (himage : (π).range = alternatingGroup (Fin 6)) (a : Vertex T) (ha : color T a = false) :
    ⁅V T a,V T a⁆ ≤ fixedCore T a := by
  have hfour := distance_eq_four h e hz hk himage
  have hb : 2 < sourceDistance h := by omega
  let geometry := sourceGeometry h
  let I := {d : Vertex T // color T d = false ∧ (cosetGraph T).dist d a ≤ 2}
  have heq : V T a = ⨆ d : I, Z T d.val := by
    apply le_antisymm
    · apply NaturalStructure.Exclusion.radius_le_of_m_ball ha
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
    (critical_commutator_fixed_midpoint h e hz hk himage f.val f.property.1 d.val hc
      a ha (by omega) (by omega))


include h e hz hk in
/-- The even-image cubic branch supplies a literal nonabelian radius with fixed derived subgroup. -/
theorem nonabelian_radius (himage : (π).range = alternatingGroup (Fin 6)) :
    ∃ c : Vertex T, color T c = false ∧ ¬ IsMulCommutative (V T c) ∧
      ⁅V T c,V T c⁆ ≤ fixedCore T c := by
  obtain ⟨b,hcrit⟩ := criticalPair_exists T (alpha T)
    ((sourceGeometry h).exists_critical (alpha T) rfl)
  let p := DistanceEight.PathCentrality.CriticalPath.ofPair (geometry := sourceGeometry h) rfl hcrit
  have hl : p.walk.length = 4 := p.length_eq_b.trans (distance_eq_four h e hz hk himage)
  have hle : 2 ≤ p.walk.length := by omega
  let c := p.walk.getVert 2
  have hc : color T c = false := (p.vertex_color hle).mpr (by decide)
  have hac : (cosetGraph T).dist (alpha T) c = 2 := p.dist_start hle
  have hcb : (cosetGraph T).dist c b = 2 := by rw [p.dist_end,hl]
  exact ⟨c,hc,faithful_midpoint_radius_not_commutative h e (alpha T) rfl b hcrit c hac hcb,
    radius_derived_le_fixed h e hz hk himage c hc⟩

include h e hz in
/-- Whole-core exhaustion or the two concrete remaining cubic natural-action branches. -/
theorem coreExhaustion_or_cubic_cases :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      ((CubicAction.projection h e hz hk).range = alternatingGroup (Fin 6) ∧
        sourceDistance h = 4 ∧ ∃ c : Vertex T, color T c = false ∧
          ¬ IsMulCommutative (V T c) ∧ ⁅V T c,V T c⁆ ≤ fixedCore T c) ∨
      (Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h) := by
  rcases coreExhaustion_or_cubic_largeDistance h e hz with hx | ⟨hk,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,?_⟩
    rcases CubicAction.range_alternatives h e hz hk with heven | hfull
    · exact Or.inl ⟨heven,distance_eq_four h e hz hk heven,nonabelian_radius h e hz hk heven⟩
    · exact Or.inr ⟨hfull,hb⟩

include h e hz in
/-- The literal C.1.32 consumer retains the entire original core in both unresolved branches. -/
theorem rankTwo_or_cubic_cases :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      ((CubicAction.projection h e hz hk).range = alternatingGroup (Fin 6) ∧
        sourceDistance h = 4 ∧ ∃ c : Vertex T, color T c = false ∧
          ¬ IsMulCommutative (V T c) ∧ ⁅V T c,V T c⁆ ≤ fixedCore T c) ∨
      (Function.Surjective (CubicAction.projection h e hz hk) ∧ 2 < sourceDistance h) :=
  (coreExhaustion_or_cubic_cases h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicEven
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
