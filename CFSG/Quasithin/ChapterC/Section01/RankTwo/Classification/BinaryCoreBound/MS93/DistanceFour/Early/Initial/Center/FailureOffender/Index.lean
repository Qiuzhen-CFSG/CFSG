module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Source

/-!
# Projected offenders from radius-intersection bounds

An opposite radius group has elementary image in the marked local SL₃(2)
quotient: its squares lie in its center, and that center lies in the target
kernel. A commutator bound on V_a ∩ Q_c therefore bounds fixed codimension
on the literal quotient V_a/Z(V_a) by [V_a : V_a ∩ Q_c].

Only the radius generators escaping Q_a are needed as actors. Their join
has the same image as V_c modulo Q_a. We construct this join and extend
bounds on its generators using relative normalization of Z(V_a).

The geometric intersection bound remains an explicit premise here. No
trivial action of Q_a, elementary lift, or residual-fixed derived group is
assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first paragraph of (4.6.1), printed p.900.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The per-generator intersection bound in the first paragraph of (4.6.1).
The escaping condition is essential; this does not bound all of V_c. -/
def RadiusCenterIntersectionBound (a c : Vertex R) : Prop :=
  ∀ d, color R d = false → (cosetGraph R).dist d c = 2 →
    ¬ Z R d ≤ Q R a →
    ⁅V R a ⊓ Q R c, Z R d⁆ ≤ (center (V R a)).map (V R a).subtype

private theorem fixedSpace_subgroup_index {G T : Type*} [Group G] [Group T]
    [IsElementaryAbelian 2 T] [Finite T] (action : G →* MulAut T) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card T = 2 ^ Module.finrank (ZMod 2) (Additive T) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive T)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

private theorem elementary_of_square_one {T : Type*} [Group T]
    (h : ∀ x : T, x ^ 2 = 1) : IsElementaryAbelian 2 T := by
  have hi (x : T) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h x)
  let : IsMulCommutative T := ⟨⟨fun x y => by
    have he := mul_inv_rev x y
    simpa only [hi] using he⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h⟩

/-- The favorable index comparison constructs the actual projected offender.
The actor may be any subgroup of the opposite radius group. -/
theorem radiusCenterOffender_of_intersection_bound
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (E : Subgroup (FreeAmalgam R)) (hEV : E ≤ V R c) (hne : ¬ E ≤ Q R a)
    (hcomm : ⁅V R a ⊓ Q R c, E⁆ ≤ (center (V R a)).map (V R a).subtype)
    (hi : (Q R c).relIndex (V R a) ≤ (Q R a).relIndex E) :
    HasRadiusCenterOffender common hb a ha := by
  let := radiusCenterQuotient_elementary common hb a ha
  let := radiusCenterQuotient_elementary common hb c hc
  let := finite_radius common a ha
  let := finite_radius common c hc
  have hAS : E ≤ stabilizer R a := hEV.trans ((radius_le_Q common c hc).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm, hd])))
  obtain ⟨π, hπ, hker⟩ := Escape.Initial.Natural.exists_localProjection source a ha
  let A := E.subgroupOf (stabilizer R a)
  have helem : IsElementaryAbelian 2 (A.map π) := by
    apply elementary_of_square_one
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := hx
    apply Subtype.ext
    change π g ^ 2 = 1
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rw [hker]
    have hs : (⟨g.val, hEV hg⟩ : V R c) ^ 2 ∈ center (V R c) := by
      have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (radiusCenterQuotient_elementary common hb c hc).exponent_dvd_p
          (QuotientGroup.mk' (center (V R c)) ⟨g.val, hEV hg⟩)
      rw [← map_pow] at hpow
      exact (QuotientGroup.eq_one_iff _).mp hpow
    exact radius_center_le_Q_of_dist_two common c a hc
      (by rw [SimpleGraph.dist_comm, hd]) (mem_map_of_mem (V R c).subtype hs)
  have hnon : A.map π ≠ ⊥ := by
    intro he
    have hAK := (Subgroup.map_eq_bot_iff _).mp he
    rw [hker] at hAK
    exact hne (fun x hx => hAK (show (⟨x, hAS hx⟩ : stabilizer R a) ∈ A from hx))
  have hcard : Nat.card (A.map π) = (Q R a).relIndex E := by
    change Nat.card ((E.subgroupOf (stabilizer R a)).map π) = _
    rw [← relIndex_ker, hker, subgroupOf, relIndex_comap,
      map_subgroupOf_eq_of_le hAS]
  refine ⟨π, A, hπ, hker, helem, hnon, ?_⟩
  let q := QuotientGroup.mk' (center (V R a))
  let C := Subgroup.toAddSubgroup.symm
    (fixedSpace (Offenders.linearize (radiusCenterQuotientAction a)) A).toAddSubgroup
  have hC : (Q R c).subgroupOf (V R a) ≤ C.comap q := by
    intro v hv g
    apply congrArg Additive.ofMul
    apply (radiusCenterQuotientAction_fixed_iff a g.val v).mpr
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator g.property ⟨v.property, hv⟩)
  have hind : C.index ≤ (Q R c).relIndex (V R a) := by
    rw [← C.index_comap_of_surjective (QuotientGroup.mk'_surjective (center (V R a)))]
    exact index_antitone hC
  have hAE : IsElementaryTwo (A.map π) := ⟨hnon, helem⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← fixedSpace_subgroup_index, ← hAE.card_eq_two_pow_rank, hcard]
  exact hind.trans hi

/-- Join of the opposite radius generators whose image in G_a/Q_a is nontrivial. -/
noncomputable def radiusEscapeActor (a c : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⨆ d, ⨆ (_ : color R d = false ∧ (cosetGraph R).dist d c ≤ 2 ∧ ¬ Z R d ≤ Q R a), Z R d

omit [Finite M] in
/-- Every escaping generator is a generator of the opposite radius group. -/
theorem radiusEscapeActor_le (a c : Vertex R) : radiusEscapeActor a c ≤ V R c := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  exact le_iSup_of_le d (le_iSup_of_le hd.2.1 le_rfl)

omit [Finite M] in
/-- Omitting generators inside Q_a preserves the full radius image modulo Q_a. -/
theorem radiusEscapeActor_sup_Q (a c : Vertex R) (hc : color R c = false) :
    radiusEscapeActor a c ⊔ Q R a = V R c ⊔ Q R a := by
  apply le_antisymm (sup_le_sup_right (radiusEscapeActor_le a c) _)
  apply sup_le _ le_sup_right
  apply radius_le_of_generators c hc
  intro d hd hdc
  by_cases h : Z R d ≤ Q R a
  · exact h.trans le_sup_right
  · have hE : Z R d ≤ radiusEscapeActor a c :=
      le_iSup_of_le d (le_iSup_of_le ⟨hd, hdc, h⟩ le_rfl)
    exact hE.trans le_sup_left

/-- The escaping actor retains the full opposite displacement index. -/
theorem radiusEscapeActor_relIndex
    (common : CommonFacts R source geometry)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    (Q R a).relIndex (radiusEscapeActor a c) = (Q R a).relIndex (V R c) := by
  have hVS : V R c ≤ stabilizer R a := (radius_le_Q common c hc).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm, hd]))
  have hES := (radiusEscapeActor_le a c).trans hVS
  have hQS : Q R a ≤ stabilizer R a := fun _ hx => hx.1
  let := Q_normal R a
  have h := congrArg (fun H : Subgroup (FreeAmalgam R) =>
    ((Q R a).subgroupOf (stabilizer R a)).relIndex (H.subgroupOf (stabilizer R a)))
      (radiusEscapeActor_sup_Q a c hc)
  rw [subgroupOf_sup hES hQS, subgroupOf_sup hVS hQS,
    relIndex_sup_right, relIndex_sup_right,
    relIndex_subgroupOf hES, relIndex_subgroupOf hVS] at h
  exact h

private theorem commutator_iSup_le_of_normalizes {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer (D : Set G)) (hc : ∀ i, ⁅A i, Y⁆ ≤ D) :
    ⁅⨆ i, A i, Y⁆ ≤ D := by
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

/-- The source per-generator bounds extend to the escaping actor, using
normalization of the actual radius center by the local stabilizer. -/
theorem radiusEscapeActor_commutator
    (common : CommonFacts R source geometry)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hgen : RadiusCenterIntersectionBound a c) :
    ⁅V R a ⊓ Q R c, radiusEscapeActor a c⁆ ≤
      (center (V R a)).map (V R a).subtype := by
  have hVS : V R c ≤ stabilizer R a := (radius_le_Q common c hc).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm, hd]))
  have hnorm := hVS.trans (radius_center_normalized a)
  rw [commutator_comm]
  unfold radiusEscapeActor
  apply commutator_iSup_le_of_normalizes _ _ _
    ((radiusEscapeActor_le a c).trans hnorm)
  intro d
  apply commutator_iSup_le_of_normalizes _ _ _
    ((le_iSup (fun d => ⨆ (_ : color R d = false ∧
      (cosetGraph R).dist d c ≤ 2 ∧ ¬ Z R d ≤ Q R a), Z R d) d).trans
        ((radiusEscapeActor_le a c).trans hnorm))
  intro hd'
  rw [commutator_comm]
  apply hgen d hd'.1 _ hd'.2.2
  have he : Even ((cosetGraph R).dist d c) := by
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d c
    rw [← hp, walk_even_iff_color_eq, hd'.1, hc]
  have hz : (cosetGraph R).dist d c ≠ 0 := by
    intro hz
    have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp hz
    subst d
    apply hd'.2.2
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc)
    rw [SimpleGraph.dist_comm, hd, geometry.distance_constant c hc]
    exact common.large_distance
  obtain ⟨n, hn⟩ := he
  omega
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
