module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.FixedSpaces

/-!
# The binary Y contradiction in MS93 (4.6.8)(4)

The genuine first-parabolic S₃ action puts the incident commutator seed
inside the second layer: a reflection's displacement in characteristic two
is fixed by that reflection. The completed finite (1.7)(i) application shows
that this seed is not fixed by the opposite tilded residual, for every
incident neighbor.

Consequently an endpoint outside the opposite core cannot fix the second
layer modulo Z_alpha. Otherwise its nonidentity involution image normally
generates the actual opposite S₃ quotient, making that entire actor fix the
layer, contrary to the preceding triple calculation. Normality is relative
to the full finite actor, and its quotient has exactly the original local
core as kernel.

Now suppose the second layer lies in Q_middle. The literal source subgroup
Y = [U_delta intersect Q_middle, Z_endpoint] lies in U_delta intersect Z_middle.
The binary edge index |Z_middle : Z_beta| = 2 and middle noncontainment put
this intersection in Z_alpha, contradicting the nontrivial endpoint action.
This binary strengthening closes the Y contradiction before the source's
later propagation step; the source assembly retains its authorized
`FlagPropagation` parameter. No reverse-containment-to-index implication is
assumed: the missing direction is proved by the actual endpoint action.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8)(3)--(4), printed p.906; the rank-one pairing is (1.7)(i),
printed pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
open Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Claim (3) for every incident neighbor. The actual finite pairing source
and its natural quotient need only incidence, not the endpoint crossing. -/
theorem incident_triple_not_le (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (d : M) (hd : flagIncident source i 1 d) :
    ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) := by
  intro ht
  let s := Pairing.Transport.sourceData source geometry common early i hkernel natural p d hd ht
  have hz := Pairing.Transport.Natural.opposite_fixed_nonzero source geometry common early i hkernel d hd
  have hpair := Pairing.Transport.Quotient.pairing_bound_of_quotient source geometry
    common.large_distance i hkernel d hd (RankOnePairing.theorem_1_7_i s hz).2.1
  exact Pairing.contradiction_of_pairing source geometry common early i hkernel p d hd
    (Pairing.Transport.Natural.moving_le_span source geometry common.large_distance i hkernel d hd) hpair

/-- The incident reflection displacement is fixed in characteristic two,
so its actual lifted seed lies in the literal second flag layer. -/
theorem incident_seed_le_secondLayer (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hd : flagIncident source i 1 d) :
    Pairing.seed source i d ≤ secondFlagLayer source i d := by
  let b := flagBarModule source geometry common.large_distance i hkernel
  obtain ⟨π, hπ, hker⟩ := exists_barProjection source i
  obtain ⟨ρ, haction⟩ := exists_descended_barRepresentation b geometry common early hkernel π hπ hker
  obtain ⟨t, ht, _, himage⟩ := exists_incident_reflection source i d hd π hπ hker
  have hs := seed_image_of_reflection b geometry common.large_distance hkernel d hd π ρ haction t himage
  have hseed := Pairing.seed_le_firstLayer source geometry common.large_distance i hkernel d hd
  have hcomm : ⁅Pairing.seed source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk x hx
    let a : flagParabolic source i := ⟨k, Pairing.incidentKernel_le_flagParabolic source i d hd hk⟩
    let v : V R (beta R) := ⟨x, hseed hx⟩
    let w := edgeRadiusAction source geometry common.large_distance i hkernel a v
    have hv : (b.projection v).toAdd ∈ BinaryS3.displacement ρ t := by
      rw [← hs]
      exact ⟨v, hx, rfl⟩
    have hf : ρ t (b.projection v).toAdd = (b.projection v).toAdd := by
      obtain ⟨u, hu⟩ := hv
      have htt : ρ t (ρ t u) = u := by
        rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one]
        rfl
      change ρ t u - u = (b.projection v).toAdd at hu
      rw [← hu, map_sub, htt]
      have hx2 (a : b.Space) : -a = a := by
        have hz : (2 : ZMod 2) • a = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
        have hz' : a + a = 0 := by simpa only [two_smul] using hz
        exact neg_eq_iff_add_eq_zero.mpr hz'
      simp only [sub_eq_add_neg, hx2, add_comm]
    have hm := (himage (π a)).mp (mem_map_of_mem π hk)
    have he : b.projection w = b.projection v := by
      apply Multiplicative.toAdd.injective
      rw [b.action a v w (edgeRadiusAction_apply source geometry common.large_distance i hkernel a v), haction]
      rcases hm with hm | hm
      · rw [hm, map_one]; rfl
      · rw [hm]; exact hf
    have hz : w * v⁻¹ ∈ b.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    rw [b.kernel] at hz
    exact hz
  have hp : Pairing.seed source i d ≤ commutatorPreimage (firstFlagLayer (R := R) 1)
      (localFlagKernel source (!i) d) (Z R (alpha R)) :=
    le_commutatorPreimage (by simpa only [firstFlagLayer, localConjugate_one] using hseed) hcomm
  exact hp.trans (le_iSup_of_le 1 (le_iSup_of_le hd le_rfl))

private theorem s3_conjugates : ∀ t : BinaryS3.Actor, t ^ 2 = 1 → t ≠ 1 →
    ∀ x : BinaryS3.Actor, x = 1 ∨ (∃ a, x = a * t * a⁻¹) ∨
      (∃ a b, x = (a * t * a⁻¹) * (b * t * b⁻¹)) := by
  decide +kernel

private theorem s3_normal_eq_top (H : Subgroup BinaryS3.Actor) [H.Normal]
    (t : BinaryS3.Actor) (ht : t ∈ H) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : H = ⊤ := by
  apply top_unique
  intro x _
  rcases s3_conjugates t ht2 ht1 x with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · exact H.one_mem
  · exact (inferInstance : H.Normal).conj_mem t ht a
  · exact H.mul_mem ((inferInstance : H.Normal).conj_mem t ht a)
      ((inferInstance : H.Normal).conj_mem t ht b)

private theorem actor_fixed_of_endpoint {G : Type*} [Group G]
    (P K E W N : Subgroup G)
    (π : P →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (hker : π.ker = K.subgroupOf P) (hKP : K ≤ P) (hEP : E ≤ P)
    (hPW : P ≤ normalizer W) (hPN : P ≤ normalizer N)
    (hKW : ⁅W,K⁆ ≤ N) (hEW : ⁅W,E⁆ ≤ N)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hEnot : ¬ E ≤ K) : ⁅W,P⁆ ≤ N := by
  let C := commutatorPreimage P W N
  have hn : P ≤ normalizer C := commutatorPreimage_normalized P W N P hPN
    P.le_normalizer hPW hPN
  let : (C.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  let D := (C.subgroupOf P).map π
  let : D.Normal := (inferInstance : (C.subgroupOf P).Normal).map π hπ
  have hKC : K ≤ C := le_commutatorPreimage hKP (by rwa [commutator_comm])
  have hEC : E ≤ C := le_commutatorPreimage hEP (by rwa [commutator_comm])
  obtain ⟨e, he, heK⟩ := SetLike.not_le_iff_exists.mp hEnot
  let a : P := ⟨e, hEP he⟩
  have ht1 : π a ≠ 1 := by
    intro h
    have hh : a ∈ π.ker := h
    rw [hker] at hh
    exact heK hh
  have ht2 : π a ^ 2 = 1 := by
    rw [← map_pow]
    have ha : a ^ 2 = 1 := Subtype.ext (hE2 e he)
    rw [ha, map_one]
  have hD : D = ⊤ := s3_normal_eq_top D (π a) (mem_map_of_mem π (hEC he)) ht2 ht1
  have hPC : P ≤ C := by
    intro x hx
    have hm : π ⟨x, hx⟩ ∈ D := hD ▸ Subgroup.mem_top _
    have hh : (⟨x, hx⟩ : P) ∈ D.comap π := hm
    have hk : π.ker ≤ C.subgroupOf P := by rw [hker]; exact fun _ hy => hKC hy
    change (⟨x, hx⟩ : P) ∈ ((C.subgroupOf P).map π).comap π at hh
    rw [comap_map_eq_self hk] at hh
    exact hh
  rw [commutator_comm]
  exact (commutator_mono hPC le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hPN)

private theorem local_barProjection (source : LocalSource L R) (j : Bool) (d : M) :
    ∃ π : localFlagActor source j d →* BinaryS3.Actor,
      Function.Surjective π ∧
      π.ker = (localFlagKernel source j d).subgroupOf (localFlagActor source j d) := by
  obtain ⟨q, hq, hk⟩ := exists_barProjection source j
  let f := (MulAut.conj (embedM R d)).toMonoidHom
  let e : flagParabolic source j ≃* localFlagActor source j d :=
    (flagParabolic source j).equivMapOfInjective f (MulAut.conj _).injective
  refine ⟨q.comp e.symm.toMonoidHom, hq.comp e.symm.surjective, ?_⟩
  ext x
  change q (e.symm x) = 1 ↔ (x : FreeAmalgam R) ∈ localFlagKernel source j d
  rw [← MonoidHom.mem_ker, hk]
  change (e.symm x : FreeAmalgam R) ∈ flagKernel source j ↔
    (x : FreeAmalgam R) ∈ (flagKernel source j).map f
  have he : f (e.symm x) = (x : FreeAmalgam R) := congrArg Subtype.val (e.apply_symm_apply x)
  constructor
  · intro h
    exact ⟨e.symm x, h, he⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy := (MulAut.conj (embedM R d)).injective (hyx.trans he.symm)
    exact hxy ▸ hy

/-- An endpoint outside the local two-core acts nontrivially on the second
layer modulo Z_alpha. The proof uses the genuine local S₃ quotient. -/
theorem secondLayer_endpoint_commutator_not_le_Z (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (d : M) (hd : flagIncident source i 1 d)
    (hEnot : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d) :
    ¬ ⁅secondFlagLayer source i d, Z R p.endpoint⁆ ≤ Z R (alpha R) := by
  intro hfixed
  obtain ⟨π, hπ, hker⟩ := local_barProjection source (!i) d
  have hP := localFlagActor_le_stabilizer source (!i) d
  have hE2 : ∀ x ∈ Z R p.endpoint, x ^ 2 = 1 := by
    let := geometry.Z_elementary (lt_trans (by decide) common.large_distance)
      p.endpoint p.endpoint_color
    intro x hx
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := Z R p.endpoint)) (⟨x, hx⟩ : Z R p.endpoint)
    exact congrArg Subtype.val hh
  have hfull := actor_fixed_of_endpoint (localFlagActor source (!i) d)
    (localFlagKernel source (!i) d) (Z R p.endpoint) (secondFlagLayer source i d)
    (Z R (alpha R)) π hπ hker (map_mono (flagKernel_le source (!i)))
    (endpoint_le_incidentActor source geometry hb i hkernel p d hd)
    (secondFlagLayer_normalized source geometry common.large_distance i d)
    (hP.trans (Z_normalized R _))
    (secondFlagLayer_commutator_le_Z source geometry common.large_distance i d)
    hfixed hE2 hEnot
  apply incident_triple_not_le source geometry common early i hkernel natural p d hd
  exact (commutator_mono
    (le_sup_right.trans (incident_seed_le_secondLayer source geometry common early i hkernel d hd))
    (map_mono (flagResidual_le source (!i)))).trans hfull

/-- Claim (4) in the binary case. Assuming containment in Q_middle makes
the actual Y lie in Z_alpha, contradicting the endpoint action. -/
theorem displacement_of_selection (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (d : M) (hd : flagIncident source i 1 d)
    (hEnot : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d)
    (hmiddle : ¬ Z R p.middle ≤ secondFlagLayer source i d) :
    2 ≤ (Q R p.middle).relIndex (secondFlagLayer source i d) := by
  apply (displacement_iff source geometry common.large_distance i d p.middle).mpr
  intro hcontained
  apply secondLayer_endpoint_commutator_not_le_Z source geometry common hb early i hkernel natural p d hd hEnot
  have hY := endpoint_commutator_le source geometry hb early i hkernel p d hd
  rw [inf_eq_left.mpr hcontained] at hY
  exact hY.trans ((inf_comm _ _).le.trans
    (middle_intersection_le_Z_of_not_le source geometry early i p d hmiddle))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident
