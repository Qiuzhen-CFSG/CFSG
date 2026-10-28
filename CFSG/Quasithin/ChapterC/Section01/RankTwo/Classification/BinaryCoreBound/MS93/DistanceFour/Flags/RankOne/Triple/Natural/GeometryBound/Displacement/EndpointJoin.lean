module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality

/-!
# Endpoint geometry for the two first-layer cases on p.905

The order-two critical commutator and order-four edge commutator force the
endpoint image modulo Q_alpha to have order two. A crossed opposite kernel
then contains the whole endpoint. Incidence puts it in the new first-color
actor, and the distinct fixed hyperplanes force it outside that actor's
kernel. The marked parabolic quotient has order six, giving the required
index-three join without assuming a natural factor.

For a first layer contained in Q_middle, its commutators with the endpoint
lie in Z_middle and are centralized by the first layer. The commutator map
for one nontrivial endpoint coset takes values in
Z_middle / (Z_middle intersect Z_alpha), of order at most two. Its kernel
is fixed modulo Z_alpha by the entire endpoint, proving the contained-layer
fixed-index bound.

`FlagCriticalData.endpoint_join` and
`FlagCriticalData.contained_firstLayer_fixedIndex_le_two` discharge the two
extra premises in `two_lt_firstLayer_displacement_of_endpoint_join`. They
need neither the excess fixed-index assumption nor either strict displacement
inequality. Strict displacement assembly remains in the parent module.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), claim (1), printed p.905 (PDF page 82), including the
contained-layer paragraph omitted from the PDF's text extraction.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

private theorem fixed_index_bound {G : Type*} [Group G]
    (W E Q N D : Subgroup G) [Finite W] [Finite D] [IsMulCommutative D]
    (hWE : ⁅W, E⁆ ≤ D) (hWD : W ≤ centralizer (D : Set G))
    (hQ : Q ≤ E) (hi : Q.relIndex E = 2)
    (hWQ : ⁅W, Q⁆ ≤ N) (hEN : E ≤ normalizer N) :
    (commutatorPreimage W E N).relIndex W ≤ N.relIndex D := by
  classical
  let : CommGroup D := IsMulCommutative.instCommGroup
  obtain ⟨e, he, heQ⟩ : ∃ e ∈ E, e ∉ Q := by
    by_contra! h
    have hh : Q = E := le_antisymm hQ h
    rw [hh, relIndex_self] at hi
    omega
  let f : W →* D := {
    toFun w := ⟨⁅(w : G), e⁆, hWE (commutator_mem_commutator w.property he)⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := by
      apply Subtype.ext
      change ⁅(x : G) * (y : G), e⁆ = ⁅(x : G), e⁆ * ⁅(y : G), e⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hy := hWE (commutator_mem_commutator y.property he)
      have hx := hWE (commutator_mem_commutator x.property he)
      rw [← hWD x.property _ hy, mul_inv_cancel_right]
      exact (le_centralizer D hy _ hx).symm }
  let q := (QuotientGroup.mk' (N.subgroupOf D)).comp f
  let K := q.ker.map W.subtype
  have hK : K ≤ commutatorPreimage W E N := by
    apply le_commutatorPreimage (map_subtype_le _)
    apply commutator_le.mpr
    rintro w ⟨v, hv, rfl⟩ t ht
    have hve : ⁅(v : G), e⁆ ∈ N :=
      (QuotientGroup.eq_one_iff (f v)).mp hv
    by_cases htQ : t ∈ Q
    · exact hWQ (commutator_mem_commutator v.property htQ)
    · have hfactor : e⁻¹ * t ∈ Q := by
        have hh := (Q.subgroupOf E).mul_mem_iff_of_index_two hi
          (a := ⟨e⁻¹, E.inv_mem he⟩) (b := ⟨t, ht⟩)
        exact hh.mpr (by simp only [mem_subgroupOf, inv_mem_iff, heQ, htQ])
      have hf := hWQ (commutator_mem_commutator v.property hfactor)
      have hn := (mem_normalizer_iff.mp (hEN he) _).mp hf
      have hh := N.mul_mem hve hn
      have heq := commutatorElement_mul_right_eq_mul_conj (v : G) e (e⁻¹ * t)
      simp only [mul_inv_cancel_left] at heq
      change ⁅(v : G), t⁆ ∈ N
      rw [heq]
      simpa only [mul_assoc] using hh
  have hKi : K.relIndex W = q.ker.index := by
    have hh := relIndex_map_map_of_injective q.ker (⊤ : Subgroup W) W.subtype_injective
    simpa only [K, ← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] using hh
  have hbound : q.ker.index ≤ N.relIndex D := by
    rw [index_ker]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (relIndex_le_of_le_left hK index_ne_zero_of_finite).trans (hKi ▸ hbound)

/-- The endpoint has image of order two modulo the original vertex kernel.
An image of order four would generate the full edge kernel and give the
critical commutator the edge commutator's order four. -/
theorem FlagCriticalData.endpoint_image_index_two (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) :
    (Q R (alpha R)).relIndex (Z R p.endpoint) = 2 := by
  let T := Q R (beta R)
  let Q₀ := (Q R (alpha R)).subgroupOf T
  let E := (Z R p.endpoint).subgroupOf T
  have hET : Z R p.endpoint ≤ T := p.endpoint_le_edgeKernel hb
  have hQT : Q R (alpha R) ≤ T := Q_le_adjacent_h R rfl (base_adjacent R)
  let : Q₀.Normal := normal_subgroupOf_of_le_normalizer
    ((show T ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Q_normalized R _))
  have hQi : Q₀.index = 4 := early.edge_Q_index _ _ rfl (base_adjacent R)
  have hd : Q₀.relIndex E ∣ 4 := hQi ▸ Q₀.relIndex_dvd_index_of_normal E
  have hne : Q₀.relIndex E ≠ 1 := by
    rw [relIndex_subgroupOf hET]
    exact fun h => p.endpoint_not_le_Q common (relIndex_eq_one.mp h)
  have hfour : Q₀.relIndex E ≠ 4 := by
    intro hi
    have hm := relIndex_mul_index (show Q₀ ≤ E ⊔ Q₀ from le_sup_right)
    rw [relIndex_sup_right, hi, hQi] at hm
    have hgen : E ⊔ Q₀ = ⊤ := index_eq_one.mp (by omega)
    have hh := congrArg (Subgroup.map T.subtype) hgen
    dsimp only [E, Q₀] at hh
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hET,
      map_subgroupOf_eq_of_le hQT, ← MonoidHom.range_eq_map, range_subtype] at hh
    have hc : ⁅Z R (alpha R), Z R p.endpoint⁆ = ⁅Z R (alpha R), T⁆ :=
      commutator_eq_of_centralizing_sup ((sup_comm _ _).trans hh)
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (geometry.centralizes _ rfl)))
        ((hET.trans (show T ≤ stabilizer R (alpha R) from
          fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R)))).trans (Z_normalized R _))
    have hn := p.critical_commutator_card_two common
    rw [hc] at hn
    dsimp only [T] at hn
    rw [early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)] at hn
    omega
  have hf := Nat.mem_divisors.mpr ⟨hd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  have hi : Q₀.relIndex E = 2 := by omega
  rwa [relIndex_subgroupOf hET] at hi

private theorem original_kernel_le_local (source : LocalSource L R) (i : Bool) (g : M) :
    Q R (alpha R) ≤ localFlagKernel source i g := by
  have hbase : Q R (alpha R) ≤ flagKernel source i := by
    rw [Q_alpha R source.two_group source.core_le]
    apply map_mono
    change pCore 2 M ≤ (parabolic source.projection source.flag i).pCoreIn 2
    rw [Incident.parabolic_core_eq_comap source i, ← source.projection_kernel]
    intro x hx
    change source.projection x ∈ (modelParabolic source.flag i).pCoreIn 2
    rw [show source.projection x = 1 from hx]
    exact one_mem _
  have hg : embedM R g ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨g, rfl⟩
  have he : localConjugate (Q R (alpha R)) g = Q R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R (alpha R) hg)
  exact he.symm.le.trans (map_mono hbase)

private theorem le_of_index_two_crossing {G : Type*} [Group G]
    (E Q K : Subgroup G) (hi : Q.relIndex E = 2) (hQK : Q ≤ K)
    (hcross : ¬ E ⊓ K ≤ Q) : E ≤ K := by
  obtain ⟨x, ⟨hxE, hxK⟩, hxQ⟩ := SetLike.not_le_iff_exists.mp hcross
  intro y hy
  by_cases hyQ : y ∈ Q
  · exact hQK hyQ
  · have hh := (Q.subgroupOf E).mul_mem_iff_of_index_two hi
      (a := ⟨x⁻¹, E.inv_mem hxE⟩) (b := ⟨y, hy⟩)
    have hf : x⁻¹ * y ∈ Q := hh.mpr
      (by simp only [mem_subgroupOf, inv_mem_iff, hxQ, hyQ])
    simpa only [mul_inv_cancel_left] using K.mul_mem hxK (hQK hf)

/-- A crossed opposite kernel contains the entire endpoint: it contains
Q_alpha, and the endpoint has only two cosets modulo Q_alpha. -/
theorem FlagCriticalData.endpoint_le_crossed_kernel (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (d : M)
    (hcross : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R)) :
    Z R p.endpoint ≤ localFlagKernel source (!i) d :=
  le_of_index_two_crossing _ _ _ (p.endpoint_image_index_two common hb early)
    (original_kernel_le_local source (!i) d) hcross

/-- Incidence places the crossed opposite core, hence the endpoint,
in the actual first-color parabolic. -/
theorem FlagCriticalData.endpoint_le_first_actor (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (d : M)
    (hcross : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R))
    (g : M) (hinc : flagIncident source i g d) :
    Z R p.endpoint ≤ localFlagActor source i g := by
  obtain ⟨m, hgm, hdm⟩ := hinc
  have hactor : localFlagActor source i m = localFlagActor source i g := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source i g (g⁻¹ * m) hgm
  have hcore : localFlagKernel source (!i) m = localFlagKernel source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source (!i) d (d⁻¹ * m) hdm
  have hle : localFlagKernel source (!i) d ≤ localFlagActor source i g := by
    rw [← hactor, ← hcore]
    exact map_mono (by simpa only [Bool.not_not] using
      Incident.flagKernel_le_oppositeActor source (!i))
  exact (p.endpoint_le_crossed_kernel common hb early d hcross).trans hle

/-- The contained-layer case of p.905. Commutators lie in Z_middle,
which has at most two cosets modulo Z_alpha. The endpoint action factors
through its two-element image modulo Q_alpha; the commutator homomorphism
therefore has a kernel of index at most two. -/
theorem FlagCriticalData.contained_firstLayer_fixedIndex_le_two
    (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (g : M)
    (hcontained : firstFlagLayer (R := R) g ≤ Q R p.middle) :
    (commutatorPreimage (firstFlagLayer (R := R) g) (Z R p.endpoint)
      (Z R (alpha R))).relIndex (firstFlagLayer (R := R) g) ≤ 2 := by
  let W := firstFlagLayer (R := R) g
  let E := Z R p.endpoint
  let D := Z R p.middle
  let C := E ⊓ Q R (alpha R)
  have hEV : E ≤ V R p.middle :=
    le_iSup_of_le p.endpoint (le_iSup_of_le (show (cosetGraph R).dist p.endpoint p.middle ≤ 2 by
      rw [SimpleGraph.dist_comm]; exact p.second_distance.le) le_rfl)
  have hWE : ⁅W, E⁆ ≤ D := by
    rw [commutator_comm]
    exact (commutator_mono hEV hcontained).trans (early.commutator_le_Z _ p.middle_color)
  have hWD : W ≤ centralizer (D : Set (FreeAmalgam R)) :=
    hcontained.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ p.middle_color)))
  have hWQ : ⁅W, C⁆ ≤ Z R (alpha R) :=
    (commutator_mono (firstFlagLayer_le_radius g) inf_le_right).trans
      (early.commutator_le_Z _ rfl)
  have hEN : E ≤ normalizer (Z R (alpha R)) :=
    (source.critical_Z_le_stabilizer geometry (alpha R) rfl p.endpoint p.critical).2.trans
      (Z_normalized R _)
  have hCi : C.relIndex E = 2 := by
    rw [inf_relIndex_left]
    exact p.endpoint_image_index_two common hb early
  let := finite_stabilizer R (alpha R)
  let := finite_stabilizer R p.middle
  let : Finite W := Finite.of_injective (inclusion ((firstFlagLayer_le_radius g).trans
    (geometry.V_local _ rfl common.large_distance))) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (Z_le_stabilizer R p.middle))
    (inclusion_injective _)
  let := geometry.Z_elementary (lt_trans (by decide) common.large_distance)
    p.middle p.middle_color
  have hi := fixed_index_bound W E C (Z R (alpha R)) D hWE hWD inf_le_left hCi hWQ hEN
  have hD : (Z R (alpha R)).relIndex D ≤ 2 := by
    have hh := relIndex_le_of_le_left
      (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      (show (Z R (beta R)).relIndex D ≠ 0 from index_ne_zero_of_finite)
    exact hh.trans_eq (early.edge_Z_index p.middle (beta R) p.middle_color
      (adjacent_symm R p.middle_neighbor))
  exact hi.trans hD

private theorem map_centralizer_equiv {G : Type*} [Group G]
    (K : Subgroup G) (e : G ≃* G) :
    (centralizer (K : Set G)).map e.toMonoidHom =
      centralizer (K.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [Finite M] in
private theorem local_fixed_eq_conjugate (common : CommonFacts R source geometry)
    (hkernel : flagKernel source i = Q R (beta R)) (g : M) :
    localFlagZ source i g = localConjugate (Z R (beta R)) g := by
  let e := MulAut.conj (embedM R g)
  have hZ : (Z R (alpha R)).map e.toMonoidHom = Z R (alpha R) :=
    Incident.localConjugate_Z g
  change Z R (alpha R) ⊓ centralizer ((flagKernel source i).map e.toMonoidHom :
    Set (FreeAmalgam R)) = (Z R (beta R)).map e.toMonoidHom
  rw [← map_centralizer_equiv, ← hZ, ← map_inf _ _ _ e.injective,
    hkernel, ← Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]

omit [Finite M] in
private theorem local_fixed_index_two (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R)) (g : M) :
    (localFlagZ source i g).relIndex (Z R (alpha R)) = 2 := by
  have hZ : localConjugate (Z R (alpha R)) g = Z R (alpha R) :=
    Incident.localConjugate_Z g
  rw [local_fixed_eq_conjugate common hkernel g, ← hZ]
  exact (relIndex_map_map_of_injective _ _ (MulAut.conj (embedM R g)).injective).trans
    (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))

omit [Finite M] in
/-- Distinct local fixed layers prevent the endpoint from lying in the
new first-color kernel. Otherwise both fixed hyperplanes lie in the proper
endpoint centralizer in Z_alpha and hence coincide. -/
theorem FlagCriticalData.endpoint_not_le_first_kernel (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R))
    (g : M) (hne : localFlagZ source i g ≠ localFlagZ source i 1) :
    ¬ Z R p.endpoint ≤ localFlagKernel source i g := by
  intro hEK
  let C := Z R (alpha R) ⊓ centralizer (Z R p.endpoint : Set (FreeAmalgam R))
  have hle (x : M) (hx : Z R p.endpoint ≤ localFlagKernel source i x) :
      localFlagZ source i x ≤ C :=
    le_inf inf_le_left (inf_le_right.trans (centralizer_le hx))
  have hbase : Z R p.endpoint ≤ localFlagKernel source i 1 := by
    simpa only [localFlagKernel, localConjugate_one, hkernel] using p.endpoint_le_edgeKernel hb
  have hneC : C.relIndex (Z R (alpha R)) ≠ 1 := by
    intro hi
    exact common.critical_noncommutation (alpha R) rfl p.endpoint p.critical
      (commutator_eq_bot_iff_le_centralizer.mpr ((relIndex_eq_one.mp hi).trans inf_le_right))
  have heq (x : M) (hx : Z R p.endpoint ≤ localFlagKernel source i x) :
      C = localFlagZ source i x := by
    have ht := relIndex_mul_relIndex (localFlagZ source i x) C (Z R (alpha R))
      (hle x hx) inf_le_left
    rw [local_fixed_index_two common early hkernel x] at ht
    have hd : C.relIndex (Z R (alpha R)) ∣ 2 :=
      ⟨(localFlagZ source i x).relIndex C, by simpa only [mul_comm] using ht.symm⟩
    have htwo : C.relIndex (Z R (alpha R)) = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hneC
    rw [htwo] at ht
    exact le_antisymm (relIndex_eq_one.mp (by omega)) (hle x hx)
  exact hne ((heq g hEK).symm.trans (heq 1 hbase))

private theorem local_kernel_index_six (source : LocalSource L R) (i : Bool) (g : M) :
    (localFlagKernel source i g).relIndex (localFlagActor source i g) = 6 := by
  rw [localFlagKernel, localFlagActor]
  change ((flagKernel source i).map _).relIndex ((flagParabolic source i).map _) = 6
  rw [relIndex_map_map_of_injective _ _ (MulAut.conj (embedM R g)).injective]
  change (((parabolic source.projection source.flag i).pCoreIn 2).map (embedM R)).relIndex
    ((parabolic source.projection source.flag i).map (embedM R)) = 6
  rw [relIndex_map_map_of_injective _ _ (embedM_injective R),
    Incident.parabolic_core_eq_comap source i, relIndex_comap]
  have hm : (parabolic source.projection source.flag i).map source.projection =
      modelParabolic source.flag i := map_comap_eq_self_of_surjective source.projection_surjective _
  rw [hm]
  let P := modelParabolic source.flag i
  have hc : Nat.card (P.pCoreIn 2) = 4 := by
    rw [pCoreIn, Nat.card_congr ((pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective).toEquiv.symm]
    exact (Matrix.PSL3Two.ParabolicCoreModel.core_data (modelParabolicEquivSymmetric source.flag i)).2
  have ht := ((P.pCoreIn 2).subgroupOf P).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show P.pCoreIn 2 ≤ P from map_subtype_le _)).toEquiv,
    hc, card_modelParabolic source.flag i] at ht
  change (P.pCoreIn 2).relIndex P * 4 = 24 at ht
  change (P.pCoreIn 2).relIndex P = 6
  omega

/-- The endpoint escapes the local two-core and has image of order two
modulo it. The core has index six in the literal marked parabolic, so the
endpoint--core join has index three. All normality is relative to that actor. -/
theorem FlagCriticalData.endpoint_join_index_three (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hcross : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R))
    (g : M) (hinc : flagIncident source i g d)
    (hne : localFlagZ source i g ≠ localFlagZ source i 1) :
    (Z R p.endpoint ⊔ localFlagKernel source i g).relIndex (localFlagActor source i g) = 3 := by
  let E := Z R p.endpoint
  let K := localFlagKernel source i g
  let P := localFlagActor source i g
  have hEP : E ≤ P := p.endpoint_le_first_actor common hb early d hcross g hinc
  have hKP : K ≤ P := map_mono (flagKernel_le source i)
  have hn : P ≤ normalizer K :=
    (map_mono (flagKernel_normalized source i)).trans
      (le_normalizer_map (MulAut.conj (embedM R g)).toMonoidHom)
  let : (K.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  have hi : K.relIndex E = 2 := by
    have hd := relIndex_dvd_of_le_left E (original_kernel_le_local source i g)
    rw [p.endpoint_image_index_two common hb early] at hd
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (fun he => p.endpoint_not_le_first_kernel common hb early hkernel g hne
        (relIndex_eq_one.mp he))
  have hj : K.relIndex (E ⊔ K) = K.relIndex E := by
    have hh := relIndex_sup_right (E.subgroupOf P) (K.subgroupOf P)
    rwa [← subgroupOf_sup hEP hKP, relIndex_subgroupOf (sup_le hEP hKP),
      relIndex_subgroupOf hEP] at hh
  have ht := relIndex_mul_relIndex K (E ⊔ K) P le_sup_right (sup_le hEP hKP)
  rw [hj, hi, local_kernel_index_six source i g] at ht
  change (E ⊔ K).relIndex P = 3
  omega

/-- The endpoint and its kernel generate an actual index-three subgroup of the
first-color actor. The conclusion holds before imposing small displacement;
no natural factor or strict displacement inequality is assumed. -/
theorem FlagCriticalData.endpoint_join (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (hkernel : flagKernel source i = Q R (beta R))
    (d : M) (hcross : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R))
    (g : M) (hinc : flagIncident source i g d)
    (hne : localFlagZ source i g ≠ localFlagZ source i 1) :
    Z R p.endpoint ≤ localFlagActor source i g ∧
      (Z R p.endpoint ⊔ localFlagKernel source i g).relIndex (localFlagActor source i g) = 3 :=
  ⟨p.endpoint_le_first_actor common hb early d hcross g hinc,
    p.endpoint_join_index_three common hb early hkernel d hcross g hinc hne⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
