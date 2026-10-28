module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Dimensions

/-!
# Endpoint and radius bounds in the large-intersection branch

The binary critical commutator has order two. Comparing it with the edge
commutator of order four makes the endpoint image modulo Q_alpha cyclic of
order two. The compatible opposite core therefore contains the whole endpoint,
so the unstarred second layer centralizes it modulo Z_alpha.

On K = V_alpha intersect Q_c, the endpoint commutator takes values in Z_c,
whose index modulo Z_alpha is at most two. The commutator homomorphism bounds
the fixed-space index on K by two. Since the unstarred second layer escapes K,
its fixed vectors halve the bound on the entire radius group from eight to four.
All quotients retain Z_alpha. Three conjugate involutions generating the actual
SL3(2) quotient then bound the codimension of its global fixed space by six,
giving the literal radius index over B at most 64. Full first-actor fixation
of Y is a separate conclusion of the source calculation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the opening of (4.6.12)(5), printed p.911. In the binary natural
three-space specialization the auxiliary commutator's order-four case is
impossible; the order-two calculation below treats the remaining case.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The source auxiliary displacement has order two in the binary specialization.
This also excludes its printed order-q² alternative, without identifying it
with the amalgam's edge subgroup R. -/
theorem endpoint_auxiliary_card_two (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) :
    Nat.card (⁅Z R (alpha R), Z R s.endpoint⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  let n : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have he := critical_endpoint_color R (alpha R) rfl _ s.critical
  rw [n.critical_commutator_eq geometry (alpha R) rfl s.endpoint s.critical]
  let : Finite (U R (alpha R)) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at _ rfl]; decide)
  let : Finite (U R s.endpoint) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at _ he]; decide)
  let := geometry.U_elementary (lt_trans (by decide) common.large_distance) (alpha R) rfl
  let := geometry.U_elementary (lt_trans (by decide) common.large_distance) s.endpoint he
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry (alpha R) rfl s.endpoint s.critical
  exact card_commutator_eq_two_of_elementary_eight _ _
    (common.natural.card_at _ rfl) (common.natural.card_at _ he) hn hn'
    (n.critical_U_noncommutation geometry (alpha R) rfl s.endpoint s.critical)

private theorem endpoint_le_edge (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    Z R s.endpoint ≤ Q R (beta R) := by
  have hEV : Z R s.endpoint ≤ V R s.middle :=
    le_iSup_of_le s.endpoint (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm]; exact s.second_distance.le) le_rfl)
  exact hEV.trans ((Early.radius_le_Q common s.middle s.middle_color).trans
    (Q_le_adjacent_h R rfl (adjacent_symm R hbc)))

/-- The critical endpoint has exactly two cosets modulo Q_alpha. -/
theorem endpoint_image_index_two (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) :
    (Q R (alpha R)).relIndex (Z R s.endpoint) = 2 := by
  let T := Q R (beta R)
  let Q₀ := (Q R (alpha R)).subgroupOf T
  let E := (Z R s.endpoint).subgroupOf T
  have hET : Z R s.endpoint ≤ T := endpoint_le_edge common s hbc
  have hQT : Q R (alpha R) ≤ T := Q_le_adjacent_h R rfl (base_adjacent R)
  let : Q₀.Normal := normal_subgroupOf_of_le_normalizer
    ((show T ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Q_normalized R _))
  have hQi : Q₀.index = 4 := radius.edge_Q_index _ _ rfl (base_adjacent R)
  have hd : Q₀.relIndex E ∣ 4 := hQi ▸ Q₀.relIndex_dvd_index_of_normal E
  have hne : Q₀.relIndex E ≠ 1 := by
    rw [relIndex_subgroupOf hET]
    intro h
    exact (common.critical_reverse _ rfl _
      (critical_endpoint_color R (alpha R) rfl _ s.critical) s.critical).2
      (relIndex_eq_one.mp h)
  have hfour : Q₀.relIndex E ≠ 4 := by
    intro hi
    have hm := relIndex_mul_index (show Q₀ ≤ E ⊔ Q₀ from le_sup_right)
    rw [relIndex_sup_right, hi, hQi] at hm
    have hgen : E ⊔ Q₀ = ⊤ := index_eq_one.mp (by omega)
    have hh := congrArg (Subgroup.map T.subtype) hgen
    dsimp only [E, Q₀] at hh
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hET,
      map_subgroupOf_eq_of_le hQT, ← MonoidHom.range_eq_map, range_subtype] at hh
    have hc : ⁅Z R (alpha R), Z R s.endpoint⁆ = ⁅Z R (alpha R), T⁆ :=
      commutator_eq_of_centralizing_sup ((sup_comm _ _).trans hh)
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (geometry.centralizes _ rfl)))
        ((hET.trans (show T ≤ stabilizer R (alpha R) from
          fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R)))).trans (Z_normalized R _))
    have hn := endpoint_auxiliary_card_two common s
    rw [hc] at hn
    dsimp only [T] at hn
    rw [radius.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)] at hn
    omega
  have hf := Nat.mem_divisors.mpr ⟨hd, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1,2,4} : Finset ℕ) by decide] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  have hi : Q₀.relIndex E = 2 := by omega
  rwa [relIndex_subgroupOf hET] at hi

private theorem original_core_le (f : Seed.Frame source) (i : Bool) :
    Q R (alpha R) ≤ (f.core i).map (embedM R) := by
  rw [Q_alpha R source.two_group source.core_le]
  apply map_mono
  change pCore 2 M ≤ (f.parabolic i).pCoreIn 2
  apply le_pCoreIn_of_normalizes pCore_isPGroup _ le_normalizer_of_normal
  intro x hx
  change source.projection x ∈ modelParabolic f.flag (if i then !f.first else f.first)
  have he : source.projection x = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [source.projection_kernel]
  rw [he]
  exact one_mem _

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

/-- The compatible opposite intrinsic core contains the entire endpoint layer. -/
theorem endpoint_le_second_core (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    Z R s.endpoint ≤ (f.core true).map (embedM R) :=
  le_of_index_two_crossing _ _ _ (endpoint_image_index_two common radius s hbc)
    (original_core_le f true) hf.endpoint_selected

/-- The literal unstarred second layer is fixed by the endpoint modulo Z_alpha. -/
theorem secondLayer_endpoint_commutator_le_Z (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s) :
    ⁅d.preimage (secondLayer d f 1), Z R s.endpoint⁆ ≤ Z R (alpha R) :=
  (commutator_mono le_rfl (endpoint_le_second_core common radius s hbc f hf)).trans
    (secondLayer_commutator_le_Z d f)

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

/-- On the midpoint intersection, endpoint fixed points have index at most two.
The codomain is Z_c modulo its intersection with the original Z_alpha. -/
theorem intersection_endpoint_fixed_index_le_two
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle) :
    (commutatorPreimage (V R (alpha R) ⊓ Q R s.middle) (Z R s.endpoint)
      (Z R (alpha R))).relIndex (V R (alpha R) ⊓ Q R s.middle) ≤ 2 := by
  let K := V R (alpha R) ⊓ Q R s.middle
  let E := Z R s.endpoint
  let D := Z R s.middle
  let C := E ⊓ Q R (alpha R)
  have hEV : E ≤ V R s.middle :=
    le_iSup_of_le s.endpoint (le_iSup_of_le (by
      rw [SimpleGraph.dist_comm]; exact s.second_distance.le) le_rfl)
  have hKE : ⁅K, E⁆ ≤ D := by
    rw [commutator_comm]
    exact (commutator_mono hEV inf_le_right).trans
      (radius.commutator_le_Z _ s.middle_color)
  have hKD : K ≤ centralizer (D : Set (FreeAmalgam R)) :=
    inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ s.middle_color)))
  have hKC : ⁅K, C⁆ ≤ Z R (alpha R) :=
    (commutator_mono inf_le_left inf_le_right).trans (radius.commutator_le_Z _ rfl)
  have hEN : E ≤ normalizer (Z R (alpha R)) :=
    (source.critical_Z_le_stabilizer geometry (alpha R) rfl s.endpoint s.critical).2.trans
      (Z_normalized R _)
  have hCi : C.relIndex E = 2 := by
    rw [inf_relIndex_left]
    exact endpoint_image_index_two common radius s hbc
  let := Early.finite_radius common (alpha R) rfl
  let : Finite K := Finite.of_injective (inclusion (show K ≤ V R (alpha R) from inf_le_left))
    (inclusion_injective _)
  let := finite_stabilizer R s.middle
  let : Finite D := Finite.of_injective (inclusion (Z_le_stabilizer R s.middle))
    (inclusion_injective _)
  let := geometry.Z_elementary (lt_trans (by decide) common.large_distance)
    s.middle s.middle_color
  have hi := fixed_index_bound K E C (Z R (alpha R)) D hKE hKD inf_le_left hCi hKC hEN
  have hD : (Z R (alpha R)).relIndex D ≤ 2 := by
    have hh := relIndex_le_of_le_left
      (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      (show (Z R (beta R)).relIndex D ≠ 0 from index_ne_zero_of_finite)
    exact hh.trans_eq (radius.edge_Z_index s.middle (beta R) s.middle_color
      (adjacent_symm R hbc))
  exact hi.trans hD

private theorem index_le_four_of_crossing {G : Type*} [Group G]
    (C K V : Subgroup G) [Finite V] (hCV : C ≤ V) (hKV : K ≤ V)
    (hK : K.relIndex V ≤ 4) (hCK : C.relIndex K ≤ 2) (hcross : ¬ C ≤ K) :
    C.relIndex V ≤ 4 := by
  let : Finite C := Finite.of_injective (inclusion hCV) (inclusion_injective _)
  have hpos : K.relIndex C ≠ 0 := index_ne_zero_of_finite
  have hne : K.relIndex C ≠ 1 := fun h => hcross (relIndex_eq_one.mp h)
  have hlo : 2 ≤ K.relIndex C := by omega
  have h₁ := relIndex_inf_mul_relIndex C K V
  have h₂ := relIndex_inf_mul_relIndex K C V
  rw [inf_eq_left.mpr hKV] at h₁
  rw [inf_eq_left.mpr hCV, inf_comm K C] at h₂
  have hmul : C.relIndex K * K.relIndex V = K.relIndex C * C.relIndex V :=
    h₁.trans h₂.symm
  have hbound : C.relIndex K * K.relIndex V ≤ 8 := by
    calc _ ≤ 2 * 4 := Nat.mul_le_mul hCK hK
         _ = 8 := rfl
  nlinarith

/-- The opening endpoint estimate of (4.6.12)(5), for the supplied quotient
and compatible frame. Fixed vectors from the escaping unstarred layer reduce
the product of the two midpoint bounds by a factor of at least two. -/
theorem endpoint_fixed_index_le_four
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
      (V R (alpha R)) ≤ 4 := by
  let C := commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))
  let K := V R (alpha R) ⊓ Q R s.middle
  let := Early.finite_radius common (alpha R) rfl
  let : Finite K := Finite.of_injective (inclusion (show K ≤ V R (alpha R) from inf_le_left))
    (inclusion_injective _)
  apply index_le_four_of_crossing C K (V R (alpha R))
    (commutatorPreimage_le _ _ _) inf_le_left
    (radius_inf_kernel_index_le_four common radius rfl s.first_distance)
  · have hnorm : V R (alpha R) ≤ normalizer (Z R (alpha R)) :=
      (geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _)
    have hle : commutatorPreimage K (Z R s.endpoint) (Z R (alpha R)) ≤ C :=
      le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans inf_le_left)
        (commutator_commutatorPreimage_le _ _ _ (inf_le_left.trans hnorm))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans
      (intersection_endpoint_fixed_index_le_two common radius s hbc)
  · intro h
    have hU : d.preimage (secondLayer d f 1) ≤ C :=
      le_commutatorPreimage (d.preimage_le _)
        (secondLayer_endpoint_commutator_le_Z common radius s hbc d f hf)
    exact secondLayer_escape d f s.middle hescape (hU.trans (h.trans inf_le_right))

open Representation Representation.BinaryOffender

omit [Finite M] in
private theorem radius_normalized (m : M) :
    embedM R m ∈ normalizer (V R (alpha R)) := by
  apply DistanceEight.V_normalized R (alpha R)
  rw [alpha, stabilizer_m_base]
  exact ⟨m, rfl⟩

omit [Finite M] in
/-- Relative indices of literal quotient preimages are their binary codimensions. -/
theorem radius_preimage_relIndex (d : LayerModule source (V R (alpha R)))
    (A : Submodule (ZMod 2) d.Space) :
    (d.preimage A).relIndex (V R (alpha R)) = 2 ^ Module.finrank (ZMod 2) (d.Space ⧸ A) := by
  unfold LayerModule.preimage
  have he := relIndex_map_map_of_injective
    ((A.toAddSubgroup.toSubgroup).comap d.projection) (⊤ : Subgroup (V R (alpha R)))
    (V R (alpha R)).subtype_injective
  simp only [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at he
  rw [he, index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup]
  change Nat.card (d.Space ⧸ A) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

omit [Finite M] in
/-- Fixed spaces in the supplied module have the original ambient commutator
preimages, with the actor transported through the same source projection. -/
theorem radius_fixed_preimage (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) (H : Subgroup M) :
    d.preimage (fixedSpace d.representation (H.map source.projection)) =
      commutatorPreimage (V R (alpha R)) (H.map (embedM R)) (Z R (alpha R)) := by
  apply le_antisymm
  · exact le_commutatorPreimage (d.preimage_le _)
      (d.preimage_commutator_le_Z _ H (by
        rintro _ ⟨m, _, rfl⟩; exact radius_normalized m) le_rfl)
  · intro x hx
    have hxV := commutatorPreimage_le _ _ _ hx
    apply (d.mem_preimage_iff _ x).mpr
    refine ⟨hxV, ?_⟩
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    apply (d.fixed_iff_commutator_mem m (radius_normalized m) ⟨x, hxV⟩).mpr
    have hh := commutator_commutatorPreimage_le (V R (alpha R)) (H.map (embedM R))
      (Z R (alpha R)) ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _))
    rw [commutator_comm] at hh
    exact hh (commutator_mem_commutator (mem_map_of_mem _ hm) hx)

/-- Source B is the preimage of the whole-quotient fixed space. The actual
local residual surjects onto SL3(2), so the full finite actor has the same fixed points. -/
theorem radius_global_fixed_preimage (common : CommonFacts R source geometry)
    (d : LayerModule source (V R (alpha R))) :
    d.preimage (fixedSpace d.representation ⊤) =
      B R (alpha R) (geometry.Z_normal (alpha R)) := by
  have hV := geometry.V_local (alpha R) rfl common.large_distance
  have hL : L.map source.projection = ⊤ := by
    have hm := congrArg (Subgroup.map source.projection) source.residual_sup_core
    rw [Subgroup.map_sup, ← source.projection_kernel, Subgroup.map_ker_self,
      sup_bot_eq, map_top_of_surjective _ source.projection_surjective] at hm
    exact hm
  ext x
  rw [d.mem_preimage_iff, mem_B_iff R (alpha R) (geometry.Z_normal _) hV x]
  constructor
  · rintro ⟨hxV, hx⟩
    refine ⟨hxV, ?_⟩
    intro l hl
    rw [Ltilde_alpha, source.residual] at hl
    obtain ⟨m, hm, rfl⟩ := hl
    exact (d.fixed_iff_commutator_mem m (radius_normalized m) ⟨x, hxV⟩).mp
      (hx ⟨source.projection m, mem_top _⟩)
  · rintro ⟨hxV, hx⟩
    refine ⟨hxV, ?_⟩
    intro g
    obtain ⟨m, hm, he⟩ := hL.ge (mem_top g.val)
    change d.representation g.val (d.projection ⟨x, hxV⟩).toAdd = _
    rw [← he]
    apply (d.fixed_iff_commutator_mem m (radius_normalized m) ⟨x, hxV⟩).mpr
    apply hx
    rw [Ltilde_alpha, source.residual]
    exact mem_map_of_mem _ hm

/-- The actual endpoint estimate bounds the quotient by B, via three conjugate
involutions generating the same marked SL3(2). No module-recognition conclusion is used. -/
theorem radius_index_le_sixty_four_of_endpoint_bound
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R)))
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) :
    (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64 := by
  let E := (Z R s.endpoint).comap (embedM R)
  let A := E.map source.projection
  have hecol := critical_endpoint_color R (alpha R) rfl _ s.critical
  have hES : Z R s.endpoint ≤ Mbar R := by
    have h := (source.critical_Z_le_stabilizer geometry (alpha R) rfl s.endpoint s.critical).2
    simpa only [alpha, stabilizer_m_base] using h
  have hE : E.map (embedM R) = Z R s.endpoint := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hES
  have hidx : 2 ^ fixedCodim d.representation A ≤ 4 := by
    have hpre := radius_fixed_preimage common d E
    rw [hE] at hpre
    rw [← hpre, radius_preimage_relIndex] at hendpoint
    exact hendpoint
  have hcod : fixedCodim d.representation A ≤ 2 := by
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx
  have hnot := (common.critical_reverse _ rfl _ hecol s.critical).2
  obtain ⟨e, he, heQ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨m, rfl⟩ := hES he
  have hm : m ∈ E := he
  have hne : source.projection m ≠ 1 := by
    intro hh
    apply heQ
    rw [Q_alpha R source.two_group source.core_le]
    apply mem_map_of_mem
    rw [← source.projection_kernel]
    exact hh
  have htwo : source.projection m ^ 2 = 1 := by
    rw [← map_pow]
    have hm2 : m ^ 2 = 1 := by
      apply embedM_injective R
      rw [map_pow, map_one]
      let := geometry.Z_elementary (lt_trans (by decide) common.large_distance) s.endpoint hecol
      exact elemPow_eq_one_of_isElementaryAbelian _ he
    rw [hm2, map_one]
  have hcyclic : fixedCodim d.representation (zpowers (source.projection m)) ≤ 2 := by
    have hle : zpowers (source.projection m) ≤ A := zpowers_le.mpr (mem_map_of_mem _ hm)
    have hdim := Submodule.finrank_mono (fixedSpace_antitone d.representation hle)
    have h₁ := fixedCodim_add_finrank d.representation A
    have h₂ := fixedCodim_add_finrank d.representation (zpowers (source.projection m))
    omega
  have htop := ModuleAlternatives.Models.fixedCodim_top_le_three_mul
    d.representation (source.projection m) htwo hne
  have htotal : fixedCodim d.representation ⊤ ≤ 6 := by omega
  rw [← radius_global_fixed_preimage common d, radius_preimage_relIndex]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) htotal

/-- Both numerical estimates at the opening of source (4.6.12)(5). -/
theorem endpoint_and_radius_bounds
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) (f : Seed.Frame source)
    (hf : Seed.Compatible f s)
    (hescape : ¬ d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle) :
    (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4 ∧
      (B R (alpha R) (geometry.Z_normal (alpha R))).relIndex (V R (alpha R)) ≤ 64 := by
  have he := endpoint_fixed_index_le_four common radius s hbc d f hf hescape
  exact ⟨he, radius_index_le_sixty_four_of_endpoint_bound common s d he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
