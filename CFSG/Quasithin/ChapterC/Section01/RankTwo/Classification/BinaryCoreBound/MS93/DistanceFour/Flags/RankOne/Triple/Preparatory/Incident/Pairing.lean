module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Coverage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Locality
/-!
# Incident pairing infrastructure for MS93 (4.6.8)(3)

This module proves the concrete binary actor supplement used in the p.906
argument: the first marked parabolic core joins the opposite ordered residual
to the full parabolic. It transports that identity to every incident flag,
constructs the finite relative normality of the fixed-space seed and its
normal closure, and proves the contradiction once the genuine `(1.7)(i)`
application supplies the two displayed commutator bounds. The final source
application is kept explicit because `FlagNaturalSection` lives in the free
amalgam while `RankOnePairing.SourceData` is a finite ambient-group record.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), printed pp.847--848 and p.906.
-/

public section
open scoped commutatorElement
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing
private theorem supplement_of_index_two {G : Type*} [Group G]
    (A K P : Subgroup G) (hA : A ≤ P) (hK : K ≤ P)
    (hindex : A.relIndex P = 2) (hx : ∃ x ∈ K, x ∉ A) : K ⊔ A = P := by
  have hle : K ⊔ A ≤ P := sup_le hK hA
  have hmul := relIndex_mul_relIndex A (K ⊔ A) P le_sup_right hle
  rw [hindex] at hmul
  have hne : A.relIndex (K ⊔ A) ≠ 1 := by
    intro h
    obtain ⟨x, hxK, hxA⟩ := hx
    exact hxA ((relIndex_eq_one.mp h) ((le_sup_left : K ≤ K ⊔ A) hxK))
  have ha : 2 ≤ A.relIndex (K ⊔ A) := by
    have hz : A.relIndex (K ⊔ A) ≠ 0 := by intro h; simp [h] at hmul
    omega
  have hb : 1 ≤ (K ⊔ A).relIndex P := by
    have hz : (K ⊔ A).relIndex P ≠ 0 := by intro h; simp [h] at hmul
    omega
  have he : (K ⊔ A).relIndex P = 1 := by nlinarith
  exact le_antisymm hle (relIndex_eq_one.mp he)

private def transvection : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩

private theorem point_core_supplements_line :
    pointParabolicSL.pCoreIn 2 ⊔ residual lineParabolicSL = lineParabolicSL := by
  rw [MarkedProduct.pointParabolic_core, line_residual]
  have hA : lineA ≤ lineParabolicSL := by rw [← line_residual]; exact map_subtype_le _
  have hK : pointV ≤ lineParabolicSL := by
    intro g hg
    rw [mem_lineParabolicSL_iff]
    exact ⟨hg.2.2.1, hg.2.2.2.2.2.1⟩
  apply supplement_of_index_two lineA pointV lineParabolicSL hA hK
  · have hm := (lineA.subgroupOf lineParabolicSL).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv,
      ← line_residual, card_line_residual, card_lineParabolicSL] at hm
    change (residual lineParabolicSL).relIndex lineParabolicSL * 12 = 24 at hm
    rw [line_residual] at hm
    omega
  · exact ⟨transvection, by decide, by decide⟩


private theorem diagram_line : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  rw [← pointParabolic_map_diagram, map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact diagram_involutive x
  rw [he, map_id]

private theorem line_core_supplements_point :
    lineParabolicSL.pCoreIn 2 ⊔ residual pointParabolicSL = pointParabolicSL := by
  have hm := congrArg (Subgroup.map diagram.toMonoidHom) point_core_supplements_line
  rw [Subgroup.map_sup, map_pCoreIn_of_injective 2 _ _ diagram.injective,
    pointParabolic_map_diagram, MarkedAutomorphisms.residual, map_embedded_pResidual, diagram_line] at hm
  exact hm

/-- The opposite core supplements the actual two-residual at either marked flag. -/
theorem model_core_sup_residual (g : SL) (i : Bool) :
    (modelParabolic g i).pCoreIn 2 ⊔
      residual (modelParabolic g (!i)) = modelParabolic g (!i) := by
  let P := if i then lineParabolicSL else pointParabolicSL
  let S := if !i then lineParabolicSL else pointParabolicSL
  have he : P.pCoreIn 2 ⊔ residual S = S := by
    cases i
    · exact point_core_supplements_line
    · exact line_core_supplements_point
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [Subgroup.map_sup, map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    MarkedAutomorphisms.residual, map_embedded_pResidual] at hm
  exact hm

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Lift the model supplement through the genuine two-group kernel. -/
theorem parabolic_core_sup_residual (source : LocalSource L R) (i : Bool) :
    (parabolic source.projection source.flag i).pCoreIn 2 ⊔
      rankOne (parabolic source.projection source.flag (!i)) =
        parabolic source.projection source.flag (!i) := by
  let K := (parabolic source.projection source.flag i).pCoreIn 2
  let P := parabolic source.projection source.flag (!i)
  have hk : source.projection.ker ≤ K := by
    rw [show K = ((modelParabolic source.flag i).pCoreIn 2).comap source.projection from
      parabolic_core_eq_comap source i]
    exact MonoidHom.ker_le_comap _ _
  have hmap : (K ⊔ rankOne P).map source.projection = P.map source.projection := by
    rw [Subgroup.map_sup, rankOne_parabolic_eq source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup), map_embedded_pResidual]
    have hK : K.map source.projection = (modelParabolic source.flag i).pCoreIn 2 := by
      rw [show K = ((modelParabolic source.flag i).pCoreIn 2).comap source.projection from
        parabolic_core_eq_comap source i]
      exact map_comap_eq_self_of_surjective source.projection_surjective _
    have hP : P.map source.projection = modelParabolic source.flag (!i) :=
      map_comap_eq_self_of_surjective source.projection_surjective _
    rw [hK, hP]
    exact model_core_sup_residual source.flag i
  have hkerP : source.projection.ker ≤ P := MonoidHom.ker_le_comap _ _
  have he := congrArg (Subgroup.comap source.projection) hmap
  rw [comap_map_eq_self (hk.trans le_sup_left), comap_map_eq_self hkerP] at he
  exact he

/-- At the base flag, Q_delta1 supplements tilde L_delta2 to the full actor. -/
theorem flagKernel_sup_oppositeResidual (source : LocalSource L R) (i : Bool) :
    flagKernel source i ⊔ flagResidual source (!i) = flagParabolic source (!i) := by
  have he := congrArg (Subgroup.map (embedM R)) (parabolic_core_sup_residual source i)
  rwa [Subgroup.map_sup] at he

/-- The supplement keeps the first core fixed at every incident opposite flag. -/
theorem flagKernel_sup_incidentResidual (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    flagKernel source i ⊔ localFlagResidual source (!i) d =
      localFlagActor source (!i) d := by
  obtain ⟨m, hm, hdm⟩ := (flagIncident_one_iff source i d).mp hd
  have hr : localFlagResidual source (!i) m = localFlagResidual source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagResidual_right_mul source (!i) d (d⁻¹ * m) hdm
  have ha : localFlagActor source (!i) m = localFlagActor source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source (!i) d (d⁻¹ * m) hdm
  have hk : localConjugate (flagKernel source i) m = flagKernel source i :=
    mem_normalizer_iff_map_conj_eq.mp
      (flagKernel_normalized source i (mem_map_of_mem (embedM R) hm))
  have he := congrArg (fun H => localConjugate H m) (flagKernel_sup_oppositeResidual source i)
  change (flagKernel source i ⊔ flagResidual source (!i)).map _ = _ at he
  rw [Subgroup.map_sup] at he
  change localConjugate (flagKernel source i) m ⊔ localFlagResidual source (!i) m =
    localFlagActor source (!i) m at he
  rwa [hk, hr, ha] at he


/-- An incident opposite core acts on the first flag layer through its full parabolic. -/
theorem incidentKernel_le_flagParabolic (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    localFlagKernel source (!i) d ≤ flagParabolic source i := by
  obtain ⟨m, hm, hdm⟩ := (flagIncident_one_iff source i d).mp hd
  have hk : localFlagKernel source (!i) m = localFlagKernel source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source (!i) d (d⁻¹ * m) hdm
  rw [← hk]
  have hbase : flagKernel source (!i) ≤ flagParabolic source i := by
    simpa only [Bool.not_not] using flagKernel_le_oppositeActor source (!i)
  exact (map_mono hbase).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    ((flagParabolic source i).le_normalizer (mem_map_of_mem (embedM R) hm)))

omit [Finite M] in
/-- Relative normality of each translated local core in its own full actor. -/
theorem localFlagKernel_normalized (source : LocalSource L R) (j : Bool) (d : M) :
    localFlagActor source j d ≤ normalizer (localFlagKernel source j d) :=
  (map_mono (flagKernel_normalized source j)).trans (le_normalizer_map _)

/-- The seed for the opposite parabolic in the application of (1.7). -/
@[expose] noncomputable def seed (source : LocalSource L R) (i : Bool) (d : M) :
    Subgroup (FreeAmalgam R) :=
  Z R (alpha R) ⊔ ⁅V R (beta R), localFlagKernel source (!i) d⁆

/-- The global normal closure is taken only in the finite vertex stabilizer. -/
@[expose] noncomputable def span (source : LocalSource L R) (i : Bool) (d : M) :
    Subgroup (FreeAmalgam R) :=
  RankOnePairing.localGenerated (stabilizer R (alpha R)) (seed source i d)

/-- The local normal closure uses the first full parabolic. -/
@[expose] noncomputable def localSpan (source : LocalSource L R) (i : Bool) (d : M) :
    Subgroup (FreeAmalgam R) :=
  RankOnePairing.localGenerated (flagParabolic source i) (seed source i d)

/-- The literal preimage of the global fixed subgroup, before dividing by a central layer. -/
@[expose] noncomputable def fixed (source : LocalSource L R) (i : Bool) (d : M) :
    Subgroup (FreeAmalgam R) :=
  commutatorPreimage (span source i d) (Ltilde R (alpha R)) (Z R (alpha R))

/-- The seed remains in the elementary first layer. -/
theorem seed_le_firstLayer (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) : seed source i d ≤ V R (beta R) := by
  refine sup_le ?_ (le_normalizer_iff_commutator_le_left.mp
    ((incidentKernel_le_flagParabolic source i d hd).trans
      (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)))
  simpa only [firstFlagLayer, localConjugate_one] using Z_le_firstFlagLayer (R := R) (1 : M)

private theorem normalizes_commutator {G : Type*} [Group G] (P H K : Subgroup G)
    (hH : P ≤ normalizer H) (hK : P ≤ normalizer K) :
    P ≤ normalizer (⁅H,K⁆ : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro p hp x hx
  have he : (⁅H,K⁆).map (MulAut.conj p).toMonoidHom = ⁅H,K⁆ := by
    rw [map_commutator]
    have hH' : H.map (MulAut.conj p).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (hH hp)
    have hK' : K.map (MulAut.conj p).toMonoidHom = K :=
      mem_normalizer_iff_map_conj_eq.mp (hK hp)
    rw [hH', hK']
  exact he ▸ mem_map_of_mem (MulAut.conj p).toMonoidHom hx

private theorem normalizes_join_of_commutator {G : Type*} [Group G]
    (E Z H : Subgroup G) (hZ : E ≤ normalizer Z) (hcomm : ⁅H,E⁆ ≤ Z) :
    E ≤ normalizer (Z ⊔ H : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro e he x hx
  have hm : (Z ⊔ H).map (MulAut.conj e).toMonoidHom ≤ Z ⊔ H := by
    have hZ' : Z.map (MulAut.conj e).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (hZ he)
    rw [Subgroup.map_sup, hZ']
    refine sup_le le_sup_left ?_
    rintro _ ⟨y, hy, rfl⟩
    have hc : ⁅e,y⁆ ∈ Z := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator he hy)
    have hh := (Z ⊔ H).mul_mem ((le_sup_left : Z ≤ Z ⊔ H) hc)
      ((le_sup_right : H ≤ Z ⊔ H) hy)
    change e * y * e⁻¹ ∈ Z ⊔ H
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
  exact hm (mem_map_of_mem (MulAut.conj e).toMonoidHom hx)

/-- Under the contrary triple hypothesis the seed is normal in the opposite
full parabolic, using the first core as the supplement. -/
theorem seed_normalized (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    localFlagActor source (!i) d ≤ normalizer (seed source i d) := by
  have hZ : localFlagActor source (!i) d ≤ normalizer (Z R (alpha R)) :=
    (localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _)
  have hK : flagKernel source i ≤ normalizer
      (⁅V R (beta R), localFlagKernel source (!i) d⁆ : Subgroup (FreeAmalgam R)) :=
    normalizes_commutator _ _ _
      ((flagKernel_le source i).trans
        (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel))
      ((flagKernel_le_incidentActor source i d hd).trans
        (localFlagKernel_normalized source (!i) d))
  rw [← flagKernel_sup_incidentResidual source i d hd]
  apply sup_le
  · exact (le_inf ((flagKernel_le_incidentActor source i d hd).trans hZ) hK).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · apply normalizes_join_of_commutator _ _ _ _ htriple
    exact ((map_mono (flagResidual_le source (!i))) :
      localFlagResidual source (!i) d ≤ localFlagActor source (!i) d).trans hZ

/-- The normality required by SourceData is relative to the opposite actor. -/
theorem seed_normal (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ((seed source i d).subgroupOf (localFlagActor source (!i) d)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (seed_normalized source geometry hlarge i hkernel d hd htriple)


/-- The seed is in the local two-core at alpha. -/
theorem seed_le_Q (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) : seed source i d ≤ Q R (alpha R) :=
  (seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
    ((edgeRadius_le_radius _ _ rfl (base_adjacent R)).trans (V_le_Q geometry hlarge _ rfl))

/-- The genuine global closure stays in the radius layer. -/
theorem span_le_radius (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) : span source i d ≤ V R (alpha R) := by
  let S := stabilizer R (alpha R)
  let : ((V R (alpha R)).subgroupOf S).Normal :=
    normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R _)
  apply map_le_iff_le_comap.mpr
  change normalClosure _ ≤ (V R (alpha R)).subgroupOf S
  apply normalClosure_le_normal
  intro x hx
  exact ((seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
    (edgeRadius_le_radius _ _ rfl (base_adjacent R))) hx

omit [Finite M] in
/-- Normalization is by G_alpha, not by the infinite free amalgam. -/
theorem span_normalized (source : LocalSource L R) (i : Bool) (d : M) :
    stabilizer R (alpha R) ≤ normalizer (span source i d) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨y, hy, rfl⟩
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (inferInstance : (normalClosure ((seed source i d).subgroupOf
      (stabilizer R (alpha R)) : Set (stabilizer R (alpha R)))).Normal).conj_mem
      y hy ⟨g, hg⟩, rfl⟩

omit [Finite M] in
/-- Intrinsic normality needed for the common normalizer-transfer theorem. -/
theorem span_normal (source : LocalSource L R) (i : Bool) (d : M) :
    ((span source i d).subgroupOf (stabilizer R (alpha R))).Normal :=
  normal_subgroupOf_of_le_normalizer (span_normalized source i d)

/-- The seed is retained in its actual G_alpha-normal closure. -/
theorem seed_le_span (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) : seed source i d ≤ span source i d :=
  RankOnePairing.le_localGenerated _ _
    ((seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
      ((edgeRadius_le_radius _ _ rfl (base_adjacent R)).trans (geometry.V_local _ rfl hlarge)))

omit [Finite M] in
/-- The first-parabolic closure embeds in the G_alpha-normal closure. -/
theorem localSpan_le_span (source : LocalSource L R) (i : Bool) (d : M) :
    localSpan source i d ≤ span source i d := by
  let P := flagParabolic source i
  let : ((span source i d).subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((flagParabolic_le source i).trans (span_normalized source i d))
  apply map_le_iff_le_comap.mpr
  change normalClosure _ ≤ (span source i d).subgroupOf P
  apply normalClosure_le_normal
  intro x hx
  exact ⟨⟨x, flagParabolic_le source i x.property⟩, le_normalClosure hx, rfl⟩

/-- The full stabilizer is generated by its local component and two-core. -/
theorem stabilizer_eq_component_sup_core (source : LocalSource L R) :
    stabilizer R (alpha R) = Ltilde R (alpha R) ⊔ Q R (alpha R) := by
  have he := RankOnePairing.component_sup_extensionCore (pairingExtension source)
  rw [pairingExtension_projection, pairingExtension_flag, pairing_core,
    RankOnePairing.component, source.rank_one_generation, source.projection_kernel] at he
  have hm := congrArg (Subgroup.map (embedM R)) he
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map] at hm
  rw [Ltilde_alpha, source.residual, Q_alpha R source.two_group source.core_le]
  rw [alpha, stabilizer_m_base]
  exact hm.symm

/-- A Z_alpha element fixed by the component is central in the full stabilizer. -/
theorem Z_inf_fixedCore_le_center (source : LocalSource L R) (geometry : Geometry R) :
    Z R (alpha R) ⊓ fixedCore R (alpha R) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  intro x hx
  have hcent : x ∈ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R)) := by
    have hL : Ltilde R (alpha R) ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
      intro y hy z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hx.2.2 y hy).symm
    have hQ : Q R (alpha R) ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
      intro y hy z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ((commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes _ rfl)) hx.1 y hy).symm
    intro y hy
    rw [stabilizer_eq_component_sup_core source] at hy
    exact ((sup_le hL hQ) hy x (Set.mem_singleton x)).symm
  refine ⟨⟨x, Z_le_stabilizer R _ hx.1⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  exact Subtype.ext (hcent y y.property)

/-- The two genuine missing source calculations suffice for the contradiction.
The common normalizer transfer promotes the pairing's V_alpha-circ bound
without assuming a later radius decomposition. -/
theorem contradiction_of_pairing (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) (d : M) (hd : flagIncident source i 1 d)
    (hmoving : ⁅V R (beta R), flagResidual source i⁆ ≤ span source i d)
    (hpair : ⁅Vcirc R (alpha R), span source i d⁆ ≤ fixedCore R (alpha R)) : False := by
  have hSV := span_le_radius source geometry common.large_distance i hkernel d hd
  have hSQ := hSV.trans (V_le_Q geometry common.large_distance _ rfl)
  have hf := common.normalization_transfer _ rfl _ hSQ (span_normal source i d) hpair
  have hZ : ⁅V R (alpha R), span source i d⁆ ≤ Z R (alpha R) :=
    (commutator_mono le_rfl hSQ).trans (early.commutator_le_Z _ rfl)
  have hc := (le_inf hZ hf).trans (Z_inf_fixedCore_le_center source geometry)
  apply p.middle_triple
  rw [commutator_comm] at hc
  have hm : Z R p.middle ≤ V R (beta R) := by
    simpa only [firstFlagLayer, localConjugate_one] using p.middle_le_firstLayer
  exact (commutator_mono ((commutator_mono hm le_rfl).trans hmoving) le_rfl).trans hc


/-- Conditional final selection: the local natural-factor and pairing producers
must supply both premises before claim (3) is complete. -/
theorem exists_delta2_triple_of_pairing (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i)
    (hmoving : ∀ d, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) →
      ⁅V R (beta R), flagResidual source i⁆ ≤ span source i d)
    (hpair : ∀ d, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) →
      ⁅Vcirc R (alpha R), span source i d⁆ ≤ fixedCore R (alpha R)) :
    ∃ d : M, flagIncident source i 1 d ∧
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) ∧
      ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) := by
  obtain ⟨d, hd, hcross⟩ := exists_delta2 source geometry common hb i hkernel p
  refine ⟨d, hd, hcross, fun htriple => ?_⟩
  exact contradiction_of_pairing source geometry common early i hkernel p d hd
    (hmoving d hd hcross htriple) (hpair d hd hcross htriple)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing
