module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import Theory.Frattini.BinarySquares

/-!
# The finite seed and pairing bounds in MS93 (4.6.8)(2)

All groups are literal preimages under the original embedding of M. The seed
is Z_alpha joined with one M-conjugate of Z_middle. Its M-normal closure is
exactly V₀. Involution generation and the assumed midpoint commutator bound
put the Frattini subgroup of this closure in U_alpha. The bad midpoint triple
makes the pairing with V_alpha nonzero, while the earlier edge commutator
bounds its order by four. The natural coordinates on U_alpha retain the
original quotient marking, including its possible graph automorphism.

These are the group-theoretic inputs to (1.7)(i). Selecting the seed conjugate
with the required opposite-parabolic module remains a separate obligation;
no single-section conclusion or final flag bound is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), pp.847--848, and
(4.6.8), claim (2), printed p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The literal preimage of an amalgam subgroup in the original finite group. -/
def layer (A : Subgroup (FreeAmalgam R)) : Subgroup M := A.comap (embedM R)

/-- Mapping a local preimage back recovers the original subgroup exactly. -/
theorem map_layer (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) : (layer A).map (embedM R) = A := by
  apply map_comap_eq_self
  simpa only [alpha, stabilizer_m_base, Mbar] using hA

/-- Only normalization by the M-vertex stabilizer is needed for normality in M. -/
theorem layer_normal (A : Subgroup (FreeAmalgam R))
    (hA : stabilizer R (alpha R) ≤ normalizer A) : (layer A).Normal := by
  constructor
  intro x hx g
  change embedM R (g * x * g⁻¹) ∈ A
  rw [map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.mp (hA (show embedM R g ∈ stabilizer R (alpha R) from
    by rw [alpha, stabilizer_m_base]; exact ⟨g, rfl⟩)) (embedM R x)).mp hx

/-- Commutators of local subgroups commute with the original embedding. -/
theorem layer_commutator (A B : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R)) (hB : B ≤ stabilizer R (alpha R)) :
    layer ⁅A, B⁆ = ⁅layer A, layer B⁆ := by
  apply map_injective (embedM_injective R)
  rw [map_commutator, map_layer A hA, map_layer B hB,
    map_layer _ ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB))]

/-- The natural central layer U_alpha in M. -/
noncomputable def naturalLayer : Subgroup M := layer (U R (alpha R))
/-- The pairing group W = V_alpha in M. -/
noncomputable def radiusLayer : Subgroup M := layer (V R (alpha R))
/-- The elementary central layer Z_alpha in M. -/
noncomputable def centralLayer : Subgroup M := layer (Z R (alpha R))
/-- The actual generated subgroup V₀ in M. -/
noncomputable def spanLayer (p : FlagCriticalData source geometry i) : Subgroup M :=
  layer (midpointSpan p)
/-- The selected midpoint generator in M. -/
noncomputable def middleLayer (p : FlagCriticalData source geometry i) : Subgroup M :=
  layer (Z R p.middle)
/-- The candidate X_alpha, enlarged by Z_alpha and conjugated inside M. -/
noncomputable def seed (p : FlagCriticalData source geometry i) (g : M) : Subgroup M :=
  centralLayer (R := R) ⊔ (middleLayer p).map (MulAut.conj g).toMonoidHom

instance naturalLayer_normal : (naturalLayer (R := R)).Normal :=
  layer_normal _ (U_normalized _)
instance radiusLayer_normal : (radiusLayer (R := R)).Normal :=
  layer_normal _ (DistanceEight.V_normalized R _)
instance centralLayer_normal : (centralLayer (R := R)).Normal :=
  layer_normal _ (Z_normalized R _)
instance spanLayer_normal (p : FlagCriticalData source geometry i) : (spanLayer p).Normal :=
  layer_normal _ (span_normalized p)

theorem map_naturalLayer : (naturalLayer (R := R)).map (embedM R) = U R (alpha R) :=
  map_layer _ ((U_le_Z _).trans (Z_le_stabilizer R _))
theorem map_centralLayer : (centralLayer (R := R)).map (embedM R) = Z R (alpha R) :=
  map_layer _ (Z_le_stabilizer R _)
theorem map_radiusLayer (common : CommonFacts R source geometry) :
    (radiusLayer (R := R)).map (embedM R) = V R (alpha R) :=
  map_layer _ (geometry.V_local _ rfl common.large_distance)
theorem map_spanLayer (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    (spanLayer p).map (embedM R) = midpointSpan p :=
  map_layer _ ((span_le_radius p).trans (geometry.V_local _ rfl common.large_distance))
theorem map_middleLayer (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    (middleLayer p).map (embedM R) = Z R p.middle :=
  map_layer _ (((middle_le_span p).trans (span_le_radius p)).trans
    (geometry.V_local _ rfl common.large_distance))

theorem map_seed (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    (seed p g).map (embedM R) = Z R (alpha R) ⊔ localConjugate (Z R p.middle) g := by
  rw [seed, Subgroup.map_sup, map_centralLayer]
  have he : (embedM R).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (embedM R g)).toMonoidHom.comp (embedM R) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv]
  rw [map_map, he, ← map_map, map_middleLayer common p]
  rfl

/-- Every candidate seed is contained in V₀. -/
theorem seed_le_span [Finite M] (p : FlagCriticalData source geometry i) (g : M) :
    seed p g ≤ spanLayer p := by
  refine sup_le (comap_mono (Z_le_span p)) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (inferInstance : (spanLayer p).Normal).conj_mem x
    ((middle_le_span p) hx) g

/-- The natural central group is contained in every candidate seed. -/
theorem naturalLayer_le_seed (p : FlagCriticalData source geometry i) (g : M) :
    naturalLayer (R := R) ≤ seed p g :=
  (comap_mono (U_le_Z _)).trans le_sup_left

/-- The pairing group lies in the genuine extension core. -/
theorem radiusLayer_le_core [Finite M] (common : CommonFacts R source geometry) :
    radiusLayer (R := R) ≤ RankOnePairing.extensionCore source.projection := by
  rw [pairing_core, source.projection_kernel, ← Q_alpha_comap R source.two_group source.core_le]
  exact comap_mono (V_le_Q geometry common.large_distance _ rfl)

/-- Each candidate seed lies in the genuine extension core. -/
theorem seed_le_core [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    seed p g ≤ RankOnePairing.extensionCore source.projection :=
  ((seed_le_span p g).trans (comap_mono (span_le_radius p))).trans
    (radiusLayer_le_core common)

/-- Every conjugate seed has exactly V₀ as its M-normal closure. -/
theorem generated_seed [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    RankOnePairing.generated (seed p g) = spanLayer p := by
  apply le_antisymm (RankOnePairing.generated_le _ _ (seed_le_span p g))
  let D := RankOnePairing.generated (seed p g)
  have hmiddle : middleLayer p ≤ D := by
    intro x hx
    have hh : g * x * g⁻¹ ∈ D :=
      le_normalClosure ((le_sup_right : (middleLayer p).map (MulAut.conj g).toMonoidHom ≤
        seed p g) (mem_map_of_mem _ hx))
    have hd := (inferInstance : D.Normal).conj_mem _ hh g⁻¹
    have he : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [he] at hd
  have hN : stabilizer R (alpha R) ≤ normalizer (D.map (embedM R)) := by
    rintro x hx
    obtain ⟨m, rfl⟩ := (show x ∈ (embedM R).range from by simpa only [alpha, stabilizer_m_base, Mbar] using hx)
    exact le_normalizer_map (embedM R)
      (mem_map_of_mem _ (show m ∈ normalizer D from by simp only [normalizer_eq_top, mem_top]))
  have hm : Z R p.middle ≤ D.map (embedM R) := by
    rw [← map_middleLayer common p]
    exact map_mono hmiddle
  have hs : midpointSpan p ≤ D.map (embedM R) :=
    iSup_conjugates_le_of_le_normalizer _ _ _ hm hN
  intro x hx
  obtain ⟨y, hy, he⟩ := hs hx
  exact (embedM_injective R he) ▸ hy

/-- Actual equivariant coordinates on U_alpha with the original quotient marking. -/
noncomputable def naturalCoordinates (common : CommonFacts R source geometry) :
    RankOnePairing.NaturalFactor source.projection
      (RankOnePairing.component source.projection source.flag) (naturalLayer (R := R)) ⊥ := by
  let e : naturalLayer (R := R) ≃* U R (alpha R) :=
    ((naturalLayer (R := R)).equivMapOfInjective (embedM R) (embedM_injective R)).trans
      (MulEquiv.subgroupCongr map_naturalLayer)
  let f := e.trans common.natural.equiv
  refine {
    marking := common.natural.marking
    coordinates := f.toMonoidHom
    surjective := f.surjective
    kernel := ?_
    normalized := le_normalizer_of_normal
    action := ?_ }
  · simpa only [bot_subgroupOf] using f.toMonoidHom.ker_eq_bot_iff.mpr f.injective
  · intro l hl x y hy
    exact common.natural.action l (e x) (e y) (by
      change embedM R (y : M) = embedM R l * embedM R (x : M) * (embedM R l)⁻¹
      rw [hy, map_mul, map_mul, map_inv])

/-- The midpoint normal span is generated by involutions. -/
theorem span_omegaOne (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) : omegaOneAmbient (midpointSpan p) = midpointSpan p := by
  apply le_antisymm (omegaOneAmbient_le _)
  change (⨆ g : stabilizer R (alpha R),
    (Z R p.middle).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) ≤ _
  apply iSup_le
  intro g
  let : IsElementaryAbelian 2 (Z R p.middle) := by
    rw [← common.X_eq_Z _ p.middle_color]
    exact omegaCenter_elementary _
  let : IsElementaryAbelian 2
      ((Z R p.middle).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) :=
    IsElementaryAbelian.map _
  rw [← omegaOneAmbient_eq_self ((Z R p.middle).map
    (MulAut.conj (g : FreeAmalgam R)).toMonoidHom)]
  apply omegaOneAmbient_mono
  exact le_iSup (fun g : stabilizer R (alpha R) =>
    (Z R p.middle).map (MulAut.conj (g : FreeAmalgam R)).toMonoidHom) g

private theorem square_mem_derived {G : Type*} [Group G] (P : Subgroup G)
    (hP : omegaOneAmbient P = P) (x : P) : (x : G) ^ 2 ∈ ⁅P, P⁆ := by
  let f : P →* Abelianization P := (powMonoidHom 2).comp Abelianization.of
  have hle : P ≤ f.ker.map P.subtype := by
    conv_lhs => rw [← hP]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hy2
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    change (Abelianization.of (⟨y, hy⟩ : P)) ^ 2 = 1
    rw [← map_pow, show (⟨y, hy⟩ : P) ^ 2 = 1 from Subtype.ext hy2, map_one]
  obtain ⟨y, hy, he⟩ := hle x.property
  change (y : G) = x at he
  have hpow : y ^ 2 ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    change Abelianization.of (y ^ 2) = 1
    rw [map_pow]
    exact hy
  have hh := mem_map_of_mem P.subtype hpow
  rw [map_subtype_commutator] at hh
  simpa only [subtype_apply, coe_pow, he] using hh

/-- The seed hypothesis puts the actual Frattini subgroup of V₀ in U_alpha. -/
theorem spanLayer_frattini [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    (frattini (spanLayer p)).map (spanLayer p).subtype ≤ naturalLayer (R := R) := by
  have hp : IsPGroup 2 (spanLayer p) :=
    (RankOnePairing.extensionCore_isPGroup source.projection).to_le
      ((comap_mono (span_le_radius p)).trans (radiusLayer_le_core common))
  rw [hp.frattini_eq_closure_squares, map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  have hderived : ⁅midpointSpan p, midpointSpan p⁆ ≤ U R (alpha R) :=
    (commutator_mono le_rfl
      ((span_le_radius p).trans (V_le_Q geometry common.large_distance _ rfl))).trans
      (span_commutator_le_U common p hseed)
  have hs := hderived (square_mem_derived _ (span_omegaOne common p)
    ⟨embedM R (x : M), x.property⟩)
  simpa only [SetLike.mem_coe, naturalLayer, layer, mem_comap, subtype_apply, coe_pow, map_pow] using hs

/-- The full seed commutator with V_alpha lies in U_alpha. -/
theorem seed_commutator_le [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) (g : M) :
    ⁅seed p g, radiusLayer (R := R)⁆ ≤ naturalLayer (R := R) := by
  have hh : ⁅spanLayer p, radiusLayer (R := R)⁆ ≤ naturalLayer (R := R) := by
    change ⁅layer (midpointSpan p), layer (V R (alpha R))⁆ ≤ _
    rw [← layer_commutator _ _
      ((span_le_radius p).trans (geometry.V_local _ rfl common.large_distance))
      (geometry.V_local _ rfl common.large_distance)]
    exact comap_mono ((commutator_mono le_rfl
      (V_le_Q geometry common.large_distance _ rfl)).trans
      (span_commutator_le_U common p hseed))
  exact (commutator_mono (seed_le_span p g) le_rfl).trans hh

/-- Z_alpha centralizes the pairing group V_alpha. -/
theorem centralLayer_centralizes_radius (common : CommonFacts R source geometry) :
    centralLayer (R := R) ≤ centralizer (radiusLayer (R := R) : Set M) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply map_injective (embedM_injective R)
  rw [map_commutator, map_centralLayer, map_radiusLayer common, Subgroup.map_bot]
  exact bot_unique ((commutator_mono le_rfl
    (V_le_Q geometry common.large_distance _ rfl)).trans (geometry.centralizes _ rfl).le)

/-- Enlarging a conjugated midpoint by Z_alpha does not change its pairing. -/
theorem seed_commutator (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    ⁅seed p g, radiusLayer (R := R)⁆ =
      (⁅middleLayer p, radiusLayer (R := R)⁆).map (MulAut.conj g).toMonoidHom := by
  have hs := commutator_eq_of_centralizing_sup (V := radiusLayer (R := R))
    (C := centralLayer (R := R)) (X := (middleLayer p).map (MulAut.conj g).toMonoidHom)
    rfl (centralLayer_centralizes_radius common) le_normalizer_of_normal
  have hw : (radiusLayer (R := R)).map (MulAut.conj g).toMonoidHom =
      radiusLayer (R := R) := Normal.map_conj_eq _ g
  rw [map_commutator, hw]
  rw [commutator_comm, commutator_comm ((middleLayer p).map (MulAut.conj g).toMonoidHom)]
  exact hs.symm

/-- The selected bad triple forces a nonzero midpoint pairing. -/
theorem middle_commutator_ne_bot (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) :
    ⁅middleLayer p, radiusLayer (R := R)⁆ ≠ ⊥ := by
  intro h
  have hh := congrArg (Subgroup.map (embedM R)) h
  rw [map_commutator, map_middleLayer common p, map_radiusLayer common, Subgroup.map_bot] at hh
  have hcent := commutator_eq_bot_iff_le_centralizer.mp hh
  have hK : flagResidual source i ≤ normalizer (V R (alpha R)) :=
    ((flagResidual_le source i).trans (flagParabolic_le source i)).trans
      (DistanceEight.V_normalized R _)
  have htriple : ⁅⁅Z R p.middle, flagResidual source i⁆, V R (alpha R)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      ((commutator_mono hcent le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hK.trans (normalizer_le_normalizer_centralizer _))))
  exact p.middle_triple (htriple.le.trans bot_le)

/-- Every conjugate seed retains the nonzero pairing required by (1.7). -/
theorem seed_commutator_nontrivial [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    Nat.card (⁅seed p g, radiusLayer (R := R)⁆ : Subgroup M) ≠ 1 := by
  rw [seed_commutator common p g, card_map_of_injective (MulAut.conj g).injective]
  intro h
  exact middle_commutator_ne_bot common p (eq_bot_of_card_eq _ h)

/-- The actual edge commutator of order four bounds the seed pairing. -/
theorem seed_commutator_card_le [Finite M] (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i) (g : M) :
    Nat.card (⁅seed p g, radiusLayer (R := R)⁆ : Subgroup M) ≤ 4 := by
  rw [seed_commutator common p g, card_map_of_injective (MulAut.conj g).injective]
  rw [← card_map_of_injective (f := embedM R) (embedM_injective R),
    map_commutator, map_middleLayer common p, map_radiusLayer common]
  have hcard := early.edge_commutator_card p.middle (beta R) p.middle_color
    (adjacent_symm R p.middle_neighbor)
  let : Finite (⁅Z R p.middle, Q R (beta R)⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hVQ : V R (alpha R) ≤ Q R (beta R) :=
    (V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R (show color R (beta R) = true from rfl) (base_adjacent R))
  exact (card_le_of_le (commutator_mono le_rfl hVQ)).trans_eq hcard

/-- The Section 1 component maps to the original vertex two-residual. -/
theorem map_component [Finite M] :
    (RankOnePairing.component source.projection source.flag).map (embedM R) =
      Ltilde R (alpha R) := by
  rw [RankOnePairing.component, source.rank_one_generation, Ltilde_alpha, source.residual]

/-- Z_alpha lies in the actual preimage of the global fixed quotient. -/
theorem centralLayer_le_fixedPreimage [Finite M] (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i) (g : M) :
    centralLayer (R := R) ≤ RankOnePairing.fixedPreimage
      (RankOnePairing.component source.projection source.flag) (seed p g)
      (naturalLayer (R := R)) := by
  have hc : ⁅RankOnePairing.component source.projection source.flag,
      centralLayer (R := R)⁆ ≤ naturalLayer (R := R) := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator, map_component, map_centralLayer, map_naturalLayer, commutator_comm]
    exact le_rfl
  intro x hx
  apply (RankOnePairing.mem_fixedPreimage _ _ _ x).mpr
  refine ⟨?_, fun l hl => hc (commutator_mem_commutator hl hx)⟩
  rw [generated_seed common p g]
  exact Z_le_span p hx

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
