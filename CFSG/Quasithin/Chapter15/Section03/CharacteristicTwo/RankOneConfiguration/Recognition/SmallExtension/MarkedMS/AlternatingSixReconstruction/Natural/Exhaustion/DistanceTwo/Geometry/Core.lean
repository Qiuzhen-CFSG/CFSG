module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Contracts
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Local orbit identities from normal generation and the maximal plane

The non-Frattini branch places the normal orbit inside the two-core: an
escaping normal subgroup contains the residual and would put the whole
commutator core inside Z. Critical reversal and the maximal-plane identity
then put the entire core inside the orbit. Residual idempotence identifies
the component commutator. The edge's abelian quotient makes the orbit/core
commutator centralize the opposite Z-layer; normal generation promotes this
to centralization by the residual, and normal closure preserves the sharper
edge commutator bound.

These arguments are adapted from Chapter C's OrbitLarge, OrbitCore and
OrbitCommutator, and apply to central covers of the natural module.
Source: MS93 (3.3), (3.6), printed pp.866--871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)

/-- Structural source facts sufficient for all local orbit identities.
Only the maximal plane, rather than a natural subgroup complement, occurs. -/
structure LocalStructure : Prop where
  edge_centralizer : EdgeCentralizerCondition R
  normal_generation : ∀ (N : Subgroup M) [N.Normal],
    (¬ N ≤ pCore 2 M) → pResidual 2 M ≤ N
  radical_derived : ⁅R,R⁆ ≤ pCore 2 M
  plane_eq : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    criticalPlane R c b = Z R c ⊓ Q R (alpha R)
  image_two : ∀ c, CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    (Q R c).relIndex (Z R (alpha R)) = 2

private theorem endpoint_le_range (hb : geo.b R = 2) {c : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl)) :
    Z R c ≤ (embedM R).range :=
  (critical_Z_le_stabilizer R geo (alpha R) rfl
    (by change 0 < geo.b R; omega) hc).trans_eq (stabilizer_m_base R)

omit [Finite M] in
/-- Any escaping actor detects residual movement on a normal section. -/
theorem core_le_of_commutator_le (hs : LocalStructure geo)
    (N E : Subgroup M) [N.Normal] (hE : ¬ E ≤ pCore 2 M)
    (hcomm : ⁅pCore 2 M,E⁆ ≤ N) : ⁅pCore 2 M,pResidual 2 M⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let C := (centralizer ((pCore 2 M).map q : Set (M ⧸ N))).comap q
  have hC (A : Subgroup M) : A ≤ C ↔ ⁅pCore 2 M,A⁆ ≤ N := by
    change A ≤ (centralizer ((pCore 2 M).map q : Set (M ⧸ N))).comap q ↔ _
    rw [←map_le_iff_le_comap,←le_centralizer_iff,
      ←commutator_eq_bot_iff_le_centralizer,←map_commutator,
      Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  let : ((pCore 2 M).map q).Normal :=
    Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hEC : E ≤ C := (hC E).mpr hcomm
  exact (hC (pResidual 2 M)).mp (hs.normal_generation C (fun h => hE (hEC.trans h)))

theorem orbit_le_core (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hs : LocalStructure geo) (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    criticalOrbitNative R c b ≤ pCore 2 M := by
  by_contra hn
  have hK := hs.normal_generation (criticalOrbitNative R c b) hn
  have hKg : Ltilde R (alpha R) ≤ criticalOrbit R c b := by
    rw [Ltilde_alpha]
    exact map_mono hK
  have hcore : core R (alpha R) ≤ Z R (alpha R) :=
    (commutator_mono le_rfl hKg).trans (criticalOrbit_commutator_le geo hp hQR hb hc hab hcb)
  have hZ := geo.omega_bound (alpha R) rfl (by change 0 < geo.b R; omega)
  exact hlarge ((hcore.trans hZ).trans le_sup_right)

theorem core_le_orbit (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hs : LocalStructure geo) (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    core R (alpha R) ≤ criticalOrbit R c b := by
  let A := criticalOrbitNative R c b
  let E := (Z R c).comap (embedM R)
  have hrev := critical_reverse R geo hs.edge_centralizer (alpha R) rfl
    (by change 0 < geo.b R; omega) c (critical_endpoint_color R (alpha R) rfl _ hc) hc
  have hEm : E.map (embedM R) = Z R c := map_comap_eq_self (endpoint_le_range geo hb hc)
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hrev.2
    rw [←hEm,Q_alpha R hp hQR]
    exact map_mono hh
  have hcomm : ⁅Q R (alpha R),Z R c⁆ ≤ criticalPlane R c b := by
    rw [hs.plane_eq c b hc hab hcb]
    exact le_inf (local_commutator_le_endpoint hab hcb) (local_commutator_le_Q geo hb hc)
  have hcomm0 : ⁅pCore 2 M,E⁆ ≤ A := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator,hEm,←Q_alpha R hp hQR]
    exact hcomm.trans (criticalPlane_le_orbit geo hb hc b)
  have hh := map_mono (f := embedM R) (core_le_of_commutator_le geo hs A E hE hcomm0)
  rwa [←core_alpha R hp hQR rfl] at hh

theorem orbit_component_commutator (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hs : LocalStructure geo) (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ = core R (alpha R) := by
  have hAQ : criticalOrbit R c b ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono (orbit_le_core geo hp hQR hs hb hlarge hc hab hcb)
  have hid : ⁅core R (alpha R),Ltilde R (alpha R)⁆ = core R (alpha R) := by
    rw [core_alpha R hp hQR rfl,Ltilde_alpha,←map_commutator]
    exact congrArg (Subgroup.map (embedM R))
      (commutator_isPPerfect_idempotent (pResidual 2 M) (pCore 2 M)
        (isPPerfect_pResidual 2) pCore_isPGroup le_normalizer_of_normal)
  exact le_antisymm (commutator_mono hAQ le_rfl)
    (hid.symm.le.trans (commutator_mono (core_le_orbit geo hp hQR hs hb hc hab hcb) le_rfl))
private theorem edge_core_coordinates (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) {c b : Vertex R}
    (hc : color R c = false) (hcb : Adjacent R c b) :
    ∃i : M →* FreeAmalgam R, Function.Injective i ∧
      R.map i = Q R b ∧ (pCore 2 M).map i = Q R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_⟩
    · have h := Q_act R g (beta R)
      rw [Q_beta] at h
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
    · have h := Q_act R g (alpha R)
      rw [Q_alpha R hp hQR] at h
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R hp hQR,map_map] using h.symm
  · rw [hg.1] at hc
    cases hc

theorem orbit_commutator_centralizes_residual
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) (hs : LocalStructure geo)
    (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hAQ : criticalOrbitNative R c b ≤ pCore 2 M) :
    ⁅⁅pCore 2 M,criticalOrbitNative R c b⁆,pResidual 2 M⁆ = ⊥ := by
  let A := criticalOrbitNative R c b
  let : A.Normal := normalClosure_normal
  let B := ⁅pCore 2 M,A⁆
  let E := (Z R c).comap (embedM R)
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := critical_reverse R geo hs.edge_centralizer
    (alpha R) rfl (by change 0 < geo.b R; omega) c hc0 hc
  have hZ : Z R c ≤ (embedM R).range := by
    rw [← show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_two R geo c hc0
    · rw [geo.distance_constant c hc0]
      change 0 < geo.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  have hEm : E.map (embedM R) = Z R c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hrev.2
    rw [←hEm,Q_alpha R hp hQR]
    exact map_mono hh
  have hBE : ⁅B,E⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (embedM_injective R)).mp
    rw [map_commutator,hEm]
    dsimp only [B]
    rw [map_commutator,←Q_alpha R hp hQR]
    have hA : criticalOrbit R c b ≤ Q R (alpha R) := by
      rw [Q_alpha R hp hQR]
      exact map_mono hAQ
    obtain ⟨i,hi,hiR,hiQ⟩ := edge_core_coordinates hp hQR hc0 hcb
    have hdd : ⁅Q R b,Q R b⁆ ≤ Q R c := by
      rw [←hiR,←hiQ,←map_commutator]
      exact map_mono hs.radical_derived
    have hQb := Q_le_adjacent_h R (edge_color hab) hab
    have hQc : ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Q R c :=
      (commutator_mono hQb (hA.trans hQb)).trans hdd
    apply le_bot_iff.mp
    exact (commutator_mono hQc le_rfl).trans_eq
      ((commutator_comm _ _).trans (Z_centralizes_Q R c hc0))
  have hEC : E ≤ centralizer (B : Set M) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBE)
  have hLC := hs.normal_generation (centralizer (B : Set M))
    (fun hh => hE (hEC.trans hh))
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hLC)

/-- The common edge kernel normalizes the source's maximal critical plane. -/
private theorem plane_normalized_edge (hb : geo.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t) :
    Q R t ≤ normalizer (criticalPlane R c t : Set (FreeAmalgam R)) := by
  have htGa : Q R t ≤ stabilizer R (alpha R) :=
    fun k hk => hk.2 (alpha R) (adjacent_symm R hat)
  have htGc : Q R t ≤ stabilizer R c :=
    fun k hk => hk.2 c (adjacent_symm R hct)
  apply le_normalizer_iff.mpr
  intro k hk y hy
  apply (mem_criticalPlane_iff geo hb hc hat hct _).mpr
  have hy' := (mem_criticalPlane_iff geo hb hc hat hct y).mp hy
  refine ⟨le_normalizer_iff.mp (Z_normalized R c) k (htGc hk) y hy'.1,?_⟩
  intro q hq
  have hq' : k⁻¹*q*k ∈ Q R (alpha R) := by
    simpa only [inv_inv] using
      le_normalizer_iff.mp (Q_normalized R (alpha R)) k⁻¹
        (htGa ((Q R t).inv_mem hk)) q hq
  have hm := hy'.2 (k⁻¹*q*k) hq'
  have hconj : (MulAut.conj k) ⁅k⁻¹*q*k,y⁆ ∈ Z R t :=
    le_normalizer_iff.mp (Z_normalized R t) k hk.1 _ hm
  rw [map_commutatorElement] at hconj
  have he : (MulAut.conj k) (k⁻¹*q*k) = q := by
    simp [MulAut.conj_apply,mul_assoc]
  rw [he] at hconj
  exact hconj

private theorem residual_sup_edge_eq_stabilizer
    (hgen : pResidual 2 M ⊔ R = ⊤) {b : Vertex R}
    (hab : Adjacent R (alpha R) b) :
    Ltilde R (alpha R) ⊔ Q R b = stabilizer R (alpha R) := by
  have hbase : Ltilde R (alpha R) ⊔ Q R (beta R) = stabilizer R (alpha R) := by
    rw [Ltilde_alpha,Q_beta,←Subgroup.map_sup,hgen,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base R).symm
  obtain ⟨g,hg,hgb⟩ := stabilizer_transitive_neighbors R (alpha R) (base_adjacent R) hab
  have he := congrArg (fun H : Subgroup (FreeAmalgam R) =>
    H.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  change act R g (alpha R) = alpha R at hg
  change act R g (beta R) = b at hgb
  rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act,hg,hgb] at he
  exact he


omit [Finite M] in
private theorem normalizes_commutator {G : Type*} [Group G]
    (P A B : Subgroup G) (hA : P ≤ normalizer A) (hB : P ≤ normalizer B) :
    P ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro p hp
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hA hp),
    mem_normalizer_iff_map_conj_eq.mp (hB hp)]

/-- Residual centralization makes the plane commutator normal, so its
normal orbit retains the sharper bound in the common edge layer. -/
theorem orbit_commutator_le_edge
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) (hgen : pResidual 2 M ⊔ R = ⊤)
    (hs : LocalStructure geo) (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hAQ : criticalOrbitNative R c b ≤ pCore 2 M) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Z R b := by
  let B := ⁅Q R (alpha R),criticalPlane R c b⁆
  have hBbig : B ≤ ⁅Q R (alpha R),criticalOrbit R c b⁆ :=
    commutator_mono le_rfl (criticalPlane_le_orbit geo hb hc b)
  have hcent : ⁅⁅Q R (alpha R),criticalOrbit R c b⁆,Ltilde R (alpha R)⁆ = ⊥ := by
    rw [Q_alpha R hp hQR,criticalOrbit,Ltilde_alpha,←map_commutator,←map_commutator,
      orbit_commutator_centralizes_residual geo hp hQR hs hb hc hab hcb hAQ,Subgroup.map_bot]
  have hBL : ⁅B,Ltilde R (alpha R)⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hBbig le_rfl).trans_eq hcent)
  have hbn : stabilizer R (alpha R) ≤ normalizer B := by
    rw [←residual_sup_edge_eq_stabilizer hgen hab]
    refine sup_le ?_ ?_
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hBL)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact normalizes_commutator _ _ _
        ((show Q R b ≤ stabilizer R (alpha R) from
          fun _ hx => hx.2 _ (adjacent_symm R hab)).trans (Q_normalized R (alpha R)))
        (plane_normalized_edge geo hb hc hab hcb)
  let B0 := B.comap (embedM R)
  let Y := (criticalPlane R c b).comap (embedM R)
  let : B0.Normal := by
    constructor
    intro x hx m
    change embedM R (m*x*m⁻¹) ∈ B
    rw [map_mul,map_mul,map_inv]
    apply le_normalizer_iff.mp hbn _ _ _ hx
    rw [show alpha R = mVertex R 1 from rfl,stabilizer_m_base]
    exact ⟨m,rfl⟩
  have hcomm : ⁅pCore 2 M,Y⁆ ≤ B0 := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,←Q_alpha R hp hQR]
    exact commutator_mono le_rfl (map_comap_le _ _)
  have hn := commutator_normalClosure_le_of_normal (pCore 2 M) Y B0 hcomm
  have hh := map_mono (f := embedM R) hn
  rw [map_commutator,←Q_alpha R hp hQR] at hh
  exact (hh.trans (map_comap_le _ _)).trans (criticalPlane_commutator_le geo hb hc hab hcb)

/-- Structural source facts discharge every local orbit-calculation field. -/
theorem localCalculations (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hgen : pResidual 2 M ⊔ R = ⊤) (hs : LocalStructure geo) (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    LocalCalculations R geo := {
  edge_centralizer := hs.edge_centralizer
  orbit_core := fun _ _ hc hab hcb => orbit_le_core geo hp hQR hs hb hlarge hc hab hcb
  commutator_edge := fun _ _ hc hab hcb => orbit_commutator_le_edge geo hp hQR hgen hs hb hc hab hcb
    (orbit_le_core geo hp hQR hs hb hlarge hc hab hcb)
  commutator_core := fun _ _ hc hab hcb => orbit_component_commutator geo hp hQR hs hb hlarge hc hab hcb
  commutator_central := fun _ _ hc hab hcb =>
    orbit_commutator_centralizes_residual geo hp hQR hs hb hc hab hcb
      (orbit_le_core geo hp hQR hs hb hlarge hc hab hcb)
  image_two := hs.image_two }

universe u
/-- The exact remaining structural source obligation for the original marked
replacement, retaining the whole moved layer as an explicit premise. -/
def LocalStructureInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalStructure (replacementGeometry h d)

/-- The actual replacement radical supplements its two-residual. -/
theorem replacement_residual_sup_radical {κ : GroupClass.{u}}
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (d : Replacement L R) :
    pResidual 2 d.overgroup ⊔ d.radical = ⊤ := by
  rw [replacement_residual h d]
  apply top_unique
  intro g _
  obtain ⟨k,hk,t,ht,rfl⟩ := replacement_product h d g
  exact mul_mem (mem_sup_left hk) (mem_sup_right ht)

/-- Consumer of the structural source facts on the literal replacement:
all local orbit/core identities required by favorable-pair selection follow. -/
theorem localCalculationInput_of_structure {κ : GroupClass.{u}}
    (hs : LocalStructureInput κ) : LocalCalculationInput κ := by
  intro G _ _ L R h e hz hn d hc hb hlarge
  exact localCalculations (replacementGeometry h d) (replacement_radical_isPGroup h d)
    (replacement_core_le_radical h d) (replacement_residual_sup_radical h d)
    (hs G L R h e hz hn d hc hb hlarge) hb hlarge

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
