module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentSelection
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Chosen

/-!
# The literal reduced moved module of the escaping component

For the selected component K, characteristic two makes the orbit of the
original omega-center reduced in KT. Its moved subgroup has the same
centralizer, so its literal centralizer quotient also has trivial two-core.
The proved orbit splitting and commutativity give full K-movement. Escape
from the fixed-line normalizer forces this moved subgroup to be nonzero.

These facts construct the original ChosenModule once minimality modulo
K-fixed subgroups is proved. The final existential application applies the
new conclusions to the same K selected from the nonsolvable C_G(z), retaining
relative normality, the fixed line, splitting and exact action kernel.

Minimality, the module markings, the A5/covered-A6/doubled-natural exclusions,
and the comparison and graph arguments remain with qt-d-1341-nonsolvable-source.
The earlier structural and 13.3 inputs retain final discharge with
qt-d-1341-fixed-core-source. No whole-module classification is asserted here.
Nonsolvability must still be supplied separately at both escaping weights.

Source: Aschbacher–Smith B.2.14, 13.4.10(4), and 13.4.13(2),
printed pp.78,907–909,911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G}

theorem component_orbit_reduced
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K).subgroupOf
      (K ⊔ (T : Subgroup G))) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hZT : Z ≤ centralizer (T : Set G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have he := conjugateSpanBy_sup_of_normalizes_seed Z K (T : Subgroup G)
    ((le_centralizer_iff.mp hZT).trans (Subgroup.centralizer_le_normalizer _)) hTK
  rw [←he]
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  exact reduced_conjugateSpan_of_sylow_central T (K ⊔ (T : Subgroup G)) Z le_sup_right
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) hZT
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h₀.qtke.evenCharacteristic T) (component_sylow_mem_HOver hzT hz1 hKz)))

theorem component_moved_reduced
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    IsPReduced 2 ((⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G).subgroupOf (K ⊔ (T : Subgroup G))) := by
  let H := K ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K
  let U := ⁅W,K⁆
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  have hWH : W ≤ H := conjugateSpanBy_le
    ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
      fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans H.le_normalizer)
  have hUW : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)
  have hHW : H ≤ normalizer (W : Set G) :=
    le_normalizer_of_normal_subgroupOf hWH (hK := hred.normal)
  have hHK : H ≤ normalizer (K : Set G) := sup_le K.le_normalizer hTK
  have hHU : H ≤ normalizer (U : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [U]
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHW hg),
      mem_normalizer_iff_map_conj_eq.mp (hHK hg)]
  let : (U.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHU
  let : (W.subgroupOf H).Normal := hred.normal
  let : IsElementaryAbelian 2 (W.subgroupOf H) := hred.elementary
  have he : centralizer (U.subgroupOf H : Set H) =
      centralizer (W.subgroupOf H : Set H) := by
    have hk := component_seed_action_kernel h₀ hzT hz1 hKz hTK
    ext a
    constructor
    · intro ha w hw
      have hau : a.val ∈ centralizer (U : Set G) := by
        intro v hv
        exact congrArg Subtype.val (ha ⟨v,(hUW.trans hWH) hv⟩ hv)
      have haw : a.val ∈ H ⊓ centralizer (W : Set G) := hk.symm ▸ ⟨a.property,hau⟩
      exact Subtype.ext (haw.2 w.val hw)
    · intro ha v hv
      exact ha v (hUW hv)
  refine ⟨inferInstance, IsElementaryAbelian.of_le
    (show U.subgroupOf H ≤ W.subgroupOf H from comap_mono hUW), ?_⟩
  let e := QuotientGroup.quotientMulEquivOfEq he
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e]
  exact hred.quotient_pCore_eq_bot

theorem component_moved_eq_commutator
    (h₀ : Hypothesis1331 T L) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ⁅⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆,K⁆ =
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z K
  let U := ⁅W,K⁆
  let C := Z ⊓ centralizer (K : Set G)
  have hs : W = U ⊔ C := component_seed_split h₀ hzT hz1 hKz hTK
  have hU : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy Z K)
  have hC : C ≤ W := inf_le_left.trans (le_conjugateSpanBy Z K)
  have hCW : ⁅C,K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hred := component_orbit_reduced h₀ hzT hz1 hKz hTK
  have hWH : W ≤ K ⊔ (T : Subgroup G) := conjugateSpanBy_le
    ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
      fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans (K ⊔ (T : Subgroup G)).le_normalizer)
  let := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  have hcomm : ⁅U,K⁆ ≤ W :=
    (commutator_mono hU le_rfl).trans hU
  have hn : W ≤ normalizer ((⁅U,K⁆ : Subgroup G) : Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hcomm)).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp
    (normalizer_commutator_ge_right W K))
  change ⁅W,K⁆ ≤ ⁅U,K⁆
  conv_lhs => rw [hs]
  exact commutator_sup_le_of_relative_normal W U C K ⁅U,K⁆ hn hU hC le_rfl
    (hCW.le.trans bot_le)

/-- Escape from the original fixed-line normalizer forces nonzero movement. -/
theorem component_moved_ne_bot
    {V : Subgroup G} {D : ChosenModule T L V}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ≠ ⊥ := by
  intro he
  have hKC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  apply hKM
  apply le_trans ?_ (fixed_generator_centralizer h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))).le
  exact hKC.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2)))

/-- On the literal moved orbit, the only remaining Irr-plus requirement is
minimality modulo fixed subgroups. All reducedness, invariance, generation,
and nontriviality premises are supplied by the original component geometry. -/
theorem component_chosen_of_minimal
    {V : Subgroup G} {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hmin : ∀ A : Subgroup G,
      A ≤ ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ →
      K ≤ normalizer (A : Set G) →
      A = ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ∨
        A ≤ centralizer (K : Set G)) :
    Nonempty (ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K
  have hWH : W ≤ K ⊔ (T : Subgroup G) := conjugateSpanBy_le
    ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
      fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans le_sup_right)
    (le_sup_left.trans (K ⊔ (T : Subgroup G)).le_normalizer)
  have hUH : ⁅W,K⁆ ≤ K ⊔ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans hWH
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  exact Section03.PlaneNoncentralitySource.exists_chosenModuleOfMinimal hred hUH hTK
    (le_normalizer_of_normal_subgroupOf hUH (hK := hred.normal))
    (component_moved_eq_commutator h₀ hzT hz1 hKz hTK)
    (component_moved_ne_bot h structural m hKM) hmin

/-- The selected source component has an actual nonzero reduced moved module,
with the same fixed line, orbit splitting and action kernel as its full orbit. -/
theorem exists_escaping_component_moved_seed
    {V : Subgroup G} {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let W := conjugateSpanBy Z K
      let U := ⁅W,K⁆
      IsPReduced 2 (U.subgroupOf (K ⊔ (T : Subgroup G))) ∧
      U ≠ ⊥ ∧ ⁅U,K⁆ = U ∧
      Z ⊓ centralizer (K : Set G) = zpowers z ∧
      W = U ⊔ zpowers z ∧
      (K ⊔ (T : Subgroup G)) ⊓ centralizer (W : Set G) =
        (K ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) := by
  obtain ⟨K,hK,hf,hstar,hn,hTK,hKM,hLN,hfix,hsplit,hkernel⟩ :=
    exists_escaping_component_seed h₀ h structural m h1332 h1338 hindex hzT hz1 hout hnonsolv
  exact ⟨K,hK,hf,hstar,hn,hTK,hKM,hLN,
    component_moved_reduced h₀ hzT hz1 hK.1 hTK,
    component_moved_ne_bot h structural m hKM,
    component_moved_eq_commutator h₀ hzT hz1 hK.1 hTK,hfix,hsplit,hkernel⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
