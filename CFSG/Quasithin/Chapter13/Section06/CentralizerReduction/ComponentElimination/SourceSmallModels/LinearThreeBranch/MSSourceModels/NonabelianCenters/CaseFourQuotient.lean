module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
public import Theory.Frattini.BinarySquares
/-!
# Reduction of the fourth MS alternative through a central involution

For a central kernel of order at most two, the preimage X of the quotient
core center centralizes the Frattini subgroup of Q: the commutator maps
Q → ker are homomorphisms and kill every square. Hence Q ∩ X lies in
D = C_Q(Φ(Q)). Two further structural statements suffice to put Q ∩ X
inside Z(Q): Z(D) ≤ Φ(Q), with [D,D] disjoint from C_Q(K), and every
noncentral element of Φ(Q) having a commutator subgroup with Q of order
larger than two. Commutator idempotence then gives the desired identity.

The two structural statements are explicit, independent proof obligations
below. This module does not assert that C.1.34(4) proves them. The source
assembly remains incomplete until they are established from the genuine
MS-pair and its section models. In particular the conditional checked-map
application is not a proof of the whole fourth alternative of 13.6.22.

The proved steps retain the literal source Q, U, core and quotient maps.
No centrality of the whole core commutator or disjointness of Q from the
quotient kernel is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34(4),
printed pp.136–137, and the last paragraph of 13.6.22 on printed p.932.
The finer source for the remaining structural investigation is
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
Lemma 4.5, printed pp.895–900.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient
variable {G : Type*} [Group G] [Finite G]
/-- Central commutators of exponent two vanish on the Frattini subgroup
of a finite two-group. -/
theorem centralizes_frattini_of_small_commutator (Q X N : Subgroup G)
    (hQ : IsPGroup 2 Q) (hN : N ≤ centralizer (Q : Set G))
    (hcard : Nat.card N ∣ 2) (hc : ⁅X,Q⁆ ≤ N) :
    X ≤ centralizer (frattiniIn Q : Set G) := by
  intro x hx q hq
  let d : Q →* N := {
    toFun y := ⟨⁅x,(y : G)⁆, hc (commutator_mem_commutator hx y.property)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅x,(a : G) * b⁆ = ⁅x,(a : G)⁆ * ⁅x,(b : G)⁆
      have hb := hc (commutator_mem_commutator hx b.property)
      rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (a : G),
        hN hb a a.property, ← mul_assoc, mul_inv_cancel_right] }
  have hPhi : frattini Q ≤ d.ker := by
    rw [hQ.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    change d (a ^ 2) = 1
    rw [map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (d a)).trans hcard)
  obtain ⟨a,ha,rfl⟩ := hq
  have he := congrArg Subtype.val (hPhi ha : d a = 1)
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- The required internal control of D = C_Q(Φ(Q)). This is an explicit
structural hypothesis, not a consequence of the source alternative proved here. -/
def FrattiniCentralizerControl (Q C : Subgroup G) : Prop :=
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  sCenter D ≤ Phi ∧ ⁅D,D⁆ ⊓ C = ⊥

/-- A noncentral Frattini element cannot have all its commutators in a
subgroup of order at most two. Its proof from the MS sections remains separate. -/
def FrattiniCommutatorLarge (Q : Subgroup G) : Prop :=
  ∀ x ∈ frattiniIn Q, x ∉ sCenter Q → 2 < Nat.card (⁅zpowers x,Q⁆ : Subgroup G)

/-- The two structural facts control the center of a central quotient,
without assuming a bound on the resulting moved subgroup. -/
theorem small_central_quotient_control (Q X N C : Subgroup G)
    (hQ : IsPGroup 2 Q) (hN : N ≤ centralizer (Q : Set G))
    (hcard : Nat.card N ∣ 2) (hc : ⁅X,Q⁆ ≤ N) (hNC : Q ⊓ N ≤ C)
    (hD : FrattiniCentralizerControl Q C) (hPhi : FrattiniCommutatorLarge Q) :
    Q ⊓ X ≤ sCenter Q := by
  let Y := Q ⊓ X
  let D := Q ⊓ centralizer (frattiniIn Q : Set G)
  have hYD : Y ≤ D := le_inf inf_le_left
    (inf_le_right.trans (centralizes_frattini_of_small_commutator Q X N hQ hN hcard hc))
  have hDDQ : ⁅D,D⁆ ≤ Q :=
    (Subgroup.commutator_le_sup D D).trans (sup_le inf_le_left inf_le_left)
  have hYDc : ⁅Y,D⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hD.2]
    have hdd : ⁅Y,D⁆ ≤ ⁅D,D⁆ := commutator_mono hYD le_rfl
    exact le_inf hdd ((le_inf (hdd.trans hDDQ)
      ((commutator_mono inf_le_right inf_le_left).trans hc)).trans hNC)
  have hYPhi : Y ≤ frattiniIn Q := by
    apply le_trans _ hD.1
    rw [centerIn_eq]
    exact le_inf hYD (commutator_eq_bot_iff_le_centralizer.mp hYDc)
  intro x hx
  by_contra hz
  have hlo := hPhi x (hYPhi hx) hz
  have hle : ⁅zpowers x,Q⁆ ≤ N :=
    (commutator_mono (zpowers_le.mpr hx.2) le_rfl).trans hc
  exact (not_lt_of_ge ((card_le_of_le hle).trans (Nat.le_of_dvd (by decide) hcard))) hlo

open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
variable {K R S : Subgroup G}

/-- The central four and natural moved section both centralize the core. -/
theorem caseFour_center_le_core_center
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    sCenter (msQ K R) ≤ sCenter (K.pCoreIn 2) := by
  rw [centerIn_eq (K.pCoreIn 2)]
  refine le_inf ?_ ?_
  · apply le_trans (map_subtype_le _)
    rw [msQ_eq_ambient_blockU K R hs hp]
    exact map_mono blockU_le_core
  · rw [h.2.2.2.1]
    apply sup_le
    · exact (h.2.2.1.trans ((centerIn_eq _).le.trans inf_le_right)).trans
        (centralizer_le ((pCoreIn_le 2 K).trans le_sup_left))
    · have hc := core_centralizes_trivial_section e BinaryLinearThree.W h.2.2.2.2.2.1
      exact fun z hz p hp => (hc hp z hz).symm

variable {H : Type*} [Group H]

/-- Intrinsic quotient control from the two independent structural inputs.
The first conclusion is proved before commutator idempotence yields equality. -/
theorem caseFour_quotient_control_of_structure
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ∣ 2)
    (hN : f.ker.map K.subtype ≤ sCenter (K ⊔ R))
    (hD : FrattiniCentralizerControl (msQ K R) (msQ K R ⊓ centralizer (K : Set G)))
    (hPhi : FrattiniCommutatorLarge (msQ K R)) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ ≤ sCenter (pCore 2 K) ∧
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ =
      ⁅sCenter (pCore 2 K), (⊤ : Subgroup K)⁆ := by
  let : Finite H := Finite.of_surjective f hf
  let X := (sCenter (pCore 2 H)).comap f
  let M := ⁅X, (⊤ : Subgroup K)⁆
  let A := X.map K.subtype
  let N := f.ker.map K.subtype
  let Q := msQ K R
  have hcore : (pCore 2 H).comap f = pCore 2 K :=
    f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore 2 K).map f = pCore 2 H := by
    rw [← hcore, map_comap_eq_self_of_surjective hf]
  have hXP : X ≤ pCore 2 K := by
    rw [← hcore]
    exact comap_mono (map_subtype_le _)
  have hnX : X.Normal := inferInstanceAs
    (((center (pCore 2 H)).map (pCore 2 H).subtype).comap f).Normal
  have hMX : M ≤ X := commutator_le_left _ _
  have hMQ : M ≤ blockU K := commutator_mono hXP le_rfl
  have hXPker : ⁅X, pCore 2 K⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator, hmap]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (map_comap_le _ _).trans ((centerIn_eq _).le.trans inf_le_right)
  have hQeq : Q = (blockU K).map K.subtype := msQ_eq_ambient_blockU K R hs hp
  have hQP : Q ≤ K.pCoreIn 2 := by
    rw [hQeq]
    exact map_mono blockU_le_core
  have hQK : Q ≤ K := hQP.trans (pCoreIn_le 2 K)
  have hNJ : N ≤ centralizer ((K ⊔ R : Subgroup G) : Set G) :=
    hN.trans ((centerIn_eq _).le.trans inf_le_right)
  have hNQ := hNJ.trans (centralizer_le (hQK.trans le_sup_left))
  have hNcard : Nat.card N ∣ 2 := by
    rw [← Nat.card_congr (f.ker.equivMapOfInjective K.subtype K.subtype_injective).toEquiv]
    exact hcard
  have hAQ : ⁅A,Q⁆ ≤ N := by
    apply le_trans (commutator_mono le_rfl hQP)
    change ⁅X.map K.subtype,(pCore 2 K).map K.subtype⁆ ≤ f.ker.map K.subtype
    rw [← map_commutator]
    exact map_mono hXPker
  have hNC : Q ⊓ N ≤ Q ⊓ centralizer (K : Set G) :=
    inf_le_inf_left Q (hNJ.trans (centralizer_le (show K ≤ K ⊔ R from le_sup_left)))
  have hQXZ := small_central_quotient_control Q A N _
    ((isPGroup_pCoreIn 2 K).to_le hQP) hNQ hNcard hAQ hNC hD hPhi
  have hMambient : M.map K.subtype ≤ sCenter (K.pCoreIn 2) := by
    apply le_trans _ (caseFour_center_le_core_center hs hp e h)
    apply le_trans _ hQXZ
    refine le_inf ?_ (map_mono hMX)
    rw [hQeq]
    exact map_mono hMQ
  have hMZ : M ≤ sCenter (pCore 2 K) := by
    have he : (sCenter (pCore 2 K)).map K.subtype = sCenter (K.pCoreIn 2) :=
      map_embeddedCenter _ _ K.subtype_injective
    intro m hm
    have hmm : (m : G) ∈ (sCenter (pCore 2 K)).map K.subtype :=
      he.symm ▸ hMambient (mem_map_of_mem K.subtype hm)
    obtain ⟨z,hz,hze⟩ := hmm
    have hez : z = m := Subtype.ext hze
    rwa [hez] at hz
  refine ⟨hMZ, ?_⟩
  have hid : ⁅M, (⊤ : Subgroup K)⁆ = M :=
    commutator_isPPerfect_idempotent ⊤ X
      (hp.of_surjective (topEquiv (G := K)).symm.toMonoidHom
        (topEquiv (G := K)).symm.surjective)
      (pCore_isPGroup.to_le hXP) (by rw [normalizer_eq_top])
  apply le_antisymm (hid.symm.le.trans (commutator_mono hMZ le_rfl))
  apply commutator_mono _ le_rfl
  intro z hz
  change f z ∈ sCenter (pCore 2 H)
  rw [centerIn_eq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact mem_map_of_mem f hz.1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmap.symm ▸ hx : x ∈ (pCore 2 K).map f)
    exact (map_mul f y z).symm.trans ((congrArg f (hz.2 y hy)).trans (map_mul f z y))

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels

/-- Application to the literal checked quotient in 13.6.22. The genuine
MS-pair discharges subnormality and two-perfection; the checked map discharges
all kernel hypotheses. Only the two structural facts remain explicit. -/
theorem caseFour_checked_commutator_of_structure {κ : CFSG.Quasithin.GroupClass}
    (T : Subgroup G) (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T v) S e)
    (hD : FrattiniCentralizerControl (msQ K (Tv T v))
      (msQ K (Tv T v) ⊓ centralizer (K : Set G)))
    (hPhi : FrattiniCommutatorLarge (msQ K (Tv T v))) :
    ⁅sourceZ0 K v hK,K⁆ = sourceU K := by
  have hh := (caseFour_quotient_control_of_structure
    (msPair_core_hypotheses hMS).1 (msPair_core_hypotheses hMS).2 e h
    (BinaryRankTwo.CenterPreimage.checkedKMap K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_surjective K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_pKernel K v hK hv)
    (checkedKMap_kernel_card K v hK hv)
    (checkedKMap_kernel_central_join K T v hK) hD hPhi).2
  have hm := congrArg (map K.subtype) hh
  rw [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient
