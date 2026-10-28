module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Source reductions for nonabelianness of the fourth-case Frattini centralizer

The fourth C.1.34 alternative forces Z(Q) < Phi(Q), a nonabelian Q,
and a center of order greater than eight. These are the inputs needed to
construct the nonabelian MS93 setup and exclude its distance-four branch.
An actual isomorphism of cores transports their Frattini centralizers;
this construction does not identify the finite ambient group with the
infinite free amalgam.

At critical distance eight, a midpoint translation supplies a critical
pair whose two Z-layers lie in the radius-four subgroup. Their source
noncommutation proves that the full radius-four subgroup is nonabelian.
The remaining source comparison is made explicit in `RadiusFourFactors`:
the two endpoint layers factor through the moved radius-four subgroup and
the radius center, and the moved subgroup lies in the core's Frattini
centralizer. Removing these actual central factors preserves the needed
commutator. The whole-radius central-supplement hypothesis in
`RadiusFourFactors.of_generation` is only an optional sufficient condition;
this module does not assert it or the endpoint factorizations from MS93.

The exact requested nonabelianness theorem from a genuine MS-pair is still
unproved. Final assembly must construct the actual source setup, discharge
the distance-four exclusion and distance-eight theorem, and prove
`RadiusFourFactors`. The checked-map consumer also retains the independent
center-radical implication and large Frattini-commutator input. No completed
source theorem is claimed for these conditional applications.

There is also an input comparison to justify: C.1.31(MS1) explicitly
requires the set product G = LR. The fields of `LinearThreeMSPair` use
K join R and relative C-component membership, without an explicit product
or R-normalization field. Establishing the source product, or another valid
realization retaining the original hypotheses, remains with the source-setup
producer. None of the results below infers it from join generation alone.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, C.1.34(4),
printed pp.136--137, and 13.6.22, printed pp.932--933;
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(2.2)(ii) and (4.5), printed pp.856--857 and 895--900. The critical pair
(alpha-4,alpha+4) occurs in the path selected at the beginning of (4.5).
The printed (4.5)(iii) centralizes Ltilde_alpha, not Z_alpha, and (vi)
identifies the moved radius-four subgroup with C_core(Phi(core)). Neither
printed statement alone supplies the needed endpoint central factors.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian

variable {G H : Type*} [Group G] [Group H]

private theorem strict_section {K A B : Subgroup G} {J V F : Type*}
    [Group J] [AddCommGroup V] [Nontrivial V] [Field F] [Module F V]
    {actor : K →* J} {rho : Representation F J V}
    (h : HasSectionModel K A B actor rho) : B < A := by
  obtain ⟨hle, _, _, hn, f, _⟩ := h
  let := hn
  refine lt_of_le_not_ge hle ?_
  intro hab
  have hz (q : A ⧸ B.subgroupOf A) : q = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf A) q
    exact (QuotientGroup.eq_one_iff a).mpr (hab a.property)
  obtain ⟨v, hv⟩ := exists_ne (1 : Multiplicative V)
  obtain ⟨q, rfl⟩ := f.surjective v
  exact hv (by rw [hz q, map_one])

variable {K R S : Subgroup G}

/-- The nontrivial dual section makes the core center strictly smaller than its Frattini subgroup. -/
theorem caseFour_center_lt_frattini
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    sCenter (msQ K R) < frattiniIn (msQ K R) :=
  strict_section h.2.2.2.2.2.2.1

/-- Nonabelianness of Q itself, as required to enter the common MS93 reduction. -/
theorem caseFour_core_nonabelian
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    ¬ IsMulCommutative (msQ K R) := by
  intro hc
  let := hc
  have hz : sCenter (msQ K R) = msQ K R := by
    rw [CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn, center_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  apply (caseFour_center_lt_frattini e h).not_ge
  rw [hz]
  exact map_subtype_le _

/-- The doubled-dual quotient is nontrivial. This alone does not prove that its covering centralizer is nonabelian. -/
theorem caseFour_frattini_lt_centralizer
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    frattiniIn (msQ K R) <
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G) :=
  strict_section h.2.2.2.2.2.2.2.1

/-- Case four cannot have the order-eight center of the MS93 distance-four
branch. The proof uses the genuine natural subgroup and its disjoint fixed
four-group, rather than a family label. -/
theorem caseFour_center_card_gt_eight [Finite G]
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    8 < Nat.card (sCenter (msQ K R)) := by
  let Z := sCenter (msQ K R)
  let C := msQ K R ⊓ centralizer (K : Set G)
  let U := ⁅Z,K⁆
  have hZ : Z = C ⊔ U := h.2.2.2.1
  have hCU : C ⊓ U = ⊥ := h.2.2.2.2.1
  have hcard : Nat.card U = 8 := by
    obtain ⟨_,_,_,hn,f,_⟩ := h.2.2.2.2.2.1
    let := hn
    have heq : Nat.card (U ⧸ (⊥ : Subgroup G).subgroupOf U) = Nat.card U := by
      rw [bot_subgroupOf]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    rw [← heq, Nat.card_congr f.toEquiv]
    change Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8
    simp [Nat.card_eq_fintype_card]
  have hUZ : U < Z := by
    apply lt_of_le_not_ge
    · rw [hZ]
      exact le_sup_right
    · intro hle
      have hCZ : C ≤ Z := by rw [hZ]; exact le_sup_left
      have hC : C = ⊥ := le_bot_iff.mp (hCU ▸ le_inf le_rfl (hCZ.trans hle))
      have hc : Nat.card C = 4 := h.2.1
      rw [hC, card_bot] at hc
      omega
  rw [← hcard]
  change Nat.card U < Nat.card Z
  have hle := card_le_of_le hUZ.le
  have hne : Nat.card U ≠ Nat.card Z := by
    intro he
    exact hUZ.ne (eq_of_le_of_card_ge hUZ.le he.ge)
  omega

/-- The intrinsic centralizer maps onto the literal ambient Frattini centralizer. -/
theorem intrinsic_frattiniCentralizer_map (A : Subgroup G) :
    (centralizer (frattini A : Set A)).map A.subtype =
      A ⊓ centralizer (frattiniIn A : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (ha b hb)
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x,hx⟩, ?_, rfl⟩
    intro b hb
    exact Subtype.ext (hc b (mem_map_of_mem A.subtype hb))

/-- A group isomorphism preserves the centralizer of the actual Frattini subgroup. -/
theorem centralizer_frattini_map (e : G ≃* H) :
    (centralizer (frattini G : Set G)).map e.toMonoidHom =
      centralizer (frattini H : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ z hz
    rw [← frattini_map_equiv e] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (map_mul e w x).symm.trans ((congrArg e (hx w hw)).trans (map_mul e x w))
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro x hx
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      hy (e x) (frattini_map_equiv e ▸ mem_map_of_mem e.toMonoidHom hx)

/-- Canonical comparison of embedded Frattini centralizers through an isomorphism of their cores. -/
noncomputable def frattiniCentralizerEquiv {A : Subgroup G} {B : Subgroup H}
    (e : A ≃* B) :
    (A ⊓ centralizer (frattiniIn A : Set G) : Subgroup G) ≃*
      (B ⊓ centralizer (frattiniIn B : Set H) : Subgroup H) :=
  (MulEquiv.subgroupCongr (intrinsic_frattiniCentralizer_map A).symm).trans
    (((centralizer (frattini A : Set A)).equivMapOfInjective
      A.subtype A.subtype_injective).symm.trans
    (((centralizer (frattini A : Set A)).equivMapOfInjective
      e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (centralizer_frattini_map e)).trans
    (((centralizer (frattini B : Set B)).equivMapOfInjective
      B.subtype B.subtype_injective).trans
    (MulEquiv.subgroupCongr (intrinsic_frattiniCentralizer_map B))))))

/-- Noncommutation is invariant under the canonical Frattini-centralizer comparison. -/
theorem frattiniCentralizer_derived_ne_bot_iff {A : Subgroup G} {B : Subgroup H}
    (e : A ≃* B) :
    ⁅A ⊓ centralizer (frattiniIn A : Set G),
      A ⊓ centralizer (frattiniIn A : Set G)⁆ ≠ ⊥ ↔
    ⁅B ⊓ centralizer (frattiniIn B : Set H),
      B ⊓ centralizer (frattiniIn B : Set H)⁆ ≠ ⊥ := by
  simp only [ne_eq, commutator_self_eq_bot_iff]
  apply not_congr
  let f := frattiniCentralizerEquiv e
  constructor
  · intro hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply f.symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hc (f.symm x) (f.symm y)
  · intro hc
    apply isMulCommutative_iff.mpr
    intro x y
    apply f.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hc (f x) (f y)

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

variable {M : Type*} [Group M] {L T : Subgroup M}
  {source : LocalSource L T} {geometry : Geometry T}

/-- The fourth alternative excludes the distance-four source branch through
the actual core isomorphism. The sole extra premise is the order-eight center
conclusion of the independently owned MS93 (4.6) branch. -/
theorem caseFour_source_distance_gt_four [Finite G]
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (common : CommonFacts T source geometry)
    (f : core T (alpha T) ≃* msQ K R)
    (hfour : geometry.b T = 4 → Nat.card (sCenter (core T (alpha T))) = 8) :
    4 < geometry.b T := by
  have hcard : Nat.card (sCenter (core T (alpha T))) = Nat.card (sCenter (msQ K R)) := by
    calc
      _ = Nat.card (center (core T (alpha T))) :=
        (Nat.card_congr ((center (core T (alpha T))).equivMapOfInjective
          (core T (alpha T)).subtype (core T (alpha T)).subtype_injective).toEquiv).symm
      _ = Nat.card (center (msQ K R)) := Nat.card_congr (centerCongr f).toEquiv
      _ = _ := Nat.card_congr ((center (msQ K R)).equivMapOfInjective
        (msQ K R).subtype (msQ K R).subtype_injective).toEquiv
  have hlarge := common.large_distance
  have heven := geometry.even (alpha T) rfl
  change Even (geometry.b T) at heven
  obtain ⟨n,hn⟩ := heven
  by_contra hle
  have hb4 : geometry.b T = 4 := by omega
  have hsmall := hfour hb4
  rw [hcard] at hsmall
  have hbig := caseFour_center_card_gt_eight e h
  omega

private theorem move_to_alpha (a : Vertex T) (ha : color T a = false) :
    ∃ g : FreeAmalgam T, act T g a = alpha T := by
  cases a with
  | inl q =>
    induction q using Quotient.inductionOn with
    | h g =>
      exact ⟨g⁻¹, by change act T g⁻¹ (mVertex T g) = mVertex T 1; simp⟩
  | inr q => cases ha

/-- Translate the midpoint of a critical eight-path to the distinguished M-vertex. -/
theorem radiusFour_critical_pair (hb : geometry.b T = 8) :
    ∃ a c : Vertex T, ∃ ha : color T a = false,
      CriticalPair T a c (geometry.exists_critical a ha) ∧
      (cosetGraph T).dist a (alpha T) = 4 ∧
      (cosetGraph T).dist c (alpha T) = 4 := by
  obtain ⟨c, ⟨p⟩⟩ := CriticalPath.exists_from (R := T) (geometry := geometry)
    (a := alpha T) rfl
  have hlen : p.walk.length = 8 := p.length_eq_b.trans hb
  have hfour : 4 ≤ p.walk.length := by omega
  have hcol : color T (p.walk.getVert 4) = false :=
    (p.vertex_color hfour).mpr (by decide)
  obtain ⟨g, hg⟩ := move_to_alpha (p.walk.getVert 4) hcol
  let q := p.act g
  refine ⟨_, _, q.start_color, q.critical, ?_, ?_⟩
  · calc
      _ = (cosetGraph T).dist (act T g (alpha T)) (act T g (p.walk.getVert 4)) :=
        congrArg ((cosetGraph T).dist (act T g (alpha T))) hg.symm
      _ = (cosetGraph T).dist (alpha T) (p.walk.getVert 4) := dist_act T g _ _
      _ = 4 := p.dist_start hfour
  · rw [← hg, dist_act, SimpleGraph.dist_comm, p.dist_end, hlen]

/-- The two critical endpoint layers inside the radius-four subgroup do not commute. -/
theorem radiusFour_derived_ne_bot (common : CommonFacts T source geometry)
    (hb : geometry.b T = 8) :
    ⁅VBall T (alpha T) 4, VBall T (alpha T) 4⁆ ≠ ⊥ := by
  obtain ⟨a, c, ha, hac, ha4, hc4⟩ := radiusFour_critical_pair hb
  have hA : Z T a ≤ VBall T (alpha T) 4 :=
    le_iSup_of_le a (le_iSup_of_le ha4.le le_rfl)
  have hC : Z T c ≤ VBall T (alpha T) 4 :=
    le_iSup_of_le c (le_iSup_of_le hc4.le le_rfl)
  intro hzero
  exact common.critical_noncommutation a ha c hac
    (le_bot_iff.mp ((commutator_mono hA hC).trans hzero.le))

/-- The base Z-layer is central in the radius-four subgroup when b > 4. -/
theorem radiusFour_centralizes_base_Z (hb : 4 < geometry.b T) :
    VBall T (alpha T) 4 ≤ centralizer (Z T (alpha T) : Set (FreeAmalgam T)) := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  have hZQ : Z T (alpha T) ≤ Q T a := by
    apply Z_le_Q_of_dist_lt T (alpha T) (geometry.exists_critical _ rfl)
    change (cosetGraph T).dist (alpha T) a < geometry.b T
    rw [SimpleGraph.dist_comm]
    omega
  have hc : Z T a ≤ centralizer (Q T a : Set (FreeAmalgam T)) := by
    by_cases hcol : color T a = false
    · exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a hcol)
    · rw [Z, if_neg hcol]
      intro z hz x hx
      exact (mem_omegaCenter_iff.mp hz).2.2 x hx
  exact hc.trans (centralizer_le hZQ)

private theorem radiusFour_moved_le :
    ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ≤ VBall T (alpha T) 4 := by
  apply le_normalizer_iff_commutator_le_left.mp
  apply (map_subtype_le _).trans
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (VBall T (alpha T) 4).map (MulAut.conj g).toMonoidHom = _
  have he := VBall_act T g⁻¹ (alpha T) 4
  have hg' : act T g⁻¹ (alpha T) = alpha T := (stabilizer T (alpha T)).inv_mem hg
  simpa only [hg', inv_inv] using he.symm

private theorem derived_sup_center (A V : Subgroup G) (hA : A ≤ V) :
    ⁅A ⊔ sCenter V, A ⊔ sCenter V⁆ = ⁅A,A⁆ := by
  let B := A ⊔ sCenter V
  have hB : B ≤ V := sup_le hA (map_subtype_le _)
  have hc : sCenter V ≤ centralizer (B : Set G) :=
    ((centerIn_eq V).le.trans inf_le_right).trans (centralizer_le hB)
  have hgen : sCenter V ⊔ A = B := sup_comm _ _
  have h₁ := commutator_eq_of_centralizing_sup hgen
    (hc.trans (centralizer_le (show A ≤ B from le_sup_left))) A.le_normalizer
  have h₂ := commutator_eq_of_centralizing_sup hgen hc
    ((show A ≤ B from le_sup_left).trans B.le_normalizer)
  exact h₂.symm.trans ((commutator_comm B A).trans h₁.symm)

/-- The remaining source-layer comparison. Both endpoint layers are factored
through the literal moved radius-four subgroup and the actual radius center.
The last field is the containment supplied by source (4.5)(vi). This record
has no constructor from the MS hypotheses in this module. -/
structure RadiusFourFactors (T : Subgroup M) (geometry : Geometry T) where
  left : Vertex T
  right : Vertex T
  left_color : color T left = false
  critical : CriticalPair T left right (geometry.exists_critical left left_color)
  left_distance : (cosetGraph T).dist left (alpha T) ≤ 4
  right_distance : (cosetGraph T).dist right (alpha T) ≤ 4
  left_factor : Z T left ≤ ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ⊔
    sCenter (VBall T (alpha T) 4)
  right_factor : Z T right ≤ ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ⊔
    sCenter (VBall T (alpha T) 4)
  moved_le : ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ≤
    core T (alpha T) ⊓ centralizer (frattiniIn (core T (alpha T)) : Set (FreeAmalgam T))

/-- A proved whole-radius factorization would suffice, but it is not assumed
to follow merely from the definition of the moved subgroup. The source
producer may instead construct the two weaker endpoint factorizations. -/
theorem RadiusFourFactors.of_generation (hb : geometry.b T = 8)
    (hgen : VBall T (alpha T) 4 ≤ ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ⊔
      sCenter (VBall T (alpha T) 4))
    (hm : ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆ ≤
      core T (alpha T) ⊓ centralizer (frattiniIn (core T (alpha T)) : Set (FreeAmalgam T))) :
    Nonempty (RadiusFourFactors T geometry) := by
  obtain ⟨a,c,ha,hac,ha4,hc4⟩ := radiusFour_critical_pair hb
  have hA : Z T a ≤ VBall T (alpha T) 4 :=
    le_iSup_of_le a (le_iSup_of_le ha4.le le_rfl)
  have hC : Z T c ≤ VBall T (alpha T) 4 :=
    le_iSup_of_le c (le_iSup_of_le hc4.le le_rfl)
  exact ⟨{
    left := a, right := c, left_color := ha, critical := hac
    left_distance := ha4.le, right_distance := hc4.le
    left_factor := hA.trans hgen
    right_factor := hC.trans hgen
    moved_le := hm }⟩

/-- Critical noncommutation survives removal of the specified central factors.
In particular neither endpoint's membership in the moved subgroup is assumed. -/
theorem radiusFour_moved_derived_ne_bot (common : CommonFacts T source geometry)
    (d : RadiusFourFactors T geometry) :
    ⁅⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆,
      ⁅VBall T (alpha T) 4, Ltilde T (alpha T)⁆⁆ ≠ ⊥ := by
  intro hzero
  apply common.critical_noncommutation d.left d.left_color d.right d.critical
  apply le_bot_iff.mp
  apply (commutator_mono d.left_factor d.right_factor).trans
  rw [derived_sup_center _ _ radiusFour_moved_le, hzero]

/-- The literal amalgam-core centralizer is nonabelian once the source-layer
factorizations and the (4.5)(vi) containment have actually been proved. -/
theorem source_frattiniCentralizer_derived_ne_bot
    (common : CommonFacts T source geometry) (d : RadiusFourFactors T geometry) :
    let D := core T (alpha T) ⊓
      centralizer (frattiniIn (core T (alpha T)) : Set (FreeAmalgam T))
    ⁅D,D⁆ ≠ ⊥ := by
  dsimp only
  intro hzero
  exact radiusFour_moved_derived_ne_bot common d
    (le_bot_iff.mp ((commutator_mono d.moved_le d.moved_le).trans hzero.le))

/-- Transport through an actual isomorphism of commutator cores. The source
setup constructs this map through embedM and the replacement inclusion. -/
theorem frattiniCentralizer_derived_ne_bot_of_radiusFactors
    (common : CommonFacts T source geometry) (d : RadiusFourFactors T geometry)
    (f : core T (alpha T) ≃* msQ K R) :
    let D := msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)
    ⁅D,D⁆ ≠ ⊥ :=
  (frattiniCentralizer_derived_ne_bot_iff f).mp
    (source_frattiniCentralizer_derived_ne_bot common d)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

/-- Actual checked-quotient consumer. The source layer producer, core
comparison, independent center-radical implication and large Frattini
commutator input all remain explicit; this is not the final source theorem. -/
theorem caseFour_checked_commutator_of_radiusFactors [Finite G]
    {κ : CFSG.Quasithin.GroupClass} (T₀ : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T₀ v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T₀ v) S e)
    (common : CommonFacts T source geometry) (d : RadiusFourFactors T geometry)
    (f : core T (alpha T) ≃* msQ K (Tv T₀ v))
    (hradical : let Q := msQ K (Tv T₀ v)
      let D := Q ⊓ centralizer (frattiniIn Q : Set G)
      ⁅D,D⁆ ≠ ⊥ → sCenter D ≤ frattiniIn Q)
    (hPhi : FrattiniCommutatorLarge (msQ K (Tv T₀ v))) :
    ⁅sourceZ0 K v hK,K⁆ = sourceU K :=
  caseFour_checked_commutator_of_center T₀ v hK hv hMS e h
    (hradical (frattiniCentralizer_derived_ne_bot_of_radiusFactors common d f)) hPhi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian

