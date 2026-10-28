module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import Theory.GroupTheory.OddElementLift
public import Theory.GroupTheory.PrimeOrderLift
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Detection of whole-center fixed points from the initial moved layer

A nontrivial subgroup X of Q normalized by K and O₂(KR) meets the central
omega of O₂(KR). If C_Q(K)=1, its commutator with K is nontrivial, so X
meets the actual initial moved subgroup. Apply this to fixed points in Z(Q).
The perfect central cover shows that every quotient scalar acts centrally
on the whole center, including at field four; no even kernel is discarded.
The initial natural/doubled alternatives then make every nonidentity scalar
fixed-free on the whole center. Odd-order lifting through the original
two-core quotient supplies a genuine order-three scalar lift. Its bijective
commutator map proves [Z(Q),K]=Z(Q).

The fixed-factor hypothesis is discharged on the original nonblock groups
in NonblockCenterScalars, giving whole-center movement at field four before
any whole-section recognition. These results do not classify those sections
or eliminate the remaining even central-cover kernels.
Source: Aschbacher--Smith C.1.34, pp.136--137, and original 4.3.8--10,
pp.616--617; the finite p-group central-omega intersection and the elementary
perfect-central-cover and coprime lifting arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.InitialDetection
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}

/-- Every nonzero subgroup of the MS core normalized by the component and
join two-core meets the initial moved subgroup, when the core has no fixed factor. -/
theorem inf_initialMoved_ne_bot (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (X : Subgroup G) (hXQ : X ≤ msQ K R)
    (hNX : (K ⊔ R).pCoreIn 2 ≤ normalizer (X : Set G))
    (hKX : K ≤ normalizer (X : Set G)) (hne : X ≠ ⊥) :
    X ⊓ initialMoved K R ≠ ⊥ := by
  intro hz
  have hY : X ⊓ initialOmega K R ≠ ⊥ := by
    rw [initialOmega_eq]
    exact inf_omegaCenterIn_ne_bot_of_normalized_twoGroup X _
      (hXQ.trans msQ_le_joinCore) (isPGroup_pCoreIn 2 _) hNX hne
  have hc : ⁅X ⊓ initialOmega K R,K⁆ = ⊥ := by
    apply bot_unique
    apply le_trans _ hz.le
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hKX))
      (commutator_mono inf_le_right le_rfl)
  apply hY
  exact bot_unique ((le_inf (inf_le_left.trans hXQ)
    (commutator_eq_bot_iff_le_centralizer.mp hc)).trans_eq hfixed)

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "Q" => msQ K R
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q

omit [Finite G] in
private theorem center_centralizes : Z ≤ centralizer (Q : Set G) := by
  rintro z ⟨z,hz,rfl⟩ q hq
  exact congrArg (Q).subtype (mem_center_iff.mp hz ⟨q,hq⟩)

/-- A central scalar in the supplied full quotient acts centrally on the
entire center, even when the covering kernel has not yet been eliminated. -/
theorem scalar_centerAction_commutes
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : K)
    (hk : linearThreeActor e k ∈ center SL(3,F)) :
    let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
    ∀ l : K, Commute (a ⟨k,mem_sup_left k.property⟩) (a ⟨l,mem_sup_left l.property⟩) := by
  let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
  let := h.component.2.perfect
  let c := CentralSections.sectionCover h hn Z
    (CentralSections.join_normalizes_center h hn) initialMoved_le_core_center
    center_centralizes e
  let kk : L := ⟨⟨k,mem_sup_left k.property⟩,k.property⟩
  have hp : c.toMonoidHom ((a.comp (L).subtype).rangeRestrict kk) = linearThreeActor e k := by
    exact CentralSections.sectionCover_apply h hn Z
      (CentralSections.join_normalizes_center h hn) initialMoved_le_core_center center_centralizes e kk
  have hz : (a.comp (L).subtype).rangeRestrict kk ∈ center (a.comp (L).subtype).range := by
    rw [←c.comap_center]
    change c.toMonoidHom _ ∈ center SL(3,F)
    rwa [hp]
  change ∀ l : K, Commute (a ⟨k,mem_sup_left k.property⟩) (a ⟨l,mem_sup_left l.property⟩)
  intro l
  let ll : L := ⟨⟨l,mem_sup_left l.property⟩,l.property⟩
  exact (congrArg Subtype.val (mem_center_iff.mp hz
    ((a.comp (L).subtype).rangeRestrict ll))).symm

omit [CharP F 2] in
private theorem core_centerAction_commutes (k : K) (x : J) (hx : x ∈ pCore 2 J) :
    let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
    Commute (a ⟨k,mem_sup_left k.property⟩) (a x) := by
  let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
  have hh : ⁅(x : G),(k : G)⁆ ∈ Q :=
    commutator_mem_commutator (mem_map_of_mem (J).subtype hx) k.property
  have he : a ⁅x,(⟨k,mem_sup_left k.property⟩ : J)⁆ = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (a ⁅x,(⟨k,mem_sup_left k.property⟩ : J)⁆ z : G) = (z : G)
    simp only [a,CentralSections.sectionAction_apply]
    rw [show (((⁅x,(⟨k,mem_sup_left k.property⟩ : J)⁆ : J)) : G) =
      ⁅(x : G),(k : G)⁆ from map_commutatorElement (J).subtype x _]
    rw [center_centralizes z.property _ hh,mul_inv_cancel_right]
  rw [map_commutatorElement] at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

omit [CharP F 2] in
private theorem normalizes_center_fixed (k : K) (H : Subgroup G) (hHJ : H ≤ J)
    (hc : ∀ g : H,
      let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
      Commute (a ⟨k,mem_sup_left k.property⟩) (a ⟨g,hHJ g.property⟩)) :
    H ≤ normalizer ((Z ⊓ centralizer ({(k : G)} : Set G) : Subgroup G) : Set G) := by
  let a := CentralSections.sectionAction Z (CentralSections.join_normalizes_center h hn)
  apply le_normalizer_iff.mpr
  rintro g hg z ⟨hz,hzk⟩
  let zz : Z := ⟨z,hz⟩
  let gg : J := ⟨g,hHJ hg⟩
  let kk : J := ⟨k,mem_sup_left k.property⟩
  have hzfix : a kk zz = zz := by
    apply Subtype.ext
    rw [show (a kk zz : G) = (k : G)*z*(k : G)⁻¹ from
      CentralSections.sectionAction_apply _ _ _ _]
    rw [mem_centralizer_iff.mp hzk k (Set.mem_singleton _),mul_inv_cancel_right]
  have hfix : a kk (a gg zz) = a gg zz := by
    calc
      _ = a gg (a kk zz) := congrArg (fun b : MulAut Z => b zz) (hc ⟨g,hg⟩).eq
      _ = _ := by rw [hzfix]
  have hgco : (a gg zz : G) = g*z*g⁻¹ := CentralSections.sectionAction_apply _ _ _ _
  refine ⟨hgco ▸ (a gg zz).property,mem_centralizer_iff.mpr ?_⟩
  rintro y (rfl : y = (k : G))
  have he := congrArg Subtype.val hfix
  simp only [a,CentralSections.sectionAction_apply] at he
  exact mul_inv_eq_iff_eq_mul.mp he

include h hn in
/-- A scalar with no fixed points on the initial moved layer has no fixed
points on the whole center. No whole-center model or trivial covering kernel
is assumed. -/
theorem center_fixed_eq_bot_of_initial
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : K)
    (hk : linearThreeActor e k ∈ center SL(3,F))
    (hki : initialMoved K R ⊓ centralizer ({(k : G)} : Set G) = ⊥) :
    Z ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  let X := Z ⊓ centralizer ({(k : G)} : Set G)
  by_contra hne
  apply inf_initialMoved_ne_bot hfixed X (inf_le_left.trans (map_subtype_le _))
    (normalizes_center_fixed h hn k _ (pCoreIn_le 2 _) ?_)
    (normalizes_center_fixed h hn k K le_sup_left ?_) hne
  · exact bot_unique ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans_eq hki)
  · intro g
    obtain ⟨x,hx,hxg⟩ := g.property
    have he : x = (⟨g,(pCoreIn_le 2 J) g.property⟩ : J) := Subtype.ext hxg
    exact he ▸ core_centerAction_commutes h hn k x hx
  · exact scalar_centerAction_commutes h hn e k hk

omit [Finite G] [Finite F] [CharP F 2] in
private theorem natural_scalar_fixed_zero (g : SL(3,F))
    (hg : g ∈ center SL(3,F)) (hne : g ≠ 1) (v : Fin 3 → F)
    (hv : specialLinearNatural 3 g v = v) : v = 0 := by
  obtain ⟨r,_,hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr1 : r ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    rw [←hr,he]
    simp
  change g.val.mulVec v = v at hv
  rw [←hr] at hv
  change (Matrix.diagonal (fun _ : Fin 3 => r)).mulVec v = v at hv
  rw [Matrix.diagonal_const_mulVec] at hv
  have hh : (r-1) • v = 0 := by rw [sub_smul,one_smul,hv,sub_self]
  exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hr1)

omit [Finite G] [Finite F] [CharP F 2] in
private theorem section_fixed_zero {W : Type*} [AddCommGroup W] [Module F W]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (rho : Representation F SL(3,F) W)
    (hm : HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e) rho)
    (k : K) (hfix : ∀ w, rho (linearThreeActor e k) w = w → w = 0) :
    initialMoved K R ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hn,a,ha⟩ := hm
  let := hn
  apply bot_unique
  rintro x ⟨hx,hxk⟩
  let xx : initialMoved K R := ⟨x,hx⟩
  have hconj : (xx : G) = k * (xx : G) * (k : G)⁻¹ := by
    rw [mem_centralizer_iff.mp hxk k (Set.mem_singleton _),mul_inv_cancel_right]
  have hz := hfix _ (ha k xx xx hconj).symm
  have he : QuotientGroup.mk' (⊥ : Subgroup (initialMoved K R)) xx = 1 :=
    a.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)
  exact congrArg Subtype.val (mem_bot.mp ((QuotientGroup.eq_one_iff xx).mp he))

include h hn in
/-- The initial natural/doubled alternatives already make every nonidentity
scalar fixed-free on the whole center, provided the actual core fixed factor
is trivial. This includes the full SL₃(4) marking. -/
theorem center_scalar_fixed_eq_bot
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e)
        (specialLinearNatural (k := F) 3) ∨
      HasSectionModel K (initialMoved K R) ⊥ (linearThreeActor e)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    (k : K) (hk : linearThreeActor e k ∈ center SL(3,F))
    (hne : linearThreeActor e k ≠ 1) :
    Z ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  apply center_fixed_eq_bot_of_initial h hn hfixed e k hk
  rcases hm with hm | hm
  · exact section_fixed_zero e _ hm k (natural_scalar_fixed_zero _ hk hne)
  · apply section_fixed_zero e _ hm k
    intro w hw
    exact Prod.ext (natural_scalar_fixed_zero _ hk hne w.1 (congrArg Prod.fst hw))
      (natural_scalar_fixed_zero _ hk hne w.2 (congrArg Prod.snd hw))

include h hn in
/-- The actual initial classification discharges the section premise in the
whole-center fixed-point theorem, for every original full quotient marking. -/
theorem center_scalar_fixed_eq_bot_of_no_fixed_factor
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : K)
    (hk : linearThreeActor e k ∈ center SL(3,F))
    (hne : linearThreeActor e k ≠ 1) :
    Z ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  obtain ⟨mark,hm⟩ := initialMoved_section_models h hn
  let b : SL(3,F) ≃* SL(3,F) := e.symm.trans mark
  have hb : b (linearThreeActor e k) = linearThreeActor mark k := by
    change mark (e.symm (e (QuotientGroup.mk' (pCore 2 K) k))) = _
    rw [e.symm_apply_apply]
    rfl
  have hmark : linearThreeActor mark k ∈ center SL(3,F) := by
    rw [←hb]
    exact (centerCongr b ⟨_,hk⟩).property
  have hmarkne : linearThreeActor mark k ≠ 1 := by
    rw [←hb]
    exact fun he => hne (b.map_eq_one_iff.mp he)
  exact center_scalar_fixed_eq_bot h hn hfixed mark hm k hmark hmarkne

include h hn in
/-- A nonidentity scalar has an actual order-three lift acting fixed-freely
on the whole center. The original two-core quotient and its marking are kept. -/
theorem exists_cubic_scalar_lift
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hne : s ≠ 1) :
    ∃ k : K, linearThreeActor e k = s ∧ orderOf k = 3 ∧
      Z ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  have hs3 : s^3 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (((center SL(3,F)).orderOf_dvd_natCard hs).trans (Matrix.SL3.card_center_dvd_three F))
  have hsorder : orderOf s = 3 := orderOf_eq_prime hs3 hne
  let f := linearThreeActor e
  obtain ⟨x,hx⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)) s
  have hx' : f x = s := hx
  obtain ⟨k,_,hkodd,hk⟩ := f.exists_odd_power_with_image x (by rw [hx',hsorder]; decide)
  have he : f k = s := hk.trans hx'
  have hker : f.ker = pCore 2 K := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have ho : orderOf k = 3 := by
    rw [←f.orderOf_map_eq_of_coprime_of_isPGroup_ker (hker.symm ▸ pCore_isPGroup)
      k hkodd.coprime_two_left,he,hsorder]
  exact ⟨k,he,ho,center_scalar_fixed_eq_bot_of_no_fixed_factor h hn hfixed e k
    (he.symm ▸ hs) (fun hz => hne (he.symm.trans hz))⟩

include h hn in
/-- A nontrivial scalar makes the entire center component-generated, before
any whole-section recognition. -/
theorem center_moved_eq_self_of_scalar
    (hfixed : Q ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hne : s ≠ 1) : ⁅Z,K⁆ = Z := by
  obtain ⟨k,_,_,hkfree⟩ := exists_cubic_scalar_lift h hn hfixed e s hs hne
  have hKZ : K ≤ normalizer (Z : Set G) :=
    (le_sup_left : K ≤ J).trans (CentralSections.join_normalizes_center h hn)
  let a : MulAut Z := (Z).normalizerMonoidHom ⟨k,hKZ k.property⟩
  have hfree : MonoidHom.FixedPointFree a := by
    intro z hz
    apply Subtype.ext
    apply hkfree.le
    refine ⟨z.property,mem_centralizer_iff.mpr ?_⟩
    rintro y (rfl : y = (k : G))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hz)
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hKZ)
  intro z hz
  obtain ⟨x,hx⟩ := hfree.commutatorMap_surjective (⟨z,hz⟩ : Z)
  have heq : (x : G) / ((k : G)*(x : G)*(k : G)⁻¹) = z := congrArg Subtype.val hx
  rw [←heq]
  simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using
    commutator_mem_commutator x.property k.property

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.InitialDetection
