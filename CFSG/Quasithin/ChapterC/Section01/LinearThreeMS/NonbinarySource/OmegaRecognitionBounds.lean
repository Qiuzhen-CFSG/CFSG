module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentSections
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.Representation.BinaryOffender.IrreducibleSubspaceExistence
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.FixedSpaceCodimension

/-!
# The displacement gap and the small central-omega branch

Put E = Ω₁(Z(Q)) for the original Q = [O₂(KR),K], and assume C_Q(K)=1.
The faithful E-action has a normal perfect central cover B of full SL₃(F).
An elementary subgroup disjoint from C(B) embeds by conjugation into
Aut(PSL₃(F)), so its order is at most 2^(2n). This bounds every moving
quadratic offender without assuming that it lies in B.

Conversely, a nonidentity operator centralizing B has a nonzero invariant
displacement space. The constituent recognition theorem supplies a natural
subspace of dimension 3n inside it. Thus every offender of rank less than
3n avoids C(B) and injects into the literal initial action. A nontrivial
kernel of that projection has an involution, forcing dim(E) ≥ 6n by
rank-nullity. All covering kernels, including those at field four, remain
present in this argument.

Below dimension 6n the entire projection kernel vanishes. Hence O₂(KR)
centralizes E, placing E in the initial central omega. The fixed-free
hypothesis and its proved splitting give E = initialMoved. The doubled
initial branch has dimension 6n and is excluded, leaving a literal natural
HasSectionModel on all of E. The final dichotomy retains the larger branch;
it does not identify E with the whole center, place offenders in B, or
supply the common marking of the upper sections required by C.1.34.

NonblockOmegaRecognitionBounds applies these results to the original
4.3.8--10 configuration and its actual Sylow intersection.
Source: Aschbacher--Smith B.1.5, K.3.2 and C.1.34, printed
pp.69--70,454--456,136--137; the full automorphism two-rank calculation
uses GLS3, Theorem 2.5.12(a), as recorded in PSL3Even.AutomorphismTwoRank.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.MovingBounds
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem conjugation_injective {X : Type*} [Group X]
    (B A : Subgroup X) (hn : A ≤ normalizer (B : Set X))
    (hd : A ⊓ centralizer (B : Set X) = ⊥) :
    Function.Injective (B.normalizerMonoidHom.comp (inclusion hn)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  apply Subtype.ext
  apply hd.le
  refine ⟨a.property,?_⟩
  have hk : inclusion hn a ∈ B.normalizerMonoidHom.ker := ha
  rw [normalizerMonoidHom_ker] at hk
  exact hk

variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)

include h hn

/-- Conjugation in the full projective automorphism group bounds an elementary
subgroup without requiring component containment. -/
theorem elementary_card_le_of_disjoint (A : Subgroup H)
    (hA : IsElementaryTwo A) (hd : A ⊓ centralizer (B : Set H) = ⊥) :
    Nat.card A ≤ 2^(2*n) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let c := KernelOffenders.omegaCover h hn (Classical.choice h.model)
  let := c.isQuasisimple
  have hAN : A ≤ normalizer (B : Set H) := by rw [normalizer_eq_top]; exact le_top
  let a := (B).normalizerMonoidHom.comp (inclusion hAN)
  let g := (MulAut.centralQuotientAction c.quotientCenterEquiv).comp a
  have hg : Function.Injective g :=
    (MulAut.centralQuotientAction_injective c.quotientCenterEquiv).comp
      (conjugation_injective B A hAN hd)
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hb := (primeRank_le_iff_elementary_card_le (MulAut PSL(3,F))).mp
    (Matrix.PSL3Even.automorphism_two_rank_eq F (by omega) h.field_card).le
    g.range inferInstance
  rwa [←Nat.card_congr (MonoidHom.ofInjective hg).toEquiv] at hb

/-- Every moving quadratic offender has order at most q² and binary rank
and whole-space fixed codimension at most 2n. -/
theorem moving_offender_bounds
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (A : Subgroup H) (hA : IsOffender rho A) (hqA : IsQuadratic rho A)
    (hm : ¬ A ≤ centralizer (B : Set H)) :
    Nat.card A ≤ 2^(2*n) ∧ rank A ≤ 2*n ∧ fixedCodim rho A ≤ 2*n := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  have hd := quadratic_inf_centralizer_eq_bot_of_component rho B A
    (CentralSections.coreOmegaRepresentation_injective h hn)
    (KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed) hm hqA
  have hc := elementary_card_le_of_disjoint h hn A hA.1 hd
  have hr : rank A ≤ 2*n := by
    rw [hA.1.card_eq_two_pow_rank] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc
  exact ⟨hc,hr,hA.2.trans hr⟩

/-- Every nonidentity operator commuting with the component moves at least
one full natural constituent, of binary dimension 3n. -/
theorem centralizing_displacement_lower_bound
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (a : H) (ha : a ∈ centralizer (B : Set H)) (hne : a ≠ 1) :
    3*n ≤ fixedCodim rho (zpowers a) := by
  let := (KernelOffenders.omegaCover h hn e).isQuasisimple
  let W := LinearMap.range (rho a - 1)
  have hW : B ≤ subspaceStabilizer rho W := by
    apply le_subspaceStabilizer
    rintro b hb v ⟨w,rfl⟩
    refine ⟨rho b w,?_⟩
    change rho a (rho b w) - rho b w = rho b (rho a w - w)
    rw [map_sub,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul,
      mem_centralizer_iff.mp ha b hb]
  have hWne : W ≠ ⊥ := by
    intro hz
    apply hne
    apply CentralSections.coreOmegaRepresentation_injective h hn
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hv : rho a v - v ∈ W := ⟨v,rfl⟩
    rw [hz,Submodule.mem_bot] at hv
    exact sub_eq_zero.mp hv
  have hnot : ¬ W ≤ fixedSpace rho B := by
    rw [KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed]
    exact fun hw => hWne (bot_unique hw)
  obtain ⟨I,hIW,hI⟩ := exists_isIrrPlus_le_of_not_fixed rho B W hW hnot
  have hi := (ConstituentRecognition.irrPlus_card_finrank h hn hfixed e I hI).2
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hi ▸ Submodule.finrank_mono hIW

/-- An offender of rank below 3n avoids the entire component centralizer;
quadraticity and component containment are unnecessary. -/
theorem small_offender_disjoint
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (A : Subgroup H) (hA : IsOffender rho A) (hr : rank A < 3*n) :
    A ⊓ centralizer (B : Set H) = ⊥ := by
  apply bot_unique
  rintro a ⟨ha,hac⟩
  by_contra hne
  have hl := centralizing_displacement_lower_bound h hn hfixed
    (Classical.choice h.model) a hac hne
  have hs : fixedSpace rho A ≤ fixedSpace rho (zpowers a) :=
    (rho).invariants_comp_subtype_antitone (zpowers_le.mpr ha)
  have hd := Submodule.finrank_mono hs
  have h1 := fixedCodim_add_finrank rho A
  have h2 := fixedCodim_add_finrank rho (zpowers a)
  have hb := hA.2
  omega

/-- The kernel of the literal projection to the initial action centralizes
the full covering component. -/
theorem initial_kernel_le_centralizer :
    (f).ker ≤ centralizer (B : Set H) := by
  let := component_normal h hn
  let : (B).Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := (KernelOffenders.omegaCover h hn (Classical.choice h.model)).isQuasisimple
  have hc : IsComponent H B := ⟨(inferInstance : (B).Normal).isSubnormal,inferInstance⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hcent : pCore 2 H ≤ centralizer (B : Set H) :=
    le_centralizer_iff.mp (hc.le_centralizer_of_solvable_normal (pCore 2 H))
  rw [NoncoreOffenders.toInitial_kernel]
  exact hcent

/-- Every offender below rank 3n injects into the actual initial action,
including nonquadratic offenders at field four. -/
theorem small_offender_initial_injective
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (A : Subgroup H) (hA : IsOffender rho A) (hr : rank A < 3*n) :
    Function.Injective ((f).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  apply Subtype.ext
  apply (small_offender_disjoint h hn hfixed A hA hr).le
  exact ⟨a.property,initial_kernel_le_centralizer h hn ha⟩

/-- A nontrivial whole-action kernel forces at least twice the natural
degree on the entire central omega. -/
theorem kernel_nontrivial_degree_lower_bound
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (hk : (f).ker ≠ ⊥) : 6*n ≤ Module.finrank (ZMod 2) (Additive E) := by
  have hp : IsPGroup 2 (f).ker := by
    rw [NoncoreOffenders.toInitial_kernel]
    exact pCore_isPGroup
  have hd : 2 ∣ Nat.card (f).ker := hp.card_eq_or_dvd.resolve_left
    (fun hc => hk (card_eq_one.mp hc))
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := (f).ker) 2 hd
  have haorder : orderOf (a : H) = 2 := (orderOf_coe a).trans ha
  have hne : (a : H) ≠ 1 := by intro he; simp [he] at haorder
  have hlo := centralizing_displacement_lower_bound h hn hfixed
    (Classical.choice h.model) a (initial_kernel_le_centralizer h hn a.property) hne
  have hhi := (involution_actor_rank_and_fixedCodim rho (a : H) haorder).2.2.2
  omega

/-- Below degree 6n the whole-action kernel vanishes, including its
exceptional field-four part. -/
theorem initial_kernel_eq_bot_of_degree_lt
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (hsmall : Module.finrank (ZMod 2) (Additive E) < 6*n) : (f).ker = ⊥ := by
  by_contra hk
  exact (not_le_of_gt hsmall) (kernel_nontrivial_degree_lower_bound h hn hfixed hk)

/-- The original radical overgroup supplies one bounded minimal offender
preserving all constituents, with its weight and literal initial projection. -/
theorem exists_bounded_minimal_offender
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (S : Subgroup J) (hRS : R.subgroupOf J ≤ S) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ D ≤ A.map q,
      IsMinimalBestOffender rho D ∧ IsQuadratic rho D ∧
      weight rho D = weight rho (A.map q) ∧ ⁅B,D⁆ = B ∧
      D ⊓ centralizer (B : Set H) = ⊥ ∧
      Function.Injective ((f).comp D.subtype) ∧
      Nat.card D ≤ 2^(2*n) ∧ rank D ≤ 2*n ∧ fixedCodim rho D ≤ 2*n ∧
      ∀ I, IsIrrPlus rho B I → D ≤ subspaceStabilizer rho I := by
  obtain ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,hI⟩ :=
    ConstituentOffenders.exists_minimal_section_offender h hn hfixed S hRS
  have hc := elementary_card_le_of_disjoint h hn D hD.1.1 hd
  have hr : rank D ≤ 2*n := by
    rw [hD.1.1.card_eq_two_pow_rank] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc
  exact ⟨A,hA,D,hDA,hD,hqD,hw,hm,hd,hfD,hc,hr,(hD.1.isOffender rho).2.trans hr,hI⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.MovingBounds

open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SmallOmega
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "f" => NoncoreOffenders.toInitial h hn E
  (CentralSections.coreOmegaLayer_centralizer_le h hn)
local notation "Z" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R)
include h hn

private theorem core_le_centralizer_of_kernel_bot (hk : (f).ker = ⊥) :
    pCore 2 J ≤ centralizer (E : Set J) := by
  intro x hx
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change (f) (q x) = (f) 1
  rw [map_one,NoncoreOffenders.toInitial_apply]
  exact (QuotientGroup.eq_one_iff x).mpr ((centralOmega_kernel_eq_core h hn).symm ▸ hx)

/-- Eliminating the entire projection kernel identifies the actual central
omega subgroup with the initial moved group. -/
theorem omega_eq_initial_of_kernel_bot
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (hk : (f).ker = ⊥) : Z = initialMoved K R := by
  have hZQ : Z ≤ msQ K R := map_subtype_le _
  have hZN : Z ≤ (K ⊔ R).pCoreIn 2 := hZQ.trans msQ_le_joinCore
  have hZJ : Z ≤ J := hZN.trans (pCoreIn_le 2 _)
  have hZI : Z ≤ initialOmega K R := by
    rw [initialOmega_eq]
    intro z hz
    have hzE : (⟨z,hZJ hz⟩ : J) ∈ E := by
      rw [CentralSections.coreOmegaLayer_eq]
      exact hz
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨hZN hz,?_,?_⟩
    · rintro x ⟨x,hx,rfl⟩
      exact (congrArg (J).subtype
        (core_le_centralizer_of_kernel_bot h hn hk hx ⟨z,hZJ hz⟩ hzE)).symm
    · exact ((mem_omegaCenterIn_iff (msQ K R) z).mp hz).2.2
  have hIN : initialOmega K R ≤ (K ⊔ R).pCoreIn 2 := by
    rw [initialOmega_eq]
    exact fun z hz => ((mem_omegaCenterIn_iff _ _).mp hz).1
  let C := initialOmega K R ⊓ centralizer (K : Set G)
  have hCM : C ≤ normalizer (initialMoved K R : Set G) :=
    (le_centralizer_iff.mp (initialMoved_centralizes_joinCore.trans
      (centralizer_le (inf_le_left.trans hIN)))).trans (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm _ CentralSections.initialMoved_le_omegaCenter
  intro z hz
  have hzsup : z ∈ initialMoved K R ⊔ C := (initialMoved_split h hn).1.symm ▸ hZI hz
  have hzprod : z ∈ (initialMoved K R : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hCM]
    exact hzsup
  obtain ⟨u,hu,c,hc,he⟩ := hzprod
  change u*c = z at he
  have hcQ : c ∈ msQ K R := by
    have hmul : u*c ∈ msQ K R := he.symm ▸ hZQ hz
    exact (msQ K R).mul_mem_cancel_left (initialMoved_le_msQ hu) |>.mp hmul
  have hc1 : c = 1 := hfixed.le ⟨hcQ,hc.2⟩
  rw [hc1,mul_one] at he
  exact he ▸ hu

/-- The entire central omega is natural below degree 6n, with bottom
denominator and an actual full quotient marking. -/
theorem omega_natural_of_degree_lt
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (hsmall : Module.finrank (ZMod 2) (Additive E) < 6*n) :
    ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3) := by
  have heq := omega_eq_initial_of_kernel_bot h hn hfixed
    (MovingBounds.initial_kernel_eq_bot_of_degree_lt h hn hfixed hsmall)
  obtain ⟨e,hm | hm⟩ := initialMoved_section_models h hn
  · exact ⟨e,heq.symm ▸ hm⟩
  · exfalso
    rw [HasSectionModel,bot_subgroupOf] at hm
    obtain ⟨_,_,_,_,b,_⟩ := hm
    have hcard : Nat.card (initialMoved K R) = 2^(6*n) := by
      rw [Nat.card_congr (QuotientGroup.quotientBot.symm.trans b).toEquiv]
      change Nat.card ((Fin 3 → F) × (Fin 3 → F)) = _
      rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,h.field_card,←pow_mul,←pow_add]
      congr 1
      omega
    have hzJ : Z ≤ J := (map_subtype_le _).trans
      (msQ_le_joinCore.trans (pCoreIn_le 2 _))
    have hEcard : Nat.card E = Nat.card Z := by
      rw [CentralSections.coreOmegaLayer_eq]
      exact Nat.card_congr (subgroupOfEquivOfLe hzJ).toEquiv
    have hp : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2^(6*n) := by
      have hdcard : Nat.card (Additive E) =
          2 ^ Module.finrank (ZMod 2) (Additive E) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact hdcard.symm.trans (hEcard.trans (by rw [heq]; exact hcard))
    have hd := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hp
    omega

/-- A source-valid central-omega dichotomy: a literal natural section or
binary degree at least 6n. The larger branch remains explicit. -/
theorem omega_natural_or_large
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) :
    (∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3)) ∨
      6*n ≤ Module.finrank (ZMod 2) (Additive E) := by
  by_cases hs : Module.finrank (ZMod 2) (Additive E) < 6*n
  · exact Or.inl (omega_natural_of_degree_lt h hn hfixed hs)
  · exact Or.inr (Nat.le_of_not_gt hs)

omit hEN in
/-- The same dichotomy on the literal ambient subgroup, stated by its order
rather than by a chosen additive carrier. -/
theorem omega_natural_or_card_large
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥) :
    (∃ e : (K ⧸ pCore 2 K) ≃* SL(3,F),
      HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural 3)) ∨
      2^(6*n) ≤ Nat.card Z := by
  let := CentralSections.coreOmegaLayer_normal h hn
  rcases omega_natural_or_large h hn hfixed with hm | hd
  · exact Or.inl hm
  right
  have hzJ : Z ≤ J := (map_subtype_le _).trans
    (msQ_le_joinCore.trans (pCoreIn_le 2 _))
  have hEcard : Nat.card E = Nat.card Z := by
    rw [CentralSections.coreOmegaLayer_eq]
    exact Nat.card_congr (subgroupOfEquivOfLe hzJ).toEquiv
  have hdcard : Nat.card (Additive E) =
      2 ^ Module.finrank (ZMod 2) (Additive E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  calc
    2^(6*n) ≤ 2 ^ Module.finrank (ZMod 2) (Additive E) :=
      Nat.pow_le_pow_right (by decide) hd
    _ = Nat.card E := hdcard.symm
    _ = Nat.card Z := hEcard

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SmallOmega
