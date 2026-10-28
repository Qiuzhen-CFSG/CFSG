module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerCore
public import Theory.GroupAction.IrreducibleCyclicPrimeCore
public import Theory.GroupTheory.PResidual.NormalityLift
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.Fitting.TwoCorePreimage

/-!
# Fitting control for an irreducible odd radical

Pass a Sylow odd complement through the literal ambient two-core quotient.
Frattini factorization transfers the full normalizer action, including when
its Sylow two-subgroup acts reducibly. The supercritical argument either
makes the complement image normal or centralizes the quotient Fitting
subgroup and detects an ordinary component. Two-perfectness lifts the
normalizer control and component detection to the original subgroups.

This is the Fitting-preimage and component-existence step of original
13.1.12, printed pp.873--874. The source consumer is SourceCentralizerComponents.
The later component-model sieve and centralizer containment are separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- A complement image controls the actual Fitting subgroup or is normal. -/
theorem normal_or_fitting {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (P : Subgroup G) (hP : XiOddQuotient p P)
    (hirr : IsNormalizerFrattiniIrreducible P) (hcore : pCore 2 G = ⊥) :
    P.Normal ∨ (P ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ K : Subgroup G, IsComponent G K ∧ ⁅K,P⁆ ≠ ⊥) := by
  rcases SourceCentralizerCore.normal_or_core_control ho hG P hP hirr with hn | ⟨hc,hother⟩
  · exact Or.inl hn
  let := hc
  have hPC := IsNormalizerFrattiniIrreducible.le_centralizer_of_cyclic_odd_pGroup
    ho P (pCore p G) pCore_isPGroup hirr hP.not_isCyclic
  have hF : P ≤ centralizer (fittingSubgroup G : Set G) := by
    apply le_centralizer_iff.mpr
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun r => ?_
    have hr := Nat.prime_of_mem_primeFactors r.val.property
    by_cases htwo : r.val.val = 2
    · rw [htwo,hcore]
      exact bot_le
    apply le_centralizer_iff.mp
    by_cases he : r.val.val = p
    · simpa only [he] using hPC
    · exact hother r.val.val hr (hr.odd_of_ne_two htwo) he
  exact Or.inr ⟨hF,exists_component_not_centralized P hF (by
    intro hle
    exact hP.not_isCyclic (isCyclic_of_injective
      (inclusion (pSubgroup_le_pCore_of_le_fitting hP.isPGroup hle))
      (inclusion_injective _)))⟩

private theorem image_le_of_normal_complement {p : ℕ} [Fact p.Prime]
    (X : Subgroup G) (hX : IsPPerfect 2 X)
    (hq : XiOddQuotient p (XiQuotient X)) (P : Sylow p X)
    (R : Subgroup (G ⧸ pCore 2 G)) [R.Normal]
    (hPR : (((P : Subgroup X).map X.subtype).map
      (QuotientGroup.mk' (pCore 2 G))) ≤ R) :
    X.map (QuotientGroup.mk' (pCore 2 G)) ≤ R := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := R.comap (q.comp X.subtype)
  have hPD : (P : Subgroup X) ≤ D := by
    intro x hx
    exact hPR (mem_map_of_mem q (mem_map_of_mem X.subtype hx))
  have hgen : D ⊔ pCore 2 X = ⊤ := by
    have hs : pCore 2 X ⊔ (P : Subgroup X) = ⊤ := by
      apply map_injective X.subtype_injective
      simpa only [Subgroup.map_sup,pCoreIn,← MonoidHom.range_eq_map,range_subtype] using
        RadicalActions.sylow_sup hq.isPGroup P
    exact top_unique (hs ▸ sup_le le_sup_right (hPD.trans le_sup_left))
  have hD : D = ⊤ := hX D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 X) pCore_isPGroup hgen)
  rintro x ⟨y,hy,rfl⟩
  exact (show (⟨y,hy⟩ : X) ∈ D from hD ▸ mem_top _)

/-- The complement is embedded in the actual quotient by the ambient two-core. -/
theorem quotient_complement_irreducible {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (X M : Subgroup G) (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hq : XiOddQuotient p (XiQuotient X))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A=⊥ ∨ A=⊤)
    (P : Sylow p X) :
    let Pbar := ((P : Subgroup X).map X.subtype).map (QuotientGroup.mk' (pCore 2 G))
    XiOddQuotient p Pbar ∧ IsNormalizerFrattiniIrreducible Pbar := by
  let P₀ := (P : Subgroup X).map X.subtype
  let q := QuotientGroup.mk' (pCore 2 G)
  have hP₀ : XiOddQuotient p P₀ :=
    hq.of_mulEquiv (RadicalActions.ambientSylowQuotientEquiv ho hq.isPGroup P).symm
  have hi : Function.Injective (q.subgroupMap P₀) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk']
    apply bot_unique
    intro a ha
    exact Subtype.ext ((pCore_isPGroup.disjoint_of_coprime hP₀.isPGroup
      (Nat.coprime_two_left.mpr ho)).le_bot ⟨ha,a.property⟩)
  refine ⟨hP₀.of_mulEquiv (MulEquiv.ofBijective (q.subgroupMap P₀)
    ⟨hi,q.subgroupMap_surjective P₀⟩),?_⟩
  exact normalizerFrattiniIrreducible_map q P₀ (M ⊓ normalizer (P₀:Set G))
    inf_le_right hi (RadicalActions.normalizer_irreducible hn
      ((pCoreIn_le 2 X).trans hXM) hirr ho hq.isPGroup P)

/-- Original 13.1.12's component-detection step with the full actor M.
It allows a reducible Sylow actor, as required in the source S₅ case. -/
theorem fitting_and_component {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hG : IsStronglyQuasithin G) (X M : Subgroup G)
    (hXM : X ≤ M) (hn : M ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X) (hq : XiOddQuotient p (XiQuotient X))
    (hcore : pCore 2 G ≤ normalizer (X : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A=⊥ ∨ A=⊤)
    (P : Sylow p X) :
    twoFittingCore G ≤ normalizer (X : Set G) ∧
      (X.Normal ∨ ∃ K : Subgroup G, K.IsCComponent ∧ IsQuasisimple (XiQuotient K) ∧
        ¬ ⁅K,(P : Subgroup X).map X.subtype⁆ ≤ pCore 2 G) := by
  let P₀ := (P : Subgroup X).map X.subtype
  let q := QuotientGroup.mk' (pCore 2 G)
  obtain ⟨hP,hi⟩ := quotient_complement_irreducible ho X M hXM hn hq hirr P
  have hqG : IsStronglyQuasithin (G ⧸ pCore 2 G) := by
    intro r hr hor
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r hor _ pCore_isPGroup).trans (hG r hr hor)
  have hker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkerN : q.ker ≤ normalizer (X : Set G) := by rwa [QuotientGroup.ker_mk']
  rcases normal_or_fitting ho hqG (P₀.map q) hP hi (pCore_quotient_pCore_eq_bot 2) with hnorm | ⟨hF,K,hK,hKP⟩
  · let := hnorm
    have he : X.map q = P₀.map q := le_antisymm
      (image_le_of_normal_complement X hX hq P (P₀.map q) le_rfl)
      (map_mono (map_subtype_le _))
    let hnX : (X.map q).Normal := he.symm ▸ hnorm
    let hnormX := normal_of_map_normal_of_pPerfect q X hX hker hkerN
    exact ⟨le_normalizer_of_normal,Or.inl hnormX⟩
  · have hXF : X.map q ≤ centralizer (fittingSubgroup (G ⧸ pCore 2 G) : Set _) :=
      image_le_of_normal_complement X hX hq P _ hF
    have hfit : twoFittingCore G ≤ normalizer (X : Set G) := by
      rw [← comap_normalizer_map_of_pPerfect q X hX hker hkerN]
      exact comap_mono ((le_centralizer_iff.mp hXF).trans (Subgroup.centralizer_le_normalizer _))
    obtain ⟨L,hL,hQL,_,hne⟩ := lift_noncentralized_component P₀ hK hKP
    exact ⟨hfit,Or.inr ⟨L,hL,hQL,hne⟩⟩

private def restrictedQuotientEquiv {X M : Subgroup G} (hXM : X ≤ M) :
    XiQuotient (X.subgroupOf M) ≃* XiQuotient X :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXM)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXM))

private def restrictedFrattiniEquiv {X M : Subgroup G} (hXM : X ≤ M) :
    XiFrattiniQuotient (X.subgroupOf M) ≃* XiFrattiniQuotient X :=
  QuotientGroup.congr _ _ (restrictedQuotientEquiv hXM)
    (frattini_map_mulEquiv (restrictedQuotientEquiv hXM))

omit [Finite G] in
private theorem restrictedFrattiniEquiv_apply_mk {X M : Subgroup G}
    (hXM : X ≤ M) (x : X.subgroupOf M) :
    restrictedFrattiniEquiv hXM (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) =
      QuotientGroup.mk' (frattini (XiQuotient X))
        (QuotientGroup.mk' (pCore 2 X) (subgroupOfEquivOfLe hXM x)) := rfl

omit [Finite G] in
private theorem restricted_equivariant {X S M : Subgroup G}
    (hXM : X ≤ M) (hn : S ≤ normalizer (X : Set G))
    (hn' : S.subgroupOf M ≤ normalizer (X.subgroupOf M : Set M))
    (s : S.subgroupOf M) (a : XiFrattiniQuotient (X.subgroupOf M)) :
    restrictedFrattiniEquiv hXM
      (xiFrattiniAction (S.subgroupOf M) (X.subgroupOf M) hn' s a) =
        xiFrattiniAction S X hn ⟨s, s.property⟩ (restrictedFrattiniEquiv hXM a) := by
  induction a using QuotientGroup.induction_on with | H a =>
    induction a using QuotientGroup.induction_on with | H x =>
      change restrictedFrattiniEquiv hXM
        (xiFrattiniAction (S.subgroupOf M) (X.subgroupOf M) hn' s
          (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
        xiFrattiniAction S X hn ⟨s, s.property⟩
          (restrictedFrattiniEquiv hXM (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
        restrictedFrattiniEquiv_apply_mk]
      rfl


/-- Restrict the actual full actor and its Frattini action to an overgroup. -/
theorem fitting_and_component_in {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (H X M S : Subgroup G) (hH : IsStronglyQuasithin H)
    (hXM : X ≤ M) (hMH : M ≤ H) (hn : M ≤ normalizer (X : Set G))
    (hX : IsPPerfect 2 X) (hq : XiOddQuotient p (XiQuotient X))
    (hS : IsSylowIn 2 S H) (hSX : S ≤ normalizer (X : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ s : M, ∀ a ∈ A, xiFrattiniAction M X hn s a ∈ A) → A=⊥ ∨ A=⊤) :
    (twoFittingCore H).map H.subtype ≤ normalizer (X : Set G) ∧
      (H ≤ normalizer (X : Set G) ∨ ∃ K : Subgroup G,
        K ∈ cComponentsIn H ∧ IsQuasisimple (XiQuotient K) ∧
          ¬ ⁅K,X⁆ ≤ H.pCoreIn 2) := by
  let X' := X.subgroupOf H
  let M' := M.subgroupOf H
  have hXH : X ≤ H := hXM.trans hMH
  have hn' : M' ≤ normalizer (X' : Set H) :=
    (comap_mono hn).trans (X.le_normalizer_comap H.subtype)
  have hi' : ∀ A : Subgroup (XiFrattiniQuotient X'),
      (∀ s : M', ∀ a ∈ A, xiFrattiniAction M' X' hn' s a ∈ A) → A=⊥ ∨ A=⊤ := by
    intro A hA
    let e := restrictedFrattiniEquiv hXH
    have hi : ∀ s : M, ∀ a ∈ A.map e.toMonoidHom,
        xiFrattiniAction M X hn s a ∈ A.map e.toMonoidHom := by
      rintro s a ⟨b,hb,rfl⟩
      let s' : M' := ⟨⟨s,hMH s.property⟩,s.property⟩
      refine ⟨xiFrattiniAction _ _ hn' s' b, hA s' b hb, ?_⟩
      exact restricted_equivariant hXH hn hn' s' b
    rcases hirr (A.map e.toMonoidHom) hi with hb | ht
    · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hb)
    · right
      apply map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (map_top_of_surjective e.toMonoidHom e.surjective).symm
  obtain ⟨T,hT⟩ := hS
  have hcore : pCore 2 H ≤ normalizer (X' : Set H) := by
    intro z hz
    apply X.le_normalizer_comap H.subtype
    exact hSX (hT ▸ mem_map_of_mem H.subtype (pCore_isPGroup.le_sylow_of_normal T hz))
  let P : Sylow p X' := default
  obtain ⟨hfit,ha⟩ := fitting_and_component ho hH X' M' (subgroupOf_mono H hXM) hn'
      (hX.of_surjective (subgroupOfEquivOfLe hXH).symm.toMonoidHom
        (subgroupOfEquivOfLe hXH).symm.surjective)
      (hq.of_mulEquiv (restrictedQuotientEquiv hXH).symm) hcore hi' P
  have hfitG : (twoFittingCore H).map H.subtype ≤ normalizer (X : Set G) := by
    have hh := (map_mono (f := H.subtype) hfit).trans (X'.le_normalizer_map H.subtype)
    simpa only [X',map_subgroupOf_eq_of_le hXH] using hh
  refine ⟨hfitG,?_⟩
  rcases ha with hnorm | ⟨K,hK,hQK,hKP⟩
  · exact Or.inl ((normal_subgroupOf_iff_le_normalizer hXH).mp hnorm)
  · right
    let L := K.map H.subtype
    have hLH : L ≤ H := map_subtype_le K
    have he : L.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
    let e : K ≃* L := K.equivMapOfInjective H.subtype H.subtype_injective
    let eqv : XiQuotient K ≃* XiQuotient L :=
      QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    refine ⟨L,⟨hLH,he.symm ▸ hK⟩,hQK.of_mulEquiv eqv,?_⟩
    intro hc
    apply hKP
    have hKX : ⁅K,X'⁆ ≤ pCore 2 H := by
      apply (map_le_map_iff_of_injective H.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hXH]
      exact hc
    exact (commutator_mono le_rfl (map_subtype_le _)).trans hKX


end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerComponents
