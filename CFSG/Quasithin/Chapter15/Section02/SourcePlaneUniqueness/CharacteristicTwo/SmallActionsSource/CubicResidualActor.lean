module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CubicResidualSeed
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.CubicNormalizer

/-!
# A normalizing actor for the cubic branch of 15.2.22

Write Y for the original residual and E for the corrected outside seed.
In the cubic-image branch, O₂(M ∩ Mc) normalizes YE: in M/O₂(M),
its commutator with the two-perfect image of E lies in the cubic residual
of its normal closure. Normalizer lifting over O₂(M) gives the literal
normalization. The same core cannot lie in S, since a normalizer of the
nonnormal cubic image acts by a common scalar on the elementary-nine
residual, whereas the core moves only a cubic subgroup.

Thus the actual core supplies t in T − S normalizing YE. The seed is
normal in YE by CubicResidualSeed, so its t-conjugate has the required
commutator containment. No chosen-actor assumption remains.

Source: Aschbacher--Smith 15.2.22, printed pp.1114--1115,
refs/quasithin.pdf. Earlier Omega and plane inputs retain their existing
producers and final discharge in the plane-uniqueness assembly.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (N : Subgroup G) :
    twoResidualAmbient N = (pResidual 2 N).map N.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext L
  constructor
  · rintro ⟨hn,n,hc⟩
    exact ⟨hn,IsPGroup.of_card hc⟩
  · rintro ⟨hn,hp⟩
    exact ⟨hn,IsPGroup.iff_card.mp hp⟩

private theorem cubic_normal_commutator (N E : Subgroup G) [N.Normal]
    (hcore : pCore 2 N = ⊥) (hc : Nat.card (pResidual 2 N) = 3)
    (hp : IsPPerfect 2 E) : ⁅N,E⁆ ≤ (pResidual 2 N).map N.subtype := by
  let A := (pResidual 2 N).map N.subtype
  have hA : Nat.card A = 3 := (card_map_of_injective N.subtype_injective).trans hc
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hAut : IsPGroup 2 (MulAut A) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut,hA,Nat.totient_prime Nat.prime_three]
    rfl)
  let f : E →* MulAut A := A.normalizerMonoidHom.comp (inclusion le_normalizer_of_normal)
  have hf := hp.hom_eq_one_of_isPGroup hAut f
  have hEA : E ≤ centralizer (A : Set G) := by
    intro e he a ha
    have hh := congrArg (fun g : E →* MulAut A => (g ⟨e,he⟩ ⟨a,ha⟩ : G)) hf
    change e * a * e⁻¹ = a at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hNA : N ⊓ centralizer (A : Set G) ≤ A := by
    intro x hx
    have hz : (⟨x,hx.1⟩ : N) ∈ centralizer (pResidual 2 N : Set N) := by
      intro y hy
      apply Subtype.ext
      exact hx.2 y (mem_map_of_mem N.subtype hy)
    exact mem_map_of_mem N.subtype ((centralizer_pResidual_le_of_pCore_eq_bot hcore) hz)
  apply (le_inf (commutator_le_left N E) ?_).trans hNA
  exact (commutator_mono le_rfl hEA).trans (commutator_le_right _ _)

private theorem cubic_movement_not_normalizes
    (R B : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hB : Nat.card B = 3) (hn : ¬ B.Normal)
    (hc : Nat.card (⁅pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),R⁆ : Subgroup _) = 3) :
    ¬ R ≤ normalizer (B : Set _) := by
  let A := pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  have cube : ∀ x ∈ A, x ^ 3 = 1 := by
    dsimp only [A]
    rw [SymmetricThreeProductResidual.residual_eq]
    have hc3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      rfl
    intro x hx
    exact Prod.ext
      (congrArg Subtype.val (hc3 ▸ pow_card_eq_one' (x := (⟨x.1,hx.1⟩ : alternatingGroup (Fin 3)))))
      (congrArg Subtype.val (hc3 ▸ pow_card_eq_one' (x := (⟨x.2,hx.2⟩ : alternatingGroup (Fin 3)))))
  intro hR
  by_cases hfix : ∀ r ∈ R, ∀ x ∈ A, r*x*r⁻¹=x
  · have hz : ⁅A,R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
      intro x hx r hr
      exact mul_inv_eq_iff_eq_mul.mp (hfix r hr x hx))
    change Nat.card (⁅A,R⁆ : Subgroup _) = 3 at hc
    rw [hz,card_bot] at hc
    contradiction
  · push Not at hfix
    obtain ⟨r,hr,x,hx,hxmove⟩ := hfix
    have hinv := (SymmetricThreeProductResidual.normalizer_cubic_scalar B hB hn r (hR hr)).resolve_left
      (fun hh => hxmove (hh x (cube x hx)))
    have hA : A ≤ ⁅A,R⁆ := by
      intro a ha
      have hs : a*a = a⁻¹ := eq_inv_of_mul_eq_one_left (by
        simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using cube a ha)
      have hs' : a⁻¹*a⁻¹=a := by simpa only [mul_inv_rev,inv_inv] using congrArg Inv.inv hs
      have he : ⁅a⁻¹,r⁆ = a := by
        calc
          _ = a⁻¹*(r*a*r⁻¹) := by simp only [commutatorElement_def,inv_inv,mul_assoc]
          _ = a⁻¹*a⁻¹ := by rw [hinv a (cube a ha)]
          _ = a := hs'
      rw [←he]
      exact commutator_mem_commutator (A.inv_mem ha) hr
    have he := le_antisymm (commutator_le_left A R) hA
    change Nat.card (⁅A,R⁆ : Subgroup _) = 3 at hc
    rw [he] at hc
    have hh : Nat.card A = 9 := SymmetricThreeProductResidual.residual_card
    omega

variable {T : Sylow 2 G} {M Mc V H ZS I E : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

theorem Seed.cubic_core_normalizes_join
    (s : Seed M I (smallActionS T ZS) E) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    (M ⊓ Mc).pCoreIn 2 ≤ normalizer ((Y ⊔ E : Subgroup G) : Set G) := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hc
  let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
  let D := Y ⊔ E
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let A := (Y.subgroupOf M).map q
  let B := (E.subgroupOf M).map q
  let N := normalClosure (R.map q : Set (M ⧸ pCore 2 M))
  have hEM : E ≤ M := s.le_NI.trans inf_le_left
  have hYM : Y ≤ M := source_omega_caseIIResidual_le T hsource.maximal.1.2
    hsource.prepared.normalized ho
  let : (Y.subgroupOf M).Normal := source_omega_lemma_15_2_3_2 T hsource.maximal.1.2
    hsource.prepared.normalized ho
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hDM : D ≤ M := sup_le hYM hEM
  have hAM : A = (pResidual 2 N).map N.subtype := by
    rw [show A = (Y.subgroupOf M).map q from rfl,
      source_omega_caseIIResidual_image T hsource.maximal.1.2 hsource.prepared.normalized ho
        q (QuotientGroup.mk'_surjective _),residual_notation]
  have hNcore : pCore 2 N = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : N.Normal).isSubnormal,
      pCore_quotient_pCore_eq_bot]
    exact N.subtype.ker_eq_bot_iff.mpr N.subtype_injective
  have hNcard : Nat.card (pResidual 2 N) = 3 := by
    rw [←card_map_of_injective N.subtype_injective,←hAM]
    exact source_omega_cyclic_star_card T hsource.maximal.1.2 hsource.partner
      hsource.prepared ho hc
  have hpB : IsPPerfect 2 B := s.perfect.of_surjective
    ((q.subgroupMap (E.subgroupOf M)).comp (subgroupOfEquivOfLe hEM).symm.toMonoidHom)
    ((q.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hEM).symm.surjective)
  have hRB : ⁅R.map q,B⁆ ≤ A := by
    rw [hAM]
    exact (commutator_mono (subset_normalClosure) le_rfl).trans
      (cubic_normal_commutator N B hNcore hNcard hpB)
  have hRqD : R.map q ≤ normalizer (((D.subgroupOf M).map q : Subgroup _) : Set _) := by
    rw [show D = Y ⊔ E from rfl,subgroupOf_sup hYM hEM,Subgroup.map_sup]
    apply le_normalizer_iff.mpr
    intro r hr x hx
    have hh : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj r).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact mem_sup_left ((inferInstance : A.Normal).conj_mem a ha r)
      · intro b hb
        have hm := (A ⊔ B).mul_mem
          (mem_sup_left (hRB (commutator_mem_commutator hr hb))) (mem_sup_right hb)
        change r * b * r⁻¹ ∈ A ⊔ B
        simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
    exact hh hx
  have hpY : IsPPerfect 2 Y := by
    let e := MulEquiv.subgroupCongr ((source_omega_caseIIResidual_eq T
      hsource.maximal.1.2 hsource.prepared.normalized ho (Mc := Mc)).trans (residual_notation _))
    exact (isPPerfect_embedded_pResidual 2 _).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hpD : IsPPerfect 2 (D.subgroupOf M) := (isPPerfect_sup Y E hpY s.perfect).of_surjective
    (subgroupOfEquivOfLe hDM).symm.toMonoidHom (subgroupOfEquivOfLe hDM).symm.surjective
  have hn : q.ker ≤ normalizer (D.subgroupOf M : Set M) := by
    rw [QuotientGroup.ker_mk',←subgroupOf_normalizer_eq hDM]
    intro x hx
    have hxs := omega_core_le_planeSylow d ho (mem_map_of_mem M.subtype hx)
    have hMn : M ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_omega_lemma_15_2_3_2 T hsource.maximal.1.2 hsource.prepared.normalized ho)
    exact ((le_inf ((inf_le_left.trans hsource.maximal.1.2).trans hMn) s.normalized).trans
      (normalizer_inf_normalizer_le_normalizer_sup Y E)) hxs
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hh : R ≤ normalizer (D.subgroupOf M : Set M) := by
    rw [←comap_normalizer_map_of_pPerfect q _ hpD hk hn]
    exact map_le_iff_le_comap.mp hRqD
  rw [←subgroupOf_normalizer_eq hDM] at hh
  intro r hr
  exact hh (show (⟨r,((pCoreIn_le 2 _).trans inf_le_left) hr⟩ : M) ∈ R from hr)

theorem Seed.cubic_core_not_le_planeSylow
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) E) (hout : ¬ E ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    ¬ (M ⊓ Mc).pCoreIn 2 ≤ smallActionS T ZS := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hc hRS
  let e := ho.2.2.2.1.some
  let f := e.toMonoidHom.comp (action hsource)
  let R := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  let B := (E.subgroupOf M).map (action hsource)
  have hBcard : Nat.card B = 3 := by
    rw [show B = (E.subgroupOf M).map (action hsource) from rfl,
      s.action_image_eq_residual d hI hout eNI,
      card_map_of_injective (intersectionImage hsource I).subtype_injective]
    have hh := congrArg (fun K : Subgroup (Equiv.Perm (Fin 3)) => Nat.card K)
      (map_pResidual_of_surjective 2 eNI.toMonoidHom eNI.surjective)
    rwa [card_map_of_injective eNI.injective,
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at hh
  have hn : ¬ (B.map e.toMonoidHom).Normal := by
    intro hn
    have hh := hn.comap e.toMonoidHom
    rw [comap_map_eq_self_of_injective e.injective] at hh
    exact s.action_image_not_normal d hI hout eNI hh
  have hmov : Nat.card (⁅pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      R.map f⁆ : Subgroup _) = 3 := by
    have he := source_omega_caseIIResidual_image_commutator T hsource.maximal.1.2
      (d.geometry.outside.1.1.2.trans d.geometry.in_partner) hsource.prepared.normalized ho
      (Mc := Mc)
    change Nat.card (((caseIIResidual T M (chosenStarredPreimage M V
      hsource.prepared.normalized) Mc).subgroupOf M).map
        (actionHom M V hsource.prepared.normalized).rangeRestrict) = 3 at hc
    rw [he] at hc
    rw [←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
      show R.map f = (R.map (action hsource)).map e.toMonoidHom from (map_map _ _ _).symm,
      ←map_commutator,card_map_of_injective e.injective]
    exact hc
  apply cubic_movement_not_normalizes (R.map f) (B.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hBcard) hn hmov
  have hEM : E ≤ M := s.le_NI.trans inf_le_left
  have hRE : R ≤ normalizer (E.subgroupOf M : Set M) := by
    rw [←subgroupOf_normalizer_eq hEM]
    exact comap_mono (hRS.trans s.normalized)
  have hm := (map_mono (f := f) hRE).trans (le_normalizer_map f)
  rw [show (E.subgroupOf M).map f = B.map e.toMonoidHom from (map_map _ _ _).symm] at hm
  exact hm

theorem Seed.exists_cubic_normalizing_actor
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) E) (hout : ¬ E ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 3 →
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ smallActionS T ZS ∧
      t ∈ normalizer ((Y ⊔ E : Subgroup G) : Set G) := by
  let := hsource.prepared.elementary
  intro ho
  dsimp only
  intro hc
  obtain ⟨t,ht,htS⟩ := SetLike.not_le_iff_exists.mp
    (s.cubic_core_not_le_planeSylow d hI hout eNI ho hc)
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTMc := d.geometry.outside.1.1.2.trans d.geometry.in_partner
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf hsource.maximal.1.2 hTMc)] using
      pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hsource.maximal.1.2 hTMc))
  exact ⟨t,hRT ht,htS,s.cubic_core_normalizes_join d ho hc ht⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
