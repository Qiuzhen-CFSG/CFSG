module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import CFSG.Quasithin.Chapter14.Section06.SuitableInvolutionIndices
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalizer
public import Theory.GroupTheory.PRadicalSylowNormalizer
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PCoreRestriction
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import Theory.GroupTheory.PResidual.NormalComplement
public import FeitThompson.FinalTheorem
public import CFSG.Quasithin.ChapterC.Section06.Original.Guarded
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer.SmallQuotient
public import CFSG.Quasithin.ChapterA.Section05To06.Ordering
public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import CFSG.Quasithin.Chapter12.Section08
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# Suitable involutions act nontrivially on the original plane

For a suitable involution u, the central character q ↦ [u,q] on the
local two-core has kernel of index two. If its kernel centralizes the
plane, that kernel equals the plane centralizer: otherwise the whole
core centralizes the conjugate span containing u. The original Sylow
group would then normalize the character kernel and preserve its binary
values, contrary to the second suitability condition.

The literal S₃ action on the plane turns this nontrivial actor into a
commutator generator of the cubic residual image. Two-perfectness lifts
that equality through the original two-core kernel. Applying the same
argument at Mc and at H supplies both commutator identities in 14.6.3(3).
The same preparation gives both original core products in 14.6.3(1).
Since the abelian plane closure puts V in Tᵤ, noncentrality also proves
that Tᵤ is nonabelian. Its ambient normalizer meets each of M and Mc in
T₀: a member of M moving the central line would place two distinct lines
in C_V(Tᵤ), contradicting noncentrality. The two-maximal-local family
then controls normalizers of all T-normal subgroups of T₀ inside N_G(Tᵤ).
The remaining quotient-model classification of that ambient normalizer
is a separate obligation in 14.6.3(4).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 14.6.3(3), printed pp.1021–1022.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

private def coreCommutator (u : G) (hu : u ∈ D.UH) : D.QH →* D.V₁ where
  toFun q := ⟨⁅u, (q : G)⁆,
    h.commutator_UH_QH_le_point (commutator_mem_commutator hu q.property)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change ⁅u, (a : G) * (b : G)⁆ = ⁅u, (a : G)⁆ * ⁅u, (b : G)⁆
    have hb := h.commutator_UH_QH_le_point (commutator_mem_commutator hu b.property)
    have hc := h.H_centralizes (pCoreIn_le 2 D.H a.property) _ hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅u, (a : G)⁆ * ((a : G) * ⁅u, (b : G)⁆) * (a : G)⁻¹ := by group
      _ = _ := by rw [← hc]; group

private theorem coreCommutator_eq_one (u : G) (hu : u ∈ D.UH) (q : D.QH) :
    coreCommutator h u hu q = 1 ↔ (q : G) ∈ centralizer ({u} : Set G) := by
  change (⟨⁅u, (q : G)⁆, _⟩ : D.V₁) = 1 ↔ _
  rw [Subtype.ext_iff, mem_centralizer_singleton_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans eq_comm

/-- The first assertion of original 14.6.3(3), on the actual F.9 groups. -/
theorem suitable_core_centralizer_not_le (hplus : D.Vplus = D.V)
    (u : G) (hu : u ∈ D.UH)
    (hindex : (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2)
    (hmove : ¬ D.QH ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (D.T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
      ¬ D.QH ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    ¬ D.QH ⊓ centralizer ({u} : Set G) ≤ D.QH ⊓ centralizer (D.V : Set G) := by
  intro hle
  let f := coreCommutator h u hu
  let C := (centralizer (D.V : Set G)).subgroupOf D.QH
  have hker : f.ker = (centralizer ({u} : Set G)).subgroupOf D.QH := by
    ext q
    exact coreCommutator_eq_one h u hu q
  have hr : Nat.card f.range = 2 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [h.point_card] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · exfalso
      apply hmove
      intro q hq
      apply (coreCommutator_eq_one h u hu ⟨q,hq⟩).mp
      have hm : f ⟨q,hq⟩ ∈ f.range := ⟨⟨q,hq⟩,rfl⟩
      simpa only [card_eq_one.mp hc, mem_bot] using hm
    · exact hc
  have hi : f.ker.index = 2 := by rw [index_ker,hr]
  have hkerC : f.ker ≤ C := by
    intro q hq
    exact (hle ⟨q.property,(coreCommutator_eq_one h u hu q).mp hq⟩).2
  have hCne : C ≠ ⊤ := by
    intro hc
    have hQV : D.QH ≤ centralizer (D.V : Set G) := by
      intro q hq
      exact show (⟨q,hq⟩ : D.QH) ∈ C from hc ▸ mem_top _
    have hQU : D.QH ≤ centralizer (D.UH : Set G) := by
      change D.QH ≤ centralizer (conjugateSpanBy D.Vplus D.H : Set G)
      rw [hplus]
      exact le_centralizer_conjugateSpanBy_of_normalizes _ _ _ (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)) hQV
    exact hmove (fun q hq => mem_centralizer_singleton_iff.mpr (hQU hq u hu).symm)
  have hker_eq : f.ker = C := by
    have hp : (f.ker.relIndex C * C.index).Prime := by
      rw [relIndex_mul_index hkerC,hi]
      exact Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hc⟩ | ⟨_,hc⟩
    · exact (hCne (index_eq_one.mp hc)).elim
    · exact le_antisymm hkerC (relIndex_eq_one.mp hc)
  have hK : D.QH ⊓ centralizer ({u} : Set G) = D.QH ⊓ centralizer (D.V : Set G) := by
    ext q
    constructor
    · exact fun hq => hle hq
    · intro hq
      have hh : (⟨q,hq.1⟩ : D.QH) ∈ f.ker := hker_eq ▸ hq.2
      exact ⟨hq.1,(coreCommutator_eq_one h u hu ⟨q,hq.1⟩).mp hh⟩
  have hTK : (D.T : Subgroup G) ≤ normalizer
      ((D.QH ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) := by
    rw [hK]
    exact (le_inf (h.T_le_H.trans (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)))
      (h.T_normalizes_V.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hout : ¬ (D.T : Subgroup G) ≤ suitableQuotientCentralizer h u := by
    intro hh
    have hi' := relIndex_eq_one.mpr hh
    omega
  obtain ⟨t,ht,ht0⟩ := SetLike.not_le_iff_exists.mp hout
  apply hproduct t ht ht0
  intro q hq
  have hq' : t * q * t⁻¹ ∈ D.QH :=
    ((ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)) (h.T_le_H ht) q).mp hq
  have hzero : f ⟨t*q*t⁻¹,hq'⟩ = 1 ↔ f ⟨q,hq⟩ = 1 := by
    rw [coreCommutator_eq_one,coreCommutator_eq_one]
    have hh : (t*q*t⁻¹ ∈ D.QH ∧ t*q*t⁻¹ ∈ centralizer ({u} : Set G)) ↔
        (q ∈ D.QH ∧ q ∈ centralizer ({u} : Set G)) := (hTK ht q).symm
    simpa only [hq, hq', true_and] using hh
  have heq : f ⟨t*q*t⁻¹,hq'⟩ = f ⟨q,hq⟩ := by
    by_cases hz : f ⟨q,hq⟩ = 1
    · exact (hzero.mpr hz).trans hz.symm
    · obtain ⟨z,_,hz'⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
      exact (hz' _ (mt hzero.mp hz)).trans (hz' _ hz).symm
  have hc : ⁅u,t*q*t⁻¹⁆ = ⁅u,q⁆ := congrArg Subtype.val heq
  have hv : ⁅(MulAut.conj t⁻¹) u,q⁆ = ⁅u,q⁆ := by
    have hh := congrArg (MulAut.conj t⁻¹) hc
    rw [map_commutatorElement] at hh
    have hqback : (MulAut.conj t⁻¹) (t*q*t⁻¹) = q := by
      change t⁻¹*(t*q*t⁻¹)*(t⁻¹)⁻¹=q
      group
    rw [hqback] at hh
    have hz := h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)
    have hcent := h.H_centralizes (h.T_le_H ((D.T : Subgroup G).inv_mem ht)) _ hz
    have hfix : (MulAut.conj t⁻¹) ⁅u,q⁆ = ⁅u,q⁆ := by
      change t⁻¹ * ⁅u,q⁆ * (t⁻¹)⁻¹ = ⁅u,q⁆
      rw [← hcent, mul_inv_cancel_right]
    exact hh.trans hfix
  have hsquare : ⁅u,q⁆ * ⁅u,q⁆ = 1 := by
    have hh := pow_card_eq_one' (x := f ⟨q,hq⟩)
    rw [h.point_card,pow_two] at hh
    exact congrArg Subtype.val hh
  have hz := h.commutator_UH_QH_le_point (commutator_mem_commutator hu hq)
  have hcent := h.H_centralizes (h.UH_le_H hu) _ hz
  apply mem_centralizer_singleton_iff.mpr
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hv,←hcent,mul_inv_cancel_right]
  exact hsquare
/-- The actual suitable centralizer is nonabelian: it contains the plane and
its core-centralizer acts nontrivially on that plane. This rules out either
small C.6 model as soon as its two-core is identified with this centralizer. -/
theorem suitableCentralizer_not_abelian (hplus : D.Vplus = D.V)
    (hab : IsMulCommutative D.UH)
    (u : G) (hu : u ∈ D.UH)
    (hindex : (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2)
    (hmove : ¬ D.QH ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (D.T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
      ¬ D.QH ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    ¬ IsMulCommutative (suitableCentralizer (D := D) u) := by
  intro ha
  let := hab
  let := ha
  have hVU : D.V ≤ D.UH := by
    change D.V ≤ conjugateSpanBy D.Vplus D.H
    rw [hplus]
    exact le_conjugateSpanBy _ _
  have hVTu : D.V ≤ suitableCentralizer (D := D) u := by
    intro v hv
    refine ⟨h.V_le_T hv,mem_centralizer_singleton_iff.mpr ?_⟩
    exact setLike_mul_comm (hVU hv) hu
  apply suitable_core_centralizer_not_le h hplus u hu hindex hmove hproduct
  intro q hq
  refine ⟨hq.1,?_⟩
  intro v hv
  exact setLike_mul_comm (hVTu hv)
    (show q ∈ suitableCentralizer (D := D) u from ⟨h.QH_le_T hq.1,hq.2⟩)

open CFSG.Quasithin.Chapter12.Section08

private theorem s3_inverse_commutator : ∀ a b : Equiv.Perm (Fin 3),
    a ∈ alternatingGroup (Fin 3) → b ∉ alternatingGroup (Fin 3) → ⁅a⁻¹,b⁆ = a := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem s3_residual_commutator (W : Subgroup (Equiv.Perm (Fin 3)))
    (hW : IsPGroup 2 W) (hne : W ≠ ⊥) :
    pResidual 2 (Equiv.Perm (Fin 3)) = ⁅pResidual 2 (Equiv.Perm (Fin 3)),W⁆ := by
  rw [Equiv.Perm.twoResidual_eq_alternating]
  let A := alternatingGroup (Fin 3)
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by
    dsimp [A]
    rw [nat_card_alternatingGroup]
    norm_num)
  obtain ⟨w,hw⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hwA : (w : Equiv.Perm (Fin 3)) ∉ A := by
    intro ha
    have hz : (w : Equiv.Perm (Fin 3)) ∈ (⊥ : Subgroup (Equiv.Perm (Fin 3))) :=
      (hW.disjoint_of_coprime hA (by decide)).le_bot ⟨w.property,ha⟩
    exact hw (Subtype.ext hz)
  apply le_antisymm
  · intro a ha
    rw [← s3_inverse_commutator a w ha hwA]
    exact commutator_mem_commutator (A.inv_mem ha) w.property
  · exact le_normalizer_iff_commutator_le_left.mp le_normalizer_of_normal

variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}

/-- Any Sylow subgroup of actors that is nontrivial on the original plane
commutator-generates the actual two-perfect residual. -/
theorem rankTwo_residual_eq_commutator (h : RankTwoHypothesis K T L M)
    (C : Subgroup G) (hCT : C ≤ (T : Subgroup G))
    (hmove : ¬ C ≤ centralizer (rankTwoSeed T M : Set G)) : L = ⁅L,C⁆ := by
  let J := L ⊔ (T : Subgroup G)
  have hLJ : L ≤ J := le_sup_left
  have hCJ : C ≤ J := hCT.trans le_sup_right
  let a := setupSeedAction J (rankTwoSeed T M)
    ((sup_le h.L_le h.sylow_le).trans RankTwoHypothesis.M_normalizes_seed)
  obtain ⟨e⟩ := h.seedAut_model
  let f := e.toMonoidHom.comp a
  have hker : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact h.literal_action_kernel
  have hLimage : (L.subgroupOf J).map f = pResidual 2 (Equiv.Perm (Fin 3)) := by
    have hmap : (L.subgroupOf J).map a =
        (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range := by
      ext b
      constructor
      · rintro ⟨l,hl,rfl⟩
        exact ⟨⟨l,hl⟩,rfl⟩
      · rintro ⟨l,rfl⟩
        exact ⟨⟨l,hLJ l.property⟩,l.property,rfl⟩
    change (L.subgroupOf J).map (e.toMonoidHom.comp a) = _
    rw [←map_map,hmap,h.L_action_range,map_pResidual]
  have hCimage : (C.subgroupOf J).map f ≠ ⊥ := by
    intro he
    have hCf : C.subgroupOf J ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp he
    apply hmove
    intro c hc
    have hc0 := hCf (show (⟨c,hCJ hc⟩ : J) ∈ C.subgroupOf J from hc)
    have hc1 : a ⟨c,hCJ hc⟩ = 1 := by
      apply e.injective
      change e (a ⟨c,hCJ hc⟩) = 1 at hc0
      simpa only [map_one] using hc0
    exact (setupSeedAction_ker J (rankTwoSeed T M) _).le hc1
  have heq := eq_commutator_of_isPPerfect_of_map_eq (L.subgroupOf J) (C.subgroupOf J)
    (((pResidual_eq_top_iff 2 L).mp h.L_residual).of_surjective
      (subgroupOfEquivOfLe hLJ).symm.toMonoidHom (subgroupOfEquivOfLe hLJ).symm.surjective)
    (by
      intro c hc
      rw [← subgroupOf_normalizer_eq hLJ]
      exact h.sylow_normalizes_L (hCT hc))
    f (by rw [hker]; exact pCore_isPGroup)
    (by rw [hLimage]; exact s3_residual_commutator _ ((T.isPGroup'.to_le hCT).comap_subtype.map f) hCimage)
  have hm := congrArg (Subgroup.map J.subtype) heq
  simpa only [map_commutator,map_subgroupOf_eq_of_le hLJ,map_subgroupOf_eq_of_le hCJ] using hm

open CFSG.Quasithin.Chapter14.SourcePreliminaries CFSG.Quasithin.Chapter15.Section03 CFSG.Quasithin.ChapterA.Section05To06

/-- Original 14.6.3(3)'s `Q_H` centralizer and residual conclusions, together
with the nonabelianness needed to exclude the small C.6.1 models. All action
and kernel data are those constructed by the original rank-two source. -/
private theorem source_suitable_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    (let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    let T0 := suitableQuotientCentralizer h u
    Tu.relIndex T0 = 2 ∧ Tu.relIndex (T : Subgroup G) = 4 ∧
      T0 = Mc.pCoreIn 2 ⊔ Tu ∧ T0 = H.pCoreIn 2 ⊔ Tu ∧
      (T : Subgroup G) ⊓ normalizer (Tu : Set G) = T0) ∧
    (¬ H.pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤
        H.pCoreIn 2 ⊓ centralizer (localModule T M : Set G) ∧
      ¬ Mc.pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤
        Mc.pCoreIn 2 ⊓ centralizer (localModule T M : Set G) ∧
      sourceResidual M Mc = ⁅sourceResidual M Mc,
        Mc.pCoreIn 2 ⊓ centralizer ({u} : Set G)⁆ ∧
      sourceResidual M Mc = ⁅sourceResidual M Mc,
        H.pCoreIn 2 ⊓ centralizer ({u} : Set G)⁆ ∧
      ¬ IsMulCommutative ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis :=
    source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQle : Mc.pCoreIn 2 ≤ D.QH :=
    (le_inf (hQMcT.trans hH.1.2) le_rfl).trans (inf_pCoreIn_le_of_le 2 hHMc)
  have hm : ¬ D.QH ≤ centralizer ({u} : Set G) := fun hh => hmove (hQle.trans hh)
  have hp : ∀ t ∈ (D.T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
      ¬ D.QH ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G) :=
    fun t ht hn hc => hproduct t ht hn (hQle.trans hc)
  have hc := suitable_core_centralizer_not_le h rfl u hu hindex hm hp
  have ha : IsMulCommutative D.UH := by
    let := hab
    exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
      setLike_mul_comm ((conjugateSpanBy_mono le_rfl hHMc) hx)
        ((conjugateSpanBy_mono le_rfl hHMc) hy)
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hMcOutside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩,fun hh => hH.2 (hHMc.trans hh)⟩
  let D0 : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h0 : D0.Hypothesis :=
    source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab Mc hMcOutside
  have hu0 : u ∈ D0.UH := (conjugateSpanBy_mono le_rfl hHMc) hu
  have hsame : suitableQuotientCentralizer h0 u = suitableQuotientCentralizer h u := by
    ext x
    change (x ∈ (T : Subgroup G) ∧ x ∈ h0.kernel (zpowers u)) ↔
      (x ∈ (T : Subgroup G) ∧ x ∈ h.kernel (zpowers u))
    rw [h0.mem_kernel_iff (zpowers_le.mpr (h0.UH_le_H hu0)),
      h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))]
    exact ⟨fun hx => ⟨hx.1,h.T_le_H hx.1,hx.2.2⟩,
      fun hx => ⟨hx.1,h0.T_le_H hx.1,hx.2.2⟩⟩
  have hi0 : (suitableQuotientCentralizer h0 u).relIndex (T : Subgroup G) = 2 := by
    rw [hsame]
    exact hindex
  have hp0 : ∀ t ∈ (D0.T : Subgroup G), t ∉ suitableQuotientCentralizer h0 u →
      ¬ D0.QH ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G) := by
    intro t ht hn
    rw [hsame] at hn
    exact hproduct t ht hn
  have hc0 := suitable_core_centralizer_not_le h0 rfl u hu0 hi0 hmove hp0
  have hr := Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e
  have hi := suitable_involution_indices h u hu hindex hm hp
  have hiMc := suitable_involution_indices h0 u hu0 hi0 hmove hp0
  refine ⟨⟨hi.1,hi.2.1,?_,hi.2.2.1,hi.2.2.2⟩,
    hc,hc0,?_,?_,suitableCentralizer_not_abelian h rfl ha u hu hindex hm hp⟩
  · exact hsame.symm.trans hiMc.2.2.1
  · apply rankTwo_residual_eq_commutator hr _ (inf_le_left.trans hQMcT)
    rw [Section02.rankTwoSeed_eq_localModule]
    exact fun hh => hc0 (le_inf inf_le_left hh)
  · apply rankTwo_residual_eq_commutator hr _ (inf_le_left.trans h.QH_le_T)
    rw [Section02.rankTwoSeed_eq_localModule]
    exact fun hh => hc (le_inf inf_le_left hh)


theorem source_suitable_core_and_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    ¬ H.pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤
        H.pCoreIn 2 ⊓ centralizer (localModule T M : Set G) ∧
      ¬ Mc.pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤
        Mc.pCoreIn 2 ⊓ centralizer (localModule T M : Set G) ∧
      sourceResidual M Mc = ⁅sourceResidual M Mc,
        Mc.pCoreIn 2 ⊓ centralizer ({u} : Set G)⁆ ∧
      sourceResidual M Mc = ⁅sourceResidual M Mc,
        H.pCoreIn 2 ⊓ centralizer ({u} : Set G)⁆ ∧
      ¬ IsMulCommutative ((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) :=
  (source_suitable_data hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct).2

/-- Original 14.6.3(1), retaining both original core products and the
literal normalizer inside the ambient Sylow subgroup. -/
theorem source_lemma_14_6_3_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    let T0 := suitableQuotientCentralizer h u
    Tu.relIndex T0 = 2 ∧ Tu.relIndex (T : Subgroup G) = 4 ∧
      T0 = Mc.pCoreIn 2 ⊔ Tu ∧ T0 = H.pCoreIn 2 ⊔ Tu ∧
      (T : Subgroup G) ⊓ normalizer (Tu : Set G) = T0 :=
  (source_suitable_data hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct).1

/-- The source normalizer calculations inside Mc, before the outside-local
argument: normalizing Tu also normalizes Tu O₂(Mc)=T0. -/
theorem suitable_local_normalizer
    (T : Sylow 2 G) (Mc Tu T0 : Subgroup G)
    (hTMc : (T : Subgroup G) ≤ Mc)
    (hjoin : T0 = Mc.pCoreIn 2 ⊔ Tu)
    (hinside : (T : Subgroup G) ⊓ normalizer (Tu : Set G) = T0)
    (hN0 : normalizer (T0 : Set G) = (T : Subgroup G)) :
    Mc ⊓ normalizer (Tu : Set G) = T0 ∧
      Chapter1.IsSylowIn 2 T0 (normalizer (Tu : Set G)) := by
  have hT0T : T0 ≤ (T : Subgroup G) := hinside ▸ inf_le_left
  have hT0N : T0 ≤ normalizer (Tu : Set G) := hinside ▸ inf_le_right
  have hlocal : Mc ⊓ normalizer (Tu : Set G) = T0 := by
    apply le_antisymm
    · intro x hx
      have hxQ : x ∈ normalizer (Mc.pCoreIn 2 : Set G) :=
        (Mc.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))) hx.1
      have hx0 : x ∈ normalizer (T0 : Set G) := by
        rw [hjoin]
        exact (normalizer_inf_normalizer_le_normalizer_sup _ _) ⟨hxQ,hx.2⟩
      exact hinside ▸ (show x ∈ (T : Subgroup G) ⊓ normalizer (Tu : Set G) from
        ⟨hN0 ▸ hx0,hx.2⟩)
    · exact le_inf (hT0T.trans hTMc) hT0N
  let I := normalizer (Tu : Set G)
  have hs : normalizer (T0.subgroupOf I : Set I) = T0.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq hT0N,hN0]
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ (x : G) ∈ T0
    exact ⟨fun hx => hinside ▸ (show (x : G) ∈ (T : Subgroup G) ⊓ I from
      ⟨hx,x.property⟩),fun hx => hT0T hx⟩
  obtain ⟨S,hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq (T0.subgroupOf I)
    (T.isPGroup'.to_le hT0T).comap_subtype hs
  refine ⟨hlocal,⟨S,?_⟩⟩
  rw [hS,map_subgroupOf_eq_of_le hT0N]

/-- An automorphism normalizing both Tu and the plane must fix its central
line: moving the line would force the whole plane to centralize Tu. -/
private theorem plane_normalizer_fixes_line (V Z Tu : Subgroup G)
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2) (hZV : Z ≤ V)
    (hZT : Z ≤ centralizer (Tu : Set G))
    (hmove : ¬ Tu ≤ centralizer (V : Set G)) :
    normalizer (Tu : Set G) ⊓ normalizer (V : Set G) ≤ centralizer (Z : Set G) := by
  intro x hx
  by_contra hxc
  have hxn : x ∉ normalizer (Z : Set G) :=
    fun h => hxc (normalizer_le_centralizer_of_card_two Z hZ h)
  let Zx := Z.map (MulAut.conj x).toMonoidHom
  have hne : Zx ≠ Z := fun he => hxn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hZxV : Zx ≤ V := by
    rintro z ⟨v,hv,rfl⟩
    exact (hx.2 v).mp (hZV hv)
  have hZxT : Zx ≤ centralizer (Tu : Set G) := by
    rintro z ⟨v,hv,rfl⟩ t ht
    have ht' : x⁻¹ * t * x ∈ Tu := by
      have hh := ((normalizer (Tu : Set G)).inv_mem hx.1 t).mp ht
      change x⁻¹ * t * (x⁻¹)⁻¹ ∈ Tu at hh
      simpa only [inv_inv] using hh
    have hc := hZT hv _ ht'
    change t * (x*v*x⁻¹) = (x*v*x⁻¹) * t
    calc
      _ = x * ((x⁻¹*t*x)*v) * x⁻¹ := by group
      _ = x * (v*(x⁻¹*t*x)) * x⁻¹ := by rw [hc]
      _ = _ := by group
  have hjoin : Z ⊔ Zx = V := by
    have hle : Z ⊔ Zx ≤ V := sup_le hZV hZxV
    have hd : Nat.card (Z ⊔ Zx : Subgroup G) ∣ 4 := hV ▸ card_dvd_of_le hle
    have htwo : 2 ≤ Nat.card (Z ⊔ Zx : Subgroup G) := by
      rw [←hZ]
      exact Nat.card_le_card_of_injective (inclusion le_sup_left) (inclusion_injective _)
    have hnot : Nat.card (Z ⊔ Zx : Subgroup G) ≠ 2 := by
      intro hh
      have hz : Z = Z ⊔ Zx := eq_of_le_of_card_ge le_sup_left (by rw [hh,hZ])
      have hxcard : Nat.card Zx = 2 := (card_map_of_injective (MulAut.conj x).injective).trans hZ
      exact hne (eq_of_le_of_card_ge (le_sup_right.trans_eq hz.symm) (by rw [hxcard,hZ]))
    have he : Nat.card (Z ⊔ Zx : Subgroup G) = 4 := by
      obtain ⟨k,hk,hke⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (show Nat.card (Z ⊔ Zx : Subgroup G) ∣ 2 ^ 2 from hd)
      interval_cases k
      · have hh : Nat.card (Z ⊔ Zx : Subgroup G) = 1 := by simpa only [pow_zero] using hke
        omega
      · exact (hnot (by simpa only [pow_one] using hke)).elim
      · exact hke
    exact eq_of_le_of_card_ge hle (by rw [he,hV])
  apply hmove
  apply le_centralizer_iff.mp
  rw [←hjoin]
  exact sup_le hZT hZxT

/-- The original suitable-involution normalizer is Sylow-controlled and
meets both maximal local subgroups in T0. This supplies the source local
C(G,T0) control before its remaining quotient-model classification. -/
theorem source_suitable_normalizer_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G)) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    let T0 := suitableQuotientCentralizer h u
    let I := normalizer (Tu : Set G)
    Mc ⊓ I = T0 ∧ M ⊓ I = T0 ∧ Chapter1.IsSylowIn 2 T0 I ∧
      ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T0 → (T : Subgroup G) ≤ normalizer (C : Set G) →
        I ⊓ normalizer (C : Set G) = T0 := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let T0 := suitableQuotientCentralizer h u
  let I := normalizer (Tu : Set G)
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct
  have hc := source_suitable_core_and_residual hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct
  have hT0T : T0 ≤ (T : Subgroup G) := inf_le_left
  have hT0I : T0 ≤ I := hi.2.2.2.2.ge.trans inf_le_right
  have hQ0 : H.pCoreIn 2 ≤ T0 := le_sup_left.trans hi.2.2.2.1.ge
  have hN0 := source_lemma_14_6_3_2 hG T hempty hM hunique hmany hcard e hab H hH
    T0 hQ0 hT0T hindex hU3
  have hZcard := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,hpair⟩ := plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZcard
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hl := suitable_local_normalizer T Mc Tu T0 hTMc hi.2.2.1 hi.2.2.2.2 hN0
  have hm : ¬ Tu ≤ centralizer (localModule T M : Set G) := by
    intro hh
    apply hc.1
    intro q hq
    exact ⟨hq.1,hh ⟨h.QH_le_T hq.1,hq.2⟩⟩
  have hMI : M ⊓ I ≤ Mc := by
    rw [hMc]
    have hfix := plane_normalizer_fixes_line (localModule T M) (centralInvolutions T) Tu
      hcard hZcard (le_conjugateSpanBy _ _)
      ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le inf_le_left)) hm
    exact (le_inf inf_le_right
      (inf_le_left.trans (le_normalizer_conjugateSpanBy _ _))).trans hfix
  have heM : M ⊓ I = T0 := le_antisymm
    ((le_inf hMI inf_le_right).trans hl.1.le)
    (le_inf (hT0T.trans hM.1.2) hT0I)
  refine ⟨hl.1,heM,hl.2,?_⟩
  intro C hC hCT0 hTC
  have hp : IsPGroup 2 C := T.isPGroup'.to_le (hCT0.trans hT0T)
  have hlocal : IsTwoLocal (normalizer (C : Set G)) := ⟨C,hC,hp,rfl⟩
  obtain ⟨N,hCN,hN⟩ := Finite.exists_le_maximal hlocal
  have hmem : N ∈ ({M,Mc} : Set (Subgroup G)) :=
    hpair ▸ (show N ∈ maximalTwoLocalOvergroups (T : Subgroup G) from ⟨hN,hTC.trans hCN⟩)
  have hbound : I ⊓ normalizer (C : Set G) ≤ T0 := by
    rcases Set.mem_insert_iff.mp hmem with hn | hn
    · subst N
      exact (le_inf (inf_le_right.trans hCN) inf_le_left).trans heM.le
    · have hn' := Set.mem_singleton_iff.mp hn
      subst N
      exact (le_inf (inf_le_right.trans hCN) inf_le_left).trans hl.1.le
  exact le_antisymm hbound (le_inf hT0I (hT0T.trans hTC))

end CFSG.Quasithin.Chapter14.Section06


/-! The final original-source normalizer and centralizer conclusion (14.6.3(4)). -/
public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter12.Section08
open CFSG.Quasithin.Chapter14.SourcePreliminaries CFSG.Quasithin.Chapter15.Section03 CFSG.Quasithin.ChapterA.Section05To06
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_of_normal_two_index
    (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hi : U.relIndex (S : Subgroup G) = 2) : Group.IsSolvable G := by
  let q := QuotientGroup.mk' U
  let P := S.mapSurjective (QuotientGroup.mk'_surjective U)
  have hp : Nat.card P = 2 := by
    change Nat.card ((S : Subgroup G).map q) = 2
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    exact hi
  have ho := P.odd_card_twoResidual_of_isCyclic (isCyclic_of_prime_card hp)
  let : Group.IsSolvable (pResidual 2 (G ⧸ U)) := odd_order_theorem _ ho
  let : Group.IsSolvable ((G ⧸ U) ⧸ pResidual 2 (G ⧸ U)) :=
    @IsNilpotent.to_isSolvable _ _ (isPGroup_quotient_pResidual 2).isNilpotent
  let : Group.IsSolvable (G ⧸ U) :=
    (Group.isSolvable_iff_subgroup_quotient (pResidual 2 (G ⧸ U))).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable U := @IsNilpotent.to_isSolvable _ _ hU.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient U).mpr ⟨inferInstance,inferInstance⟩

omit [Finite G] in
private theorem characteristic_control_of_normal_control
    (T : Sylow 2 G) (I T0 : Subgroup G) (hT0I : T0 ≤ I)
    (_hT0T : T0 ≤ (T : Subgroup G))
    (hnorm : (T : Subgroup G) ≤ normalizer (T0 : Set G))
    (hcontrol : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T0 →
      (T : Subgroup G) ≤ normalizer (C : Set G) → I ⊓ normalizer (C : Set G) = T0) :
    (T0.subgroupOf I).characteristicNormalizerClosure ≤ T0.subgroupOf I := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hC hne
  let := hC
  let R := T0.subgroupOf I
  let e := subgroupOfEquivOfLe hT0I
  let D := C.map e.toMonoidHom
  let : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    rintro a x ⟨y,hy,rfl⟩
    exact ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hC (MulAut.congr e.symm a) hy,e.apply_symm_apply _⟩
  let A := D.map T0.subtype
  have hA : A ≠ ⊥ := fun hh => hne
    ((C.map_eq_bot_iff_of_injective e.injective).mp
      ((D.map_eq_bot_iff_of_injective T0.subtype_injective).mp hh))
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    hnorm.trans (normalizer_le_normalizer_characteristic_image T0 D)
  have he : (C.map R.subtype).map I.subtype = A := by
    change (C.map R.subtype).map I.subtype = (C.map e.toMonoidHom).map T0.subtype
    rw [map_map,map_map]
    rfl
  intro x hx
  have ha : (x : G) ∈ normalizer (A : Set G) := by
    rw [←he]
    exact (C.map R.subtype).le_normalizer_map I.subtype (mem_map_of_mem I.subtype hx)
  exact hcontrol A hA (map_subtype_le _) hTA ▸ ⟨x.property,ha⟩


omit [Finite G] in
private theorem c6_control_of_normal_control
    (T : Sylow 2 G) (I T0 : Subgroup G) (hT0I : T0 < I)
    (hT0T : T0 ≤ (T : Subgroup G)) (hi : T0.relIndex (T : Subgroup G) = 2)
    (hcontrol : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T0 →
      (T : Subgroup G) ≤ normalizer (C : Set G) → I ⊓ normalizer (C : Set G) = T0) :
    ∀ W : Subgroup G, W ≠ ⊥ → W ≤ T0 → I ≤ normalizer (W : Set G) →
      (T : Subgroup G) ⊓ normalizer (W : Set G) = T0 := by
  intro W hW hWT0 hIW
  let N := (T : Subgroup G) ⊓ normalizer (W : Set G)
  have h0N : T0 ≤ N := le_inf hT0T (hT0I.le.trans hIW)
  have hmul : T0.relIndex N * N.relIndex (T : Subgroup G) = 2 :=
    (relIndex_mul_relIndex T0 N (T : Subgroup G) h0N inf_le_left).trans hi
  have hd : T0.relIndex N ∣ 2 := ⟨_,hmul.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact le_antisymm (relIndex_eq_one.mp he) h0N
  · have hNT : N.relIndex (T : Subgroup G) = 1 := by
      rw [he] at hmul
      omega
    have hTN := (relIndex_eq_one.mp hNT).trans (show N ≤ normalizer (W : Set G) from inf_le_right)
    have hIeq : I = T0 := by
      rw [←hcontrol W hW hWT0 hTN,inf_eq_left.mpr hIW]
    exact (hT0I.ne hIeq.symm).elim

private theorem normalizer_local_preparation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (Tu T0 : Subgroup G)
    (hTu : Tu ≠ ⊥) (hTuT : Tu ≤ (T : Subgroup G))
    (hZ : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ Tu ≠ ⊥)
    (hT0T : T0 ≤ (T : Subgroup G))
    (hi : Tu.relIndex T0 = 2)
    (hSylow : Chapter1.IsSylowIn 2 T0 (normalizer (Tu : Set G)))
    (hnorm : (T : Subgroup G) ≤ normalizer (T0 : Set G))
    (hcontrol : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T0 →
      (T : Subgroup G) ≤ normalizer (C : Set G) →
        normalizer (Tu : Set G) ⊓ normalizer (C : Set G) = T0) :
    let I := normalizer (Tu : Set G)
    Group.IsSolvable I ∧ IsSQTK KnownSimple.IsKnownSimple I ∧
      generalizedFitting I = pCore 2 I ∧
      (T0.subgroupOf I).characteristicNormalizerClosure ≤ T0.subgroupOf I := by
  let I := normalizer (Tu : Set G)
  have hp := T.isPGroup'.to_le hTuT
  have hT0I := (Chapter1.isSylowIn_iff.mp hSylow).2.1
  obtain ⟨S,hS⟩ := hSylow
  have hSe : (S : Subgroup I) = T0.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hT0I]
    exact hS
  let U := Tu.subgroupOf I
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_refl I)
  have hu : IsPGroup 2 U := hp.comap_subtype
  have hui : U.relIndex (S : Subgroup I) = 2 := by
    rw [hSe,relIndex_subgroupOf hT0I]
    exact hi
  have hf : generalizedFitting I = pCore 2 I :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_3 T (hG.evenCharacteristic T) hTu hp hZ).2.2)
  exact ⟨solvable_of_normal_two_index S U hu hui,
    hG.twoLocal_sqtk ⟨Tu,hTu,hp,rfl⟩,hf,
    characteristic_control_of_normal_control T I T0 hT0I hT0T hnorm hcontrol⟩

theorem source_suitable_normalizer_preparation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G)) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    let T0 := suitableQuotientCentralizer h u
    let I := normalizer (Tu : Set G)
    Group.IsSolvable I ∧ IsSQTK KnownSimple.IsKnownSimple I ∧
      generalizedFitting I = pCore 2 I ∧
      (T0.subgroupOf I).characteristicNormalizerClosure ≤ T0.subgroupOf I ∧
      (T0 < I → ∀ W : Subgroup G, W ≠ ⊥ → W ≤ T0 → I ≤ normalizer (W : Set G) →
        (T : Subgroup G) ⊓ normalizer (W : Set G) = T0) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let T0 := suitableQuotientCentralizer h u
  let I := normalizer (Tu : Set G)
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct
  have hc := source_suitable_normalizer_control hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3
  have huT : u ∈ (T : Subgroup G) := h.QH_le_T (h.UH_le_QH hu)
  have hZTu : centralInvolutions T ≤ Tu := by
    intro z hz
    refine ⟨centralInvolutions_le_sylow T hz,?_⟩
    intro v hv
    have hvu : v = u := Set.mem_singleton_iff.mp hv
    subst v
    exact centralInvolutions_le_centralizer_sylow T hz u huT
  have hZcenter : centralInvolutions T ≤ (center (T : Subgroup G)).map (T : Subgroup G).subtype := by
    rintro z ⟨z₀,⟨z₁,hz₁,rfl⟩,rfl⟩
    exact ⟨z₁,z₁.property,rfl⟩
  have hZne : centralInvolutions T ≠ ⊥ := by
    intro he
    have hh := plane_centralInvolutions_card T M hM.1.2 hcard e
    rw [he,card_bot] at hh
    omega
  have hTu : Tu ≠ ⊥ := fun he => hZne (bot_unique (hZTu.trans_eq he))
  have hZ : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ Tu ≠ ⊥ :=
    fun he => hZne (bot_unique ((le_inf hZcenter hZTu).trans_eq he))
  have hT0T : T0 ≤ (T : Subgroup G) := inf_le_left
  have hn : (T : Subgroup G) ≤ normalizer (T0 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hT0T).mp (normal_of_index_eq_two hindex)
  have hp := normalizer_local_preparation hG T Tu T0 hTu inf_le_left hZ hT0T hi.1 hc.2.2.1
    hn hc.2.2.2
  exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,fun hlt =>
    c6_control_of_normal_control T I T0 hlt hT0T hindex hc.2.2.2⟩

private theorem sylow_centralizer_of_normalizer
    (u : G) (T : Sylow 2 G) (Tu T0 H : Subgroup G)
    (hTuC : Tu ≤ centralizer ({u} : Set G))
    (hT0T : T0 ≤ (T : Subgroup G)) (hT0H : T0 ≤ H)
    (hN : normalizer (Tu : Set G) = T0)
    (hlocal : Chapter1.IsSylowIn 2 Tu (H ⊓ centralizer ({u} : Set G))) :
    Chapter1.IsSylowIn 2 Tu (centralizer ({u} : Set G)) := by
  let C := centralizer ({u} : Set G)
  have hp := (Chapter1.isSylowIn_iff.mp hlocal).1
  have hNC : C ⊓ normalizer (Tu : Set G) = Tu := by
    apply (Chapter1.isSylowIn_iff.mp hlocal).2.2
    · rw [hN]
      exact T.isPGroup'.to_le (inf_le_right.trans hT0T)
    · exact le_inf hTuC Tu.le_normalizer
    · rw [hN]
      exact le_inf (inf_le_right.trans hT0H) inf_le_left
  have hn : normalizer (Tu.subgroupOf C : Set C) = Tu.subgroupOf C := by
    rw [←subgroupOf_normalizer_eq hTuC]
    ext x
    change (x : G) ∈ normalizer (Tu : Set G) ↔ (x : G) ∈ Tu
    exact ⟨fun hx => hNC ▸ (show (x : G) ∈ C ⊓ normalizer (Tu : Set G) from
      ⟨x.property,hx⟩),fun hx => Tu.le_normalizer hx⟩
  obtain ⟨S,hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq (Tu.subgroupOf C)
    hp.comap_subtype hn
  exact ⟨S,by rw [hS,map_subgroupOf_eq_of_le hTuC]⟩

private theorem not_twoCentral_of_proper_sylow_centralizer
    (u : G) (T : Sylow 2 G) (Tu : Subgroup G)
    (hTuT : Tu < (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 Tu (centralizer ({u} : Set G))) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({u} : Set G) := by
  rintro ⟨S,hSC⟩
  let C := centralizer ({u} : Set G)
  obtain ⟨R,hR⟩ := hSylow
  obtain ⟨P,hP⟩ := (S.isPGroup'.comap_subtype : IsPGroup 2
    ((S : Subgroup G).subgroupOf C)).exists_le_sylow
  have hbound : Nat.card T ≤ Nat.card Tu := calc
    Nat.card T = Nat.card S := by rw [T.card_eq_multiplicity,S.card_eq_multiplicity]
    _ = Nat.card ((S : Subgroup G).subgroupOf C) :=
      (Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv).symm
    _ ≤ Nat.card P := Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)
    _ = Nat.card R := by rw [P.card_eq_multiplicity,R.card_eq_multiplicity]
    _ = Nat.card Tu := by
      rw [←hR]
      exact (card_map_of_injective C.subtype_injective).symm
  exact hTuT.ne (eq_of_le_of_card_ge hTuT.le hbound)
private theorem c6_cubic_normal_two_abelian
    (I T Tu : Subgroup G) (d : ChapterC.Section06.Original.Input I T)
    (hK : ChapterC.IsAlternatingBlock (pResidual 2 I) 3)
    (hp : IsPGroup 2 Tu) (hUI : Tu ≤ I) (hn : I ≤ normalizer (Tu : Set G)) :
    IsMulCommutative Tu := by
  have hKa : ChapterC.IsAlternatingBlock ((pResidual 2 I).map I.subtype) 3 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      ((pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective) hK
  have hm : Nonempty (I ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (I ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
    rcases (d.cubic_rank_and_family hKa).2.2 with ha | hb
    · exact Or.inr ha.2
    · exact Or.inl hb.1
  let : IsElementaryAbelian 2 (pCore 2 I) := (symmetric_four_model_twoCore_data hm).1
  let : IsMulCommutative (I.pCoreIn 2) :=
    inferInstanceAs (IsMulCommutative ((pCore 2 I).map I.subtype))
  have hle : Tu ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes hp hUI hn
  exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hle ha) (hle hb)
theorem source_lemma_14_6_3_4
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G))) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    normalizer (Tu : Set G) = suitableQuotientCentralizer h u ∧
      Chapter1.IsSylowIn 2 Tu (centralizer ({u} : Set G)) ∧
      ¬∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({u} : Set G) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let T0 := suitableQuotientCentralizer h u
  let I := normalizer (Tu : Set G)
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct
  have hc := source_suitable_normalizer_control hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3
  have hp := source_suitable_normalizer_preparation hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3
  have hn := source_suitable_core_and_residual hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hT0T : T0 ≤ (T : Subgroup G) := inf_le_left
  have hT0I : T0 ≤ I := (Chapter1.isSylowIn_iff.mp hc.2.2.1).2.1
  have hproper : T0 < (T : Subgroup G) := lt_of_le_of_ne hT0T (by
    intro he
    have hii := hindex
    change T0.relIndex (T : Subgroup G) = 2 at hii
    rw [he,relIndex_self] at hii
    omega)
  have heq : I = T0 := by
    apply le_antisymm _ hT0I
    by_contra hnot
    have hlt : T0 < I := lt_of_le_not_ge hT0I hnot
    obtain ⟨S,hS⟩ := hc.2.2.1
    have hSe : (S : Subgroup I) = T0.subgroupOf I := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le hT0I]
      exact hS
    let U := Tu.subgroupOf I
    let : U.Normal := normal_subgroupOf_of_le_normalizer (le_refl I)
    have hU : IsPGroup 2 U := (T.isPGroup'.to_le (show Tu ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    have hUS : U ≤ (S : Subgroup I) := by
      rw [hSe]
      exact comap_mono (le_sup_right.trans hi.2.2.2.1.ge)
    have hUindex : U.relIndex (S : Subgroup I) = 2 := by
      rw [hSe,relIndex_subgroupOf hT0I]
      exact hi.1
    have hSproper : (S : Subgroup I) ≠ ⊤ := by
      intro hh
      apply hlt.ne
      calc
        T0 = (S : Subgroup I).map I.subtype := hS.symm
        _ = I := by rw [hh, ←MonoidHom.range_eq_map, I.range_subtype]
    have hcpu : (S : Subgroup I).characteristicNormalizerClosure ≤ (S : Subgroup I) := by
      rw [hSe]
      exact hp.2.2.2.1
    have hclass := SuitableSmallQuotient.small_quotient_and_residual hp.1 hp.2.1 hp.2.2.1 S U
      hU hUS hUindex hSproper hcpu
    have hq := hclass.2.2
    have hK := hclass.2.1
    let d : ChapterC.Section06.Original.Input I (T : Subgroup G) := {
      fitting := hp.2.2.1
      models := Or.inr (Or.inl hq)
      two := T.isPGroup'
      sylow := S
      intersection := hS.trans hi.2.2.2.2.symm
      proper := hi.2.2.2.2 ▸ hproper
      control := by
        rw [hi.2.2.2.2]
        exact hp.2.2.2.2 hlt }
    exact hn.2.2.2.2 (c6_cubic_normal_two_abelian I (T : Subgroup G) Tu d hK
      (T.isPGroup'.to_le inf_le_left) Tu.le_normalizer le_rfl)
  have hs := sylow_centralizer_of_normalizer u T Tu T0 H inf_le_right hT0T
    (hT0T.trans h.T_le_H) heq hlocal
  refine ⟨heq,hs,not_twoCentral_of_proper_sylow_centralizer u T Tu ?_ hs⟩
  exact lt_of_le_of_ne inf_le_left (by
    intro he
    have hii : Tu.relIndex (T : Subgroup G) = 4 := hi.2.1
    rw [he,relIndex_self] at hii
    omega)

end CFSG.Quasithin.Chapter14.Section06
