module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.Source
public import Theory.Representation.FixedSpaceCodimension
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.PermutationFusion

/-!
# Actual elementary actors for the degree-twenty HS calculation

Conjugation on the specified central quotient is faithful on elementary
actors. An involution induces an inner automorphism exactly when it belongs
to the generalized Fitting subgroup. Thus inner actors have rank at most four,
and intersection with that subgroup loses at most one rank. In particular,
every actor of rank at least two contains an inner involution. Outer
involutions are marked by the two actual degree-100 normalizer representatives;
no identification of a representation with a matrix model is assumed.

These are group and fixed-space reductions for Guralnick--Malle,
*Classification of 2F-modules, I*, Proposition 5.1, HS paragraph, preprint
pp.16--17, and Aschbacher--Smith K.4, printed p.457. The degree-twenty
representation estimates remain explicit in the conditional assembly below.
In GM's labels the elementary-centralizer representative is 2D and the
symmetric-centralizer representative is 2C.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

namespace Twenty

abbrev HS := KnownSimple.SporadicName.hs.Carrier

/-- The literal conjugation action on the specified HS central quotient. -/
noncomputable def quotientAction
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) :
    G →* MulAut HS :=
  (MulAut.centralQuotientAction e).comp MulAut.conjNormal

/-- Conjugation on the actual HS quotient loses no elementary actor. -/
theorem quotientAction_injective_on_elementary (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Function.Injective ((quotientAction e).comp A.subtype) := by
  let := h.quasisimple
  let := h.irreducible
  have hn : A ≤ normalizer (generalizedFitting G : Set G) := by
    rw [normalizer_eq_top]
    exact le_top
  have hc := Representation.BinaryIrreducibleCentralizer.elementary_conjugation_injective
    ρ (generalizedFitting G) h.faithful A hn
  have he : ((quotientAction e).comp A.subtype) =
      (MulAut.centralQuotientAction e).comp
        ((generalizedFitting G).normalizerMonoidHom.comp (inclusion hn)) := by
    ext a x
    rfl
  rw [he]
  exact (MulAut.centralQuotientAction_injective e).comp hc

/-- Innerness on the quotient detects actual membership for involutions,
even before eliminating the center of the covering group. -/
theorem quotientAction_inner_iff (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    {t : G} (ht : t ^ 2 = 1) :
    (∃ x : HS, quotientAction e t = MulAut.conj x) ↔ t ∈ generalizedFitting G := by
  let := h.quasisimple
  let := h.irreducible
  constructor
  · intro hi
    have hi' := (MulAut.centralQuotientAction_inner_iff e (MulAut.conjNormal t)).mp hi
    have hn : t ∈ normalizer (generalizedFitting G : Set G) := by
      rw [normalizer_eq_top]
      trivial
    apply involution_mem_of_inner ρ (generalizedFitting G) h.faithful ⟨t, hn⟩ ht
    exact hi'
  · intro htL
    let x : generalizedFitting G := ⟨t, htL⟩
    refine ⟨e (QuotientGroup.mk' _ x), ?_⟩
    change MulAut.centralQuotientAction e (MulAut.conjNormal (x : G)) = _
    rw [MulAut.conjNormal_val, MulAut.centralQuotientAction_conj]

/-- An elementary actor contained in the component has rank at most four. -/
theorem inner_rank_le_four (h : SourceHypotheses ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G) :
    rank A ≤ 4 := by
  let := hA.2
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  let : Finite HS := Finite.of_surjective e e.surjective
  let f : A →* HS := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (generalizedFitting G))).comp (inclusion hAL))
  have hconj : (MulAut.conj : HS →* MulAut HS).comp f =
      (quotientAction e).comp A.subtype := by
    apply MonoidHom.ext
    intro a
    change MulAut.conj (e (QuotientGroup.mk' _ (inclusion hAL a))) =
      MulAut.centralQuotientAction e (MulAut.conjNormal (a : G))
    rw [← MulAut.centralQuotientAction_conj]
    exact congrArg (MulAut.centralQuotientAction e)
      (MulAut.conjNormal_val (h := inclusion hAL a)).symm
  have hfi : Function.Injective f := by
    apply Function.Injective.of_comp (f := MulAut.conj)
    rw [← MonoidHom.coe_comp, hconj]
    exact quotientAction_injective_on_elementary h e A
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb := (primeRank_le_iff_elementary_card_le HS).mp
    _root_.Sporadic.LeechRelated.HS.twoRank_le_four f.range he
  have hc : Nat.card A ≤ 2 ^ 4 :=
    (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).le.trans hb
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

/-- Intersecting an elementary actor with the actual component loses at most
one binary dimension. This retains the literal intersection used in the S8 branch. -/
theorem rank_le_inner_rank_add_one (h : SourceHypotheses ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    rank A ≤ rank (A ⊓ generalizedFitting G) + 1 := by
  let := hA.2
  obtain ⟨e⟩ := h.centralQuotient
  let : Finite HS := Finite.of_surjective e e.surjective
  let f : A →* MulAut.Outer HS :=
    (QuotientGroup.mk' (MulAut.innerSubgroup HS)).comp ((quotientAction e).comp A.subtype)
  have hk (a : A) : a ∈ f.ker ↔ (a : G) ∈ generalizedFitting G := by
    change (QuotientGroup.mk' (MulAut.innerSubgroup HS)) (quotientAction e a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have he : quotientAction e (a : G) ∈ MulAut.innerSubgroup HS ↔
        ∃ x : HS, quotientAction e (a : G) = MulAut.conj x := by
      exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩
    rw [he, quotientAction_inner_iff h e (elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G) a.property)]
  let B := A ⊓ generalizedFitting G
  let ek : f.ker ≃* B := {
    toFun x := ⟨x.1, x.1.property, (hk x.1).mp x.2⟩
    invFun x := ⟨⟨x, x.2.1⟩, (hk ⟨x, x.2.1⟩).mpr x.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hcard : Nat.card A = Nat.card B * Nat.card f.range := by
    rw [← f.ker.card_mul_index, index_ker, Nat.card_congr ek.toEquiv]
  have ho : Nat.card f.range ≤ 2 :=
    (card_le_card_group f.range).trans
      (Nat.le_of_dvd (by decide) _root_.Sporadic.LeechRelated.HS.outer_card_dvd_two)
  have hBcard : Nat.card B = 2 ^ rank B := by
    by_cases hB : B = ⊥
    · simp [hB]
    · exact (hA.of_le inf_le_left hB).card_eq_two_pow_rank
  have hb : 2 ^ rank A ≤ 2 ^ (rank B + 1) := by
    rw [← hA.card_eq_two_pow_rank, hcard, pow_succ, ← hBcard]
    exact Nat.mul_le_mul_left _ ho
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

/-- The outer quotient has order at most two, so a rank-two actor already
contains a nonidentity involution of the actual component. -/
theorem exists_inner_involution (h : SourceHypotheses ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : 2 ≤ rank A) :
    ∃ t : G, t ∈ A ∧ t ∈ generalizedFitting G ∧ t ≠ 1 ∧ t ^ 2 = 1 := by
  let := hA.2
  have hb := rank_le_inner_rank_add_one h hA
  have hne : A ⊓ generalizedFitting G ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hb
    omega
  obtain ⟨t, ht, ht1⟩ := (A ⊓ generalizedFitting G).bot_or_exists_ne_one.resolve_left hne
  exact ⟨t, ht.1, ht.2, ht1, elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht.1⟩

open Chapter16.OtherPreliminaries.JankoTwoHigmanSims in
/-- GM's outer 2D class, marked by its actual elementary-centralizer representative. -/
def IsElementaryOuter
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) (t : G) : Prop :=
  IsConj (_root_.Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
    HSOuter.elementaryNormalizer) (quotientAction e t)

open Chapter16.OtherPreliminaries.JankoTwoHigmanSims in
/-- GM's outer 2C class, marked by its actual symmetric-centralizer representative. -/
def IsSymmetricOuter
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) (t : G) : Prop :=
  IsConj (_root_.Sporadic.LeechRelated.HS.generated.normalizerMonoidHom
    HSOuter.symmetricNormalizer) (quotientAction e t)

open Chapter16.OtherPreliminaries.JankoTwoHigmanSims in
/-- The actual quotient action of every outer involution belongs to one of
the two marked classes. This does not assert any module identification. -/
theorem outer_involution_cases (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    {t : G} (ht : t ^ 2 = 1) (hout : t ∉ generalizedFitting G) :
    IsElementaryOuter e t ∨ IsSymmetricOuter e t := by
  have hi : ¬ ∃ x : HS, quotientAction e t = MulAut.conj x :=
    fun hinner => hout ((quotientAction_inner_iff h e ht).mp hinner)
  have hne : quotientAction e t ≠ 1 := by
    intro he
    exact hi ⟨1, by simpa using he⟩
  have horder : orderOf (quotientAction e t) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, ht, map_one]) hne
  obtain ⟨n, hn, hnorder, hnout⟩ := HSOuter.outer_involution_lift _ horder hi
  rcases HSOuter.outer_involution_permutation_fusion n hnorder hnout with hE | hS
  · obtain ⟨g, hg⟩ := hE
    have hc : IsConj HSOuter.elementaryNormalizer n := by
      apply isConj_iff.mpr
      exact ⟨g, Subtype.ext hg.symm⟩
    apply Or.inl
    change IsConj _ (quotientAction e t)
    rw [← hn]
    exact _root_.Sporadic.LeechRelated.HS.generated.normalizerMonoidHom.map_isConj hc
  · obtain ⟨g, hg⟩ := hS
    have hc : IsConj HSOuter.symmetricNormalizer n := by
      apply isConj_iff.mpr
      exact ⟨g, Subtype.ext hg.symm⟩
    apply Or.inr
    change IsConj _ (quotientAction e t)
    rw [← hn]
    exact _root_.Sporadic.LeechRelated.HS.generated.normalizerMonoidHom.map_isConj hc

variable [FiniteDimensional (ZMod 2) V]

/-- The two inner module calculations, without repeating the rank reduction.
The rank-four clause is the central-core/S5 argument, including the exclusion
of the 2B class by its displacement ten. These are pending representation inputs. -/
structure InnerEstimates (ρ : Representation (ZMod 2) G V) : Prop where
  involution : ∀ t : G, t ∈ generalizedFitting G → t ≠ 1 → t ^ 2 = 1 →
    8 ≤ fixedCodim ρ (zpowers t)
  rank_four : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ generalizedFitting G →
    rank A = 4 → 9 ≤ fixedCodim ρ A

/-- The elementary-centralizer outer class moves ten dimensions. Only the
rank-five actors require the additional centralizer argument. -/
structure ElementaryOuterEstimates (ρ : Representation (ZMod 2) G V)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) : Prop where
  involution : ∀ t : G, t ^ 2 = 1 → IsElementaryOuter e t →
    10 ≤ fixedCodim ρ (zpowers t)
  rank_five : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 5 →
    ∀ t ∈ A, IsElementaryOuter e t → 11 ≤ fixedCodim ρ A

/-- The three bounds supplied by the 6,6,8 restriction at the actual
symmetric outer centralizer. They refer to the original action on V. -/
structure SymmetricOuterEstimates (ρ : Representation (ZMod 2) G V)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS) : Prop where
  involution : ∀ t : G, t ^ 2 = 1 → IsSymmetricOuter e t →
    6 ≤ fixedCodim ρ (zpowers t)
  rank_four : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 4 →
    ∀ t ∈ A, IsSymmetricOuter e t → 10 ≤ fixedCodim ρ A
  rank_five : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 5 →
    ∀ t ∈ A, IsSymmetricOuter e t → 11 ≤ fixedCodim ρ A

omit [Finite G] in
private theorem codim_le_of_mem {A : Subgroup G} {t : G} (ht : t ∈ A) :
    fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A := by
  have hf := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hA := fixedCodim_add_finrank ρ A
  have ht' := fixedCodim_add_finrank ρ (zpowers t)
  omega

/-- The source inner calculation gives a strict ratio-two gap on every
inner elementary actor, using its proved rank-four bound. -/
theorem inner_gap_of_estimates (h : SourceHypotheses ρ) (hI : InnerEstimates ρ)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ generalizedFitting G) :
    2 * rank A < fixedCodim ρ A := by
  have hr := inner_rank_le_four h hA hAL
  by_cases hr4 : rank A = 4
  · have hd := hI.rank_four A hA hAL hr4
    omega
  · let := hA.2
    obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have hd := (hI.involution t (hAL ht) ht1
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht)).trans (codim_le_of_mem ht)
    omega

/-- All four source involution branches assemble on the original elementary
actor. The three module estimates are explicit undischarged inputs. -/
theorem gap_of_estimates (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hI : InnerEstimates ρ) (hE : ElementaryOuterEstimates ρ e)
    (hS : SymmetricOuterEstimates ρ e)
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim ρ A := by
  let := hA.2
  have hr := hA.rank_le_of_primeRank_le h.twoRank_le_five
  by_cases hAL : A ≤ generalizedFitting G
  · exact inner_gap_of_estimates h hI hA hAL
  · obtain ⟨t, ht, htL⟩ := Set.not_subset.mp hAL
    have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht
    rcases outer_involution_cases h e ht2 htL with htE | htS
    · by_cases hr5 : rank A = 5
      · have hd := hE.rank_five A hA hr5 t ht htE
        omega
      · have hd := (hE.involution t ht2 htE).trans (codim_le_of_mem ht)
        omega
    · by_cases hr5 : rank A = 5
      · have hd := hS.rank_five A hA hr5 t ht htS
        omega
      by_cases hr4 : rank A = 4
      · have hd := hS.rank_four A hA hr4 t ht htS
        omega
      by_cases hr2 : 2 ≤ rank A
      · obtain ⟨s, hs, hsL, hs1, hs2⟩ := exists_inner_involution h hA hr2
        have hd := (hI.involution s hsL hs1 hs2).trans (codim_le_of_mem hs)
        omega
      · have hd := (hS.involution t ht2 htS).trans (codim_le_of_mem ht)
        omega

/-- Application to the actual source consumer. Degree reduction and all three
local representation inputs still have to be supplied by their producers. -/
theorem not_cubicRatio_le_two_of_estimates (h : SourceHypotheses ρ)
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 5)
    (hdegree : Module.finrank (ZMod 2) V ≤ 50 → Module.finrank (ZMod 2) V = 20)
    (hI : Module.finrank (ZMod 2) V = 20 → InnerEstimates ρ)
    (hE : Module.finrank (ZMod 2) V = 20 → ElementaryOuterEstimates ρ e)
    (hS : Module.finrank (ZMod 2) V = 20 → SymmetricOuterEstimates ρ e) :
    ¬ cubicRatio ρ ≤ 2 :=
  h.not_cubicRatio_le_two_of_inputs hgen hdegree
    (fun hd => gap_of_estimates h e (hI hd) (hE hd) (hS hd))

/-- The subgroup generated by all conjugates of A inside the centralizer of t. -/
noncomputable def centralizerConjugateClosure (A : Subgroup G) (t : G) : Subgroup G :=
  ⨆ c : centralizer ({t} : Set G), A.map (MulAut.conj (c : G)).toMonoidHom

omit [Finite G] in
/-- Equality with the fixed space of t propagates to every centralizer conjugate.
This is the common-fixed-space step in GM's standard centralizer argument. -/
theorem fixedSpace_centralizerConjugateClosure {A : Subgroup G} {t : G}
    (ht : t ∈ A) (hd : fixedCodim ρ A = fixedCodim ρ (zpowers t)) :
    fixedSpace ρ (centralizerConjugateClosure A t) = fixedSpace ρ (zpowers t) := by
  have he (c : centralizer ({t} : Set G)) :
      fixedSpace ρ (A.map (MulAut.conj (c : G)).toMonoidHom) =
        fixedSpace ρ (zpowers t) := by
    apply fixedSpace_eq_of_fixedCodim_eq ρ
    · apply zpowers_le.mpr
      refine ⟨t, ht, ?_⟩
      change (c : G) * t * (c : G)⁻¹ = t
      rw [mem_centralizer_singleton_iff.mp c.property]
      simp only [mul_inv_cancel_right]
    · rw [fixedCodim_map_conj, hd]
  change Representation.invariants (ρ.comp (⨆ c : centralizer ({t} : Set G),
    A.map (MulAut.conj (c : G)).toMonoidHom).subtype) = _
  rw [Representation.invariants_comp_iSup ρ]
  change (⨅ c : centralizer ({t} : Set G),
    fixedSpace ρ (A.map (MulAut.conj (c : G)).toMonoidHom)) = _
  simp only [he, ciInf_const]

omit [Finite G] in
/-- A subgroup in the centralizer closure moving more than t forces the
whole actor to move strictly more than t. No normality in G is imposed. -/
theorem lt_fixedCodim_of_centralizerConjugateClosure {A K : Subgroup G} {t : G}
    (ht : t ∈ A) (hK : K ≤ centralizerConjugateClosure A t)
    (hd : fixedCodim ρ (zpowers t) < fixedCodim ρ K) :
    fixedCodim ρ (zpowers t) < fixedCodim ρ A := by
  have hAt := Submodule.finrank_mono
    (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hA := fixedCodim_add_finrank ρ A
  have ht' := fixedCodim_add_finrank ρ (zpowers t)
  by_contra hnot
  have he : fixedCodim ρ A = fixedCodim ρ (zpowers t) := by omega
  have hfix := fixedSpace_centralizerConjugateClosure ht he
  have hle : fixedSpace ρ (zpowers t) ≤ fixedSpace ρ K := by
    rw [← hfix]
    exact Representation.invariants_comp_subtype_antitone ρ hK
  have hh := Submodule.finrank_mono hle
  have hKd := fixedCodim_add_finrank ρ K
  omega

omit [Finite G] in
/-- The numerical form used by both source centralizer branches. -/
theorem lt_fixedCodim_of_centralizerConjugateClosure_bound
    {A K : Subgroup G} {t : G} {d : ℕ} (ht : t ∈ A)
    (hK : K ≤ centralizerConjugateClosure A t)
    (htd : d ≤ fixedCodim ρ (zpowers t)) (hKd : d < fixedCodim ρ K) :
    d < fixedCodim ρ A := by
  by_cases hd : d < fixedCodim ρ (zpowers t)
  · exact hd.trans_le (codim_le_of_mem ht)
  · have he : fixedCodim ρ (zpowers t) = d := by omega
    have hh := lt_fixedCodim_of_centralizerConjugateClosure ht hK (he ▸ hKd)
    simpa only [he] using hh

omit [Finite G] in
/-- Application of the common-fixed-space argument to the source inner
rank-four actor. The producer must construct K in this literal closure. -/
theorem inner_rank_four_bound_of_closure
    (hI : ∀ t : G, t ∈ generalizedFitting G → t ≠ 1 → t ^ 2 = 1 →
      8 ≤ fixedCodim ρ (zpowers t))
    {A K : Subgroup G} {t : G} (ht : t ∈ A)
    (htL : t ∈ generalizedFitting G) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hK : K ≤ centralizerConjugateClosure A t) (hKd : 8 < fixedCodim ρ K) :
    9 ≤ fixedCodim ρ A := by
  exact lt_fixedCodim_of_centralizerConjugateClosure_bound ht hK
    (hI t htL ht1 ht2) hKd

/-- Application to the source E16.S5 outer centralizer, using displacement
ten and a genuinely embedded subgroup of its conjugate closure. -/
theorem elementary_outer_rank_five_bound_of_closure
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* HS)
    (hE : ∀ t : G, t ^ 2 = 1 → IsElementaryOuter e t →
      10 ≤ fixedCodim ρ (zpowers t))
    {A K : Subgroup G} {t : G} (ht : t ∈ A) (ht2 : t ^ 2 = 1)
    (htE : IsElementaryOuter e t) (hK : K ≤ centralizerConjugateClosure A t)
    (hKd : 10 < fixedCodim ρ K) : 11 ≤ fixedCodim ρ A := by
  exact lt_fixedCodim_of_centralizerConjugateClosure_bound ht hK
    (hE t ht2 htE) hKd

end Twenty
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
