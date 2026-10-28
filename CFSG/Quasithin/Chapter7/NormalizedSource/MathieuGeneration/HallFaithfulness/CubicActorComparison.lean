module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.OddActorComparison
public import Theory.SpecificGroups.Janko4.Model.MathieuCubicFixers

/-!
# The cubic exceptional section in the original Mathieu odd-actor comparison

The model sieve also applies to an actor of order three. In M23 and M24,
a fixed M22 section supplies an element of order eleven commuting with
the actor, contradicting the native odd-order spectrum. The fixed-section
index argument excludes HS, and the full residual-image two-core and
self-dual degree bounds exclude the exceptional rank-two models.
Consequently a nontrivial cubic action occurs only on the actual J4 simple
section of the original containing C-component.

The literal Hall application retains the full original covering component,
fixed involution, M22 residual and its inclusion in the ambient component.
Either the entire involution-centralizer residual lies in N_G(L), or its
ambient simple section is J4 and the full actor image has order three. The
exceptional replacement subgroup, M12/M22 pushing-up exclusions and the
Mathieu seed/fixed-line identification remain to be proved before this
reduction can imply SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith 4.4.3, printed p.623, applied in 4.4.14,
printed pp.624--625. The small-section and sporadic proofs are adapted from
Chapter4.Section04.OddLocalMathieu.Models at this narrow extension boundary;
the imported native model certificates retain their original attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu
open ChapterA.Section02 ClassificationModels Sporadic.Mathieu

private theorem section_card_dvd {S : Type*} [Group S]
    (h : IsSectionOf M22 S) : 443520 ∣ Nat.card S := by
  obtain ⟨B,f,hf⟩ := h
  rw [←m22_order]
  exact (card_dvd_of_surjective f hf).trans B.card_subgroup_dvd_card

variable {S : Type*} [Group S]

private theorem not_alternating_section (h : IsSectionOf M22 S)
    {n : ℕ} (hn : n ≤ 9) (e : S ≃* alternatingGroup (Fin n)) : False := by
  have hd : 11 ∣ Nat.card S := (by decide : 11 ∣ 443520).trans (section_card_dvd h)
  rw [Nat.card_congr e.toEquiv] at hd
  have hh := (alternatingGroup (Fin n)).card_subgroup_dvd_card
  rw [Nat.card_perm,Nat.card_fin] at hh
  have hbad := hd.trans (hh.trans (Nat.factorial_dvd_factorial hn))
  norm_num [Nat.factorial] at hbad

private theorem not_binary_linear_section (h : IsSectionOf M22 S)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL S n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let a := e.trans (Atlas.fieldEquivPSL n ef)
  have hd : 11 ∣ Nat.card S := (by decide : 11 ∣ 443520).trans (section_card_dvd h)
  rw [Nat.card_congr a.toEquiv] at hd
  have hs := hd.trans (card_quotient_dvd_card (center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))))
  have hgl := hs.trans (card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective)
  rcases hn with rfl | rfl
  all_goals
    rw [Matrix.card_GL_field,ZMod.card] at hgl
    norm_num [Fin.prod_univ_succ] at hgl

private theorem not_fixed_section_of_mathieu_embedding
    {S : Type*} [Group S] [Finite S] (hz : center S = ⊥)
    (hi : Function.Surjective (MulAut.conj : S →* MulAut S))
    (j : S →* M24) (hj : Function.Injective j)
    {p : ℕ} (hp : p.Prime) (hpgt : 2 < p) : ¬ HasMathieuFixedSection S p := by
  rintro ⟨a,ha,hs⟩
  obtain ⟨x,rfl⟩ := hi a
  have hxo : orderOf x = p :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) x).symm.trans ha
  obtain ⟨q,hq,hqd,hneq,hoq,hlarge⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ 443520 ∧
      p ≠ q ∧ Odd q ∧ 21 < p * q := by
    by_cases he : p = 11
    · exact ⟨5,by decide,by decide,by omega,by decide,by omega⟩
    · exact ⟨11,by decide,by decide,he,by decide,by omega⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' q (hqd.trans (section_card_dvd hs))
  have hyc : x * (y : S) = (y : S) * x := by
    have hh := (MulAut.mem_fixedSubgroup _ _).mp y.property
    change x * (y : S) * x⁻¹ = y at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hyord : orderOf (y : S) = q := (orderOf_coe y).trans hy
  have hcop : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hneq (((Nat.dvd_prime hq).mp hd).resolve_left hp.ne_one))
  have hxy : orderOf (j (x * y)) = p * q := by
    rw [orderOf_injective j hj]
    exact (Commute.orderOf_mul_eq_mul_orderOf_of_coprime hyc
      (by rw [hxo,hyord]; exact hcop)).trans (by rw [hxo,hyord])
  have ho : Odd (p*q) := (hp.odd_of_ne_two (by omega)).mul hoq
  rcases M24OddCyclic.oddOrderSpectrum (j (x * y))
    (by rw [hxy]; exact ho.not_two_dvd_nat) with hh | hh | hh | hh
  · omega
  · rw [hxy] at hh
    exact Nat.not_prime_mul hp.ne_one hq.ne_one hh
  · omega
  · omega

/-- Prime-order odd automorphisms of M₂₃ cannot fix an M₂₂ section. -/
private theorem no_mathieu_cubic_fixed_m23 {p : ℕ} (hp : p.Prime) (hgt : 2 < p) :
    ¬ HasMathieuFixedSection M23 p := by
  let j : M23 →* M24 := (MulAction.stabilizer M24 (24 : Fin 24)).subtype.comp
    m23ToM24PointStabilizer
  exact not_fixed_section_of_mathieu_embedding M23Geometry.m23_center_eq_bot
    m23_conj_surjective j (Subtype.val_injective.comp m23ToM24PointStabilizer_injective) hp hgt

/-- The same native odd-order spectrum excludes M₂₄. -/
private theorem no_mathieu_cubic_fixed_m24 {p : ℕ} (hp : p.Prime) (hgt : 2 < p) :
    ¬ HasMathieuFixedSection M24 p :=
  not_fixed_section_of_mathieu_embedding M24InvolutionCentralizers.center_eq_bot
    M24OuterRestriction.conj_surjective (MonoidHom.id _) Function.injective_id hp hgt

open Sporadic.LeechRelated.HS
/-- An odd-prime automorphism of HS fixing an M₂₂ section would centralize
a conjugate of the concrete point stabilizer, whose centralizer is trivial. -/
private theorem no_mathieu_cubic_fixed_hs {p : ℕ} (hp : p.Prime) (hgt : 2 < p) :
    ¬ HasMathieuFixedSection Carrier p := by
  rintro ⟨a,ha,hsec⟩
  have houter := outer_isPGroup_two_of_pointStabilizer_map pointStabilizer_map
    normalizer_relIndex_dvd_two_pow
  have hin : a ∈ MulAut.innerSubgroup Carrier := by
    apply (QuotientGroup.eq_one_iff a).mp
    let q := QuotientGroup.mk' (MulAut.innerSubgroup Carrier)
    obtain ⟨n,hn⟩ := houter (q a)
    have hq : (q a)^p = 1 := by rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_left.mpr (hp.odd_of_ne_two (by omega))).pow_left n)
      (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hq)
  obtain ⟨x,rfl⟩ := hin
  let C := (MulAut.conj x).fixedSubgroup
  have hdiv : 443520 ∣ Nat.card C := by
    obtain ⟨U,f,hf⟩ := hsec
    rw [←Sporadic.Mathieu.m22_order]
    exact (card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card
  have hi : C.index ∣ 100 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 443520)).mp
    have hh := Nat.mul_dvd_mul_right hdiv C.index
    rw [C.card_mul_index,NormalizerIndex.card_carrier] at hh
    exact hh
  let : MulAction pointStabilizer (Carrier ⧸ C) :=
    MulAction.compHom (Carrier ⧸ C) pointStabilizer.subtype
  obtain ⟨z,hz⟩ := MulAction.exists_fixedPoint_of_smallMaximalIndex_dvd
    (G := pointStabilizer) (X := Carrier ⧸ C) (d := 11)
    (fun U hU hsize => SmallIndex.pointStabilizer_smallMaximalIndex U hU
      (hsize.trans (Nat.le_of_dvd (by decide) hi)))
    (fun hd => (by decide : ¬11 ∣ 100) (hd.trans hi))
  obtain ⟨g,rfl⟩ := Quotient.exists_rep z
  have hcentral : g * x * g⁻¹ ∈ centralizer (pointStabilizer : Set Carrier) := by
    intro y hy
    have hfix := hz ⟨y,hy⟩
    change (QuotientGroup.mk (y*g) : Carrier ⧸ C) = QuotientGroup.mk g at hfix
    have hm : g⁻¹*y*g ∈ C := by
      simpa only [mul_assoc] using (QuotientGroup.eq.mp hfix.symm)
    have hh := (MulAut.mem_fixedSubgroup _ _).mp hm
    change x*(g⁻¹*y*g)*x⁻¹ = g⁻¹*y*g at hh
    have he := mul_inv_eq_iff_eq_mul.mp hh
    have he' := congrArg (fun z : Carrier => g*z*g⁻¹) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using he'.symm
  rw [PointCentralizer.centralizer_pointStabilizer_eq_bot] at hcentral
  have hx : x = 1 := (MulAut.conj g).injective ((mem_bot.mp hcentral).trans (map_one _).symm)
  rw [hx,map_one,orderOf_one] at ha
  omega
private theorem sporadic_remaining {S : Type*} [Group S] {p : ℕ} (hp : 1 < p)
    (h : HasMathieuFixedSection S p) (hm : IsTheoremCSporadicModel S) :
    Nonempty (S ≃* M23) ∨ Nonempty (S ≃* M24) ∨
    Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨ Nonempty (S ≃* Janko4.Model) := by
  have hd := h.card_dvd
  rcases hm with ⟨name,hn,⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card M11 at hd
      rw [m11_order] at hd
      norm_num at hd
    | m12 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card M12 at hd
      rw [m12_order] at hd
      norm_num at hd
    | m22 => exact (no_mathieu_self_fixed_section hp (h.of_mulEquiv e)).elim
    | m23 => exact Or.inl ⟨e⟩
    | m24 => exact Or.inr (Or.inl ⟨e⟩)
    | hs => exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    | j4 => exact Or.inr (Or.inr (Or.inr ⟨e⟩))
    | j2 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
      norm_num at hd
    | j3 => exact (hn rfl).elim
    | he =>
      rw [Nat.card_congr e.toEquiv] at hd
      have hh := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound
        Held.NormalizerGraph.Orbital.held_le_preservingGroup
        (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd
          Held.NormalizerGraph.Orbital.held_le_preservingGroup)
      have hb := hd.trans hh
      norm_num at hb
    | ru =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 443520 ∣ Nat.card Rudvalis.Model at hd
      rw [Rudvalis.model_card] at hd
      norm_num at hd
  · rw [Nat.card_congr e.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd

/-- In the cubic comparison the full Mathieu seed forces the actual J4
simple section; its two-core is retained throughout the model sieve. -/
theorem cubic_mathieu_fixed_seed_is_janko
    {P S : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : IsTheoremCModel S)
    (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22)
    (a : MulAut S) (ha : orderOf a = 3) (hfix : f.range ≤ a.fixedSubgroup) :
    Nonempty (S ≃* Janko4.Model) := by
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h : HasMathieuFixedSection S 3 := ⟨a,ha,
    (IsSectionOf.of_surjective g hg).ambient_injective
      (inclusion hfix) (inclusion_injective hfix)⟩
  have hr : RemainingOddLocalModel S := by
    cases hm with
    | alternating n hn iso =>
      exact (not_alternating_section h.section (by omega) iso.some).elim
    | odd hm => exact (h.not_odd hm).elim
    | bender hm => exact (not_bender_section h.section hm).elim
    | rank_two n hm => exact Or.inl (h.rank_two_rows hm)
    | linear_binary n hn hm => exact (not_binary_linear_section h.section hn hm).elim
    | sporadic hm =>
      rcases sporadic_remaining (by decide) h hm with he | he | hs | hj
      · exact (no_mathieu_cubic_fixed_m23 (by decide) (by decide) (h.of_mulEquiv he.some)).elim
      · exact (no_mathieu_cubic_fixed_m24 (by decide) (by decide) (h.of_mulEquiv he.some)).elim
      · exact (no_mathieu_cubic_fixed_hs (by decide) (by decide) (h.of_mulEquiv hs.some)).elim
      · exact Or.inr hj
  rcases hr with hr | hj
  · obtain ⟨_,hqs,⟨ez⟩⟩ := rank_two_seed_quasisimple hr f hne e
    let := hqs
    obtain ⟨m,hm,⟨er⟩⟩ := rank_two_mathieu_cover_is_ree hr f.range ez
    exact (M22LocalSections.no_embedding_ree g hg hm
      (er.toMonoidHom.comp f.range.subtype) (er.injective.comp f.range.subtype_injective)).elim
  · exact hj

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

include D in
/-- On the original full component, failure of the odd-actor comparison
forces a cubic acting nontrivially on an actual J4 simple section. -/
theorem sourceOrbit_mathieu_oddActor_comparison_or_cubic_janko
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L)
    (z : G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hAz : A ≤ centralizer ({z} : Set G))
    (P : Subgroup (centralizer ({z} : Set G) ⊓ centralizer (A : Set G) : Subgroup G))
    (hP : P.IsCComponent)
    (eP : (P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22)
    (Q : Subgroup (centralizer ({z} : Set G))) [Q.Normal]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hPQ : P.map (inclusion inf_le_left) ≤ Q) :
    Q.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G) ∨
      (p = 3 ∧ Nonempty (SimpleSection Q ≃* Janko4.Model) ∧
        ∃ x : A, orderOf (simpleAction Q (⟨x,hAz x.property⟩ : centralizer ({z} : Set G))) = 3 ∧
          Nat.card ((simpleAction Q).comp (inclusion hAz)).range = 3) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let C := centralizer ({z} : Set G)
  let E := C ⊓ centralizer (A : Set G)
  let Qg := Q.map C.subtype
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers z,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hz).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers z) = 2^1 by rw [Nat.card_zpowers,hz]; rfl)
  have hE : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show E ≤ C from inf_le_left))).mp
      (hC.subgroup (E.subgroupOf C))
  let := hP.perfect
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hP.ne_bot
  let : IsQuasisimple (P ⧸ pCore 2 P) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hE hP
      (mathieu_radical_three_rank eP)
  let j := seedInclusion inf_le_left hPQ
  let f := (projection Q).comp j
  obtain ⟨hfn,_,⟨e⟩⟩ := seed_image j (seedInclusion_injective inf_le_left hPQ) eP
  by_cases htriv : ∀ x : A, simpleAction Q (⟨x,hAz x.property⟩ : C) = 1
  · left
    have hc : ⁅A.subgroupOf C,Q⁆ ≤ Q.pCoreIn 2 :=
      commutator_le_of_trivial_simpleAction Q (A.subgroupOf C)
        (fun x => htriv ⟨x,x.property⟩)
    have hcG := map_mono (f := C.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hAz,
      ←AmalgamLocalCores.pCoreIn_map_of_injective 2 C.subtype C.subtype_injective] at hcG
    have hCQ : C ≤ normalizer (Qg : Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        Q.le_normalizer_map C.subtype
    have ho : Odd (Nat.card A) := by
      obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
      rw [hn]
      exact ho.pow
    exact D.sourceOrbit_oddActor_comparison h A hne hA ho Qg (hTz.trans hCQ)
      ((le_sectionCentralizer_iff _ _).mpr ⟨hAz.trans hCQ,hcG⟩)

  · right
    push Not at htriv
    obtain ⟨x,hx⟩ := htriv
    let a := simpleAction Q (⟨x,hAz x.property⟩ : C)
    have hap : a ^ p = 1 := by
      rw [←map_pow]
      have he : (⟨x,hAz x.property⟩ : C) ^ p = 1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
      rw [he,map_one]
    have ha : orderOf a = p := orderOf_eq_prime hap hx
    have hfixedAll (t : A) : f.range ≤ (simpleAction Q (⟨t,hAz t.property⟩ : C)).fixedSubgroup := by
      rintro _ ⟨y,rfl⟩
      rw [MulAut.mem_fixedSubgroup]
      change simpleAction Q (⟨t,hAz t.property⟩ : C) (projection Q (j y)) = projection Q (j y)
      rw [simpleAction_projection]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      change (t : G) * ((y : E) : G) * (t : G)⁻¹ = _
      rw [y.val.property.2 (t : G) t.property,mul_inv_cancel_right]
      rfl
    have hfixed := hfixedAll x
    have hp3 : p = 3 := by
      by_contra hn
      have hp2 := hp.two_le
      have hne2 : p ≠ 2 := fun hh => by rw [hh] at ho; norm_num at ho
      exact no_large_prime_mathieu_fixed_seed (simpleSection_model (hC.subgroup Q))
        f hfn e hp (by omega) a ha hfixed
    have hmodel := cubic_mathieu_fixed_seed_is_janko (simpleSection_model (hC.subgroup Q))
      f hfn e a (ha.trans hp3) hfixed
    let : IsElementaryAbelian 3 A := hp3 ▸ hAe
    let b := (simpleAction Q).comp (inclusion hAz)
    let g := e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
    have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hb := Janko4.MathieuCubicFixers.cubic_mathieu_actor_range_card hmodel.some f.range
      g hg b x (ha.trans hp3)
      (fun t u hu => (MulAut.mem_fixedSubgroup _ _).mp (hfixedAll t hu))
    exact ⟨hp3,hmodel,x,ha.trans hp3,hb⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The exceptional cubic action retains the full original component,
involution, residual inclusion and the actual ambient J4 simple section. -/
@[expose] def MathieuJankoCubicSectionCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃ Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ P.map (inclusion inf_le_left) ≤ Q ∧
              ∃ hn : Q.Normal, letI := hn
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              Nonempty (OddLocalMathieu.SimpleSection Q ≃* Janko4.Model) ∧
              ∃ hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                ∃ x : A, orderOf (OddLocalMathieu.simpleAction Q ⟨x,hAz x.property⟩) = 3 ∧
                  Nat.card ((OddLocalMathieu.simpleAction Q).comp (inclusion hAz)).range = 3

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Apply the comparison to the actual seed, with every original residual
map retained also in the exceptional cubic J4 branch. -/
theorem sourceOrbit_mathieu_janko_comparison_or_cubic_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L) (hAV : A ≤ centralizer (V : Set G))
    (hc : MathieuJankoSeedResidualCase (T : Subgroup G) L V A
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
      (p = 3 ∧ MathieuJankoCubicSectionCase (T : Subgroup G) L V A) := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hAk,hseed,
    z,hzV,hz,hTz,hres,heR,P,hP,hPn,⟨eP⟩,hPm,Q,hQ,hunique⟩ := hc
  let := hQ.2.2.1
  let := hQ.2.2.2
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ hzV).symm
  have hQM := D.sourceOrbit_mathieu_oddActor_comparison_or_cubic_janko h hp ho A hne hAe hA
    _ hzG hTz hAz P hP eP Q hQ.2.1
  rcases hQM with hQM | ⟨hp3,hmodel,x,hx⟩
  · left
    refine ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,?_⟩
    rw [←hPm]
    have hh := map_mono (f := (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype)
      hQ.2.1
    rw [map_map,subtype_comp_inclusion] at hh
    exact hh.trans hQM
  · exact .inr ⟨hp3,K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
      P,hP,hPn,⟨eP⟩,hPm,Q,hQ.1,hQ.2.1,hQ.2.2.1,hQ.2.2.2,hmodel,hAz,x,hx⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall actor's exceptional action is cubic on an actual J4
simple section of its original involution-centralizer component; the whole
actor image there has order three. -/
theorem sourceOrbit_mathieu_hall_cubic_section
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
            (p = 3 ∧ MathieuJankoCubicSectionCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_small_pushingUp G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  have hp := hA.1
  have ho := hA.2.1
  have hne := hA.2.2.1
  have he := hA.2.2.2.1
  have hAC := hA.2.2.2.2.2.1
  have hAV := hA.2.2.2.2.2.2.1
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  refine ⟨hc.1,hc.2,?_⟩
  exact D.sourceOrbit_mathieu_janko_comparison_or_cubic_section h.toHypothesis1221
    hp ho A hne he hAC hAV hc.2
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
