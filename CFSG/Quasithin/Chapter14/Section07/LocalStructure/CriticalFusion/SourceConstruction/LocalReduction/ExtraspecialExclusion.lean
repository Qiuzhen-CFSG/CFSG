module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourTI
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupAction.FourthPowerFixed
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes

/-!
# Eliminating the original extraspecial residual by weak closure

For the actual central TI subgroup D of order four, every conjugate A lying
in R₁ centralizes U. If A meets U trivially, TI makes all its nonidentity
actors have the same fixed space. The fourth-power fixed-space calculation
makes a moving A elementary. The two-rank bound on R₁* gives a nonidentity
core actor, whose fixed hyperplane is then fixed by all of A. The faithful
extraspecial quotient has no such small actors, so A lies in O₂(H). Its
faithful commutator row would inject four elements into V₁, a contradiction.

If A meets U nontrivially and moves U, TI makes U normalize A. The common
commutator has order at most two, so the same displacement estimate puts A
in O₂(H), and [A,U] = V₁. Since D contains V₁, TI identifies A with D,
which centralizes U because D lies in Z(K) and U lies in K.

Consequently the literal W₀(R₁,D) lies in both O₂(LT) and O₂(H). It is
normal in LT and H and is nontrivial. The unique maximal two-local over LT
therefore contains H, contradicting the original escape property. Both the
K/O₂(K) and O²(H/O₂(H)) formulations use their actual residual comparison.
No source Data or extra local-recognition premise is assumed. The subsequent
solvable-local and component reductions through 14.7.52 remain separate.

Source: Aschbacher–Smith, conclusion of the proof of 14.7.14,
printed p.1054, following 14.7.26; refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem ti_fixed_commutator (A U : Subgroup G) (hTI : IsTISubgroup A)
    (hAU : A ≤ normalizer (U : Set G)) {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    ⁅U ⊓ centralizer ({a} : Set G), A⁆ ≤ A ⊓ U := by
  refine le_inf (le_normalizer_iff_commutator_le_right.mp
    (inf_le_right.trans (hTI.centralizer_le_normalizer ha hne))) ?_
  exact (commutator_mono inf_le_left le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAU)

omit [Finite G] in
private theorem ti_disjoint_fixed (A U : Subgroup G) (hTI : IsTISubgroup A)
    (hAU : A ≤ normalizer (U : Set G)) (hd : Disjoint A U)
    {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    U ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G) := by
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique ((ti_fixed_commutator A U hTI hAU ha hne).trans hd.le_bot))

private theorem ti_disjoint_elementary (A U : Subgroup G) [IsElementaryAbelian 2 U]
    (hTI : IsTISubgroup A) (hAU : A ≤ normalizer (U : Set G))
    (hd : Disjoint A U) (hcard : Nat.card A = 4)
    (hmove : ¬ A ≤ centralizer (U : Set G)) : IsElementaryAbelian 2 A := by
  let α : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAU)
  have hk (a : A) (ha : α a = 1) : a = 1 := by
    by_contra hn
    apply hmove
    apply le_centralizer_iff.mp
    intro v hv
    apply ti_disjoint_fixed A U hTI hAU hd a.property
      (fun he => hn (Subtype.ext he))
    refine ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg (fun f : MulAut U => (f ⟨v,hv⟩ : G)) ha
    change (a:G)*v*(a:G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hs (a : A) : a ^ 2 = 1 := by
    by_contra hn
    have hfour : α a ^ 4 = 1 := by
      rw [←map_pow, ←hcard, pow_card_eq_one',map_one]
    have he : FixedPoints.subgroup (zpowers (α a)) U =
        FixedPoints.subgroup (zpowers (α a ^ 2)) U := by
      ext v
      simp only [MulAut.mem_fixed_zpowers_iff]
      constructor
      · intro hv
        change α a (α a v) = v
        rw [hv,hv]
      · intro hv
        have hc : (v:G) ∈ centralizer (A : Set G) := by
          apply ti_disjoint_fixed A U hTI hAU hd (A.pow_mem a.property 2)
            (fun he => hn (Subtype.ext he))
          refine ⟨v.property, mem_centralizer_singleton_iff.mpr ?_⟩
          have he := congrArg (fun v : U => (v:G)) hv
          rw [←map_pow] at he
          change (a:G)^2*(v:G)*((a:G)^2)⁻¹ = v at he
          exact (mul_inv_eq_iff_eq_mul.mp he).symm
        apply Subtype.ext
        change (a:G)*(v:G)*(a:G)⁻¹ = v
        rw [hc a a.property,mul_inv_cancel_right]
    have ha : α a ≠ 1 := fun he => hn (by rw [hk a he,one_pow])
    have hh := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one (α a) hfour ha
    rw [he] at hh
    exact (lt_irrefl _ hh)
  exact { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hcard)
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }


private theorem rank_one_fourth_actor_trivial
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hexp : Monoid.exponent P = 3)
    (hc : centralizer (P : Set D) ≤ P) (t : D) (ht : t^4=1)
    (hs : BinaryOffender.fixedCodim ρ (zpowers t) ≤ 1) : t=1 := by
  have hcentral : t ∈ centralizer (P : Set D) := by
    intro p hp
    let x : P := ⟨⁅t,p⁆, P.mul_mem ((inferInstance : P.Normal).conj_mem p hp t) (P.inv_mem hp)⟩
    have hx : x=1 := by
      by_contra hn
      have hx3 : orderOf x=3 := orderOf_eq_prime
        (by simpa only [hexp] using Monoid.pow_exponent_eq_one x) hn
      have hlo := (ExtraspecialBinarySix.faithful_cubic_displacement_lower
        (ρ.comp P.subtype) (hf.comp P.subtype_injective) hP x hx3).1
      have hhi := BinaryOffender.fixedCodim_commutator_le_twice ρ t p
      simp only [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hlo hhi hs
      change 4 ≤ Module.finrank (ZMod 2) (ρ (t*p*t⁻¹*p⁻¹) - LinearMap.id).range at hlo
      omega
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hx)).symm
  have ht3 : t^3=1 := congrArg Subtype.val
    (show (⟨t,hc hcentral⟩ : P)^3=1 by
      simpa only [hexp] using Monoid.pow_exponent_eq_one (⟨t,hc hcentral⟩ : P))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 4 3)
    (orderOf_dvd_of_pow_eq_one ht) (orderOf_dvd_of_pow_eq_one ht3))

variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

private theorem small_actor_in_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (a : F.H) (ha4 : a^4=1)
    (hs : BinaryOffender.fixedCodim ρ (zpowers a) ≤ 1) : (a:G) ∈ F.H.pCoreIn 2 := by
  let : Finite W := Finite.of_surjective (fun u : F.U => (s.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  let P := pResidual 2 (HStar F.H)
  let eP := (residualStarEquiv F).symm.trans e
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv eP.symm
  have hP : Nat.card P=27 := (Nat.card_congr eP.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent P=3 :=
    (Monoid.exponent_eq_of_mulEquiv eP).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hb : b ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [section_action_kernel_eq_core_of_escape h structural (h.flag_escape F previous) s] at hb
    exact (QuotientGroup.eq_one_iff _).mpr hb
  have hs' : BinaryOffender.fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
    rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hs ⊢
    change Module.finrank (ZMod 2) ((σ.comp (starMap F)) a-LinearMap.id).range ≤ 1
    rwa [hσ]
  have hx := rank_one_fourth_actor_trivial σ hf P hP hexp
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    (starMap F a) (by rw [←map_pow,ha4,map_one]) hs'
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff a).mp hx)

omit [Finite G] in
private def centralRow (A Z : Subgroup G) (hZ : Z ≤ centralizer (A : Set G))
    (t : G) (ht : ∀ a ∈ A, ⁅t,a⁆ ∈ Z) : A →* Z where
  toFun a := ⟨⁅t,(a:G)⁆,ht a a.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅t,(a:G)*(b:G)⁆ = ⁅t,(a:G)⁆ * ⁅t,(b:G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      _ = ⁅t,(a:G)⁆ * ((a:G)*⁅t,(b:G)⁆) * (a:G)⁻¹ := by group
      _ = ⁅t,(a:G)⁆ * ⁅t,(b:G)⁆ := by rw [hZ (ht b b.property) a a.property]; group

omit [Finite G] in
private theorem centralRow_ker (A Z : Subgroup G) (hZ : Z ≤ centralizer (A : Set G))
    (t : G) (ht : ∀ a ∈ A, ⁅t,a⁆ ∈ Z) :
    (centralRow A Z hZ t ht).ker = (centralizer ({t} : Set G)).subgroupOf A := by
  ext a
  change (⟨⁅t,(a:G)⁆,ht a a.property⟩ : Z) = 1 ↔ (a:G) ∈ centralizer ({t} : Set G)
  rw [Subtype.ext_iff]
  change ⁅t,(a:G)⁆ = 1 ↔ (a:G) ∈ centralizer ({t}:Set G)
  rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff,eq_comm]

private theorem core_element_centralizer_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    {b : G} (hb : b ∈ F.H.pCoreIn 2) :
    (F.U ⊓ centralizer ({b} : Set G)).relIndex F.U ≤ 2 := by
  have hZ : F.Vi 1 ≤ centralizer (F.U : Set G) :=
    le_centralizer_iff.mp (s.section_le.trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have ht (u : G) (hu : u ∈ F.U) : ⁅b,u⁆ ∈ F.Vi 1 :=
    section_core_commutator_le_point h s (commutator_mem_commutator hb hu)
  let f := centralRow F.U (F.Vi 1) hZ b ht
  have hc := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hk := centralRow_ker F.U (F.Vi 1) hZ b ht
  rw [inf_relIndex_left]
  change ((centralizer ({b} : Set G)).subgroupOf F.U).index ≤ 2
  rw [←hk,index_ker]
  exact hc.trans_eq (by simpa using F.card 1 (by decide))

private theorem ti_disjoint_four_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hd : Disjoint A F.U)
    (hmove : ¬ A ≤ centralizer (F.U : Set G)) : A ≤ F.H.pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hAH : A ≤ F.H := hA.trans ((pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hAU := hAH.trans s.normalized
  let := ti_disjoint_elementary A F.U hTI hAU hd hc hmove
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have h27 : Nat.card ((K F) ⧸ pCore 2 (K F))=27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hmeet : A ⊓ F.H.pCoreIn 2 ≠ ⊥ := by
    intro hbot
    let f : A →* HStar F.H := (starMap F).comp (inclusion hAH)
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (by
      apply bot_unique
      intro a ha
      have hcore : (a:G) ∈ F.H.pCoreIn 2 :=
        mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff _).mp ha)
      exact Subtype.ext (mem_bot.mp (hbot ▸ (show (a:G) ∈ A ⊓ F.H.pCoreIn 2 from ⟨a.property,hcore⟩))))
    have hr : f.range ≤ star F (F.Ri L 1) := by
      rintro _ ⟨a,rfl⟩
      exact mem_map_of_mem (starMap F) (hA a.property)
    let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
    have hrank := (primeRank_mono 2 hr).trans
      (point_core_rank_one_of_extraspecial_residual h structural hex h27)
    have heq : Nat.card f.range = 4 := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
    let : IsElementaryAbelian 2 (⊤ : Subgroup f.range) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup f.range).subtype Subtype.val_injective
    have hb := (primeRank_le_iff_elementary_card_le f.range).mp hrank ⊤ inferInstance
    rw [card_top,heq] at hb
    norm_num at hb
  obtain ⟨⟨b,hb⟩,hbn⟩ := ne_bot_iff_exists_ne_one.mp hmeet
  have hbne : b ≠ 1 := fun he => hbn (Subtype.ext he)
  have hfixed := ti_disjoint_fixed A F.U hTI hAU hd hb.1 hbne
  have hindex := core_element_centralizer_index h s hb.2
  let B := F.U ⊓ centralizer ({b} : Set G)
  have hZB : F.Vi 1 ≤ B := le_inf s.kernel_le
    (le_centralizer_iff.mp ((zpowers_le.mpr (hAH hb.1)).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))) |>.trans
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers b))))
  have hsmall := BinaryConjugationSection.fixedCodim_le_one_of_fixed_index
    F.H F.U (F.Vi 1) A B ρ (MonoidHom.id F.H) s inf_le_left hZB
    (by rw [commutator_comm]; exact (commutator_eq_bot_iff_le_centralizer.mpr hfixed).le.trans bot_le) hindex
  intro a ha
  let aH : F.H := ⟨a,hAH ha⟩
  apply small_actor_in_core h structural previous ⟨e⟩ s aH
    (Subtype.ext (by simpa only [hc,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))))
  let : Finite _ := Finite.of_surjective (fun u : F.U => (s.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hle := Submodule.finrank_mono (BinaryOffender.fixedSpace_antitone ρ
    (zpowers_le.mpr (show aH ∈ ((A.subgroupOf F.H).map (MonoidHom.id F.H)) by
      exact mem_map_of_mem _ ha)))
  have hsum := BinaryOffender.fixedCodim_add_finrank ρ (zpowers aH)
  have hsum' := BinaryOffender.fixedCodim_add_finrank ρ ((A.subgroupOf F.H).map (MonoidHom.id F.H))
  omega

/-- Every moving TI four-subgroup of the original R₁ meets U. This is the
first case of the weak-closure argument, with the actual two-core retained. -/
theorem extraspecial_ti_four_meets_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hmove : ¬ A ≤ centralizer (F.U : Set G)) :
    A ⊓ F.U ≠ ⊥ := by
  intro hbot
  have hd : Disjoint A F.U := disjoint_iff.mpr hbot
  have hAQ := ti_disjoint_four_le_core h hab structural previous he A hA hc hTI hd hmove
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hAH := hAQ.trans (pCoreIn_le 2 F.H)
  have hAU := hAH.trans s.normalized
  have hcomm : ⁅F.U,A⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono hAQ le_rfl).trans (section_core_commutator_le_point h s)
  obtain ⟨v,hv,hvn⟩ : ∃ v ∈ F.U, v ∉ centralizer (A : Set G) := by
    by_contra! hh
    exact hmove (le_centralizer_iff.mp hh)
  have hZA : F.Vi 1 ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp (hAH.trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  let f := centralRow A (F.Vi 1) hZA v
    (fun a ha => hcomm (commutator_mem_commutator hv ha))
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (by
    apply bot_unique
    intro a ha
    by_contra hn
    have ha1 : a ≠ 1 := hn
    have he : ⁅v,(a:G)⁆=1 := congrArg Subtype.val ha
    apply hvn
    apply ti_disjoint_fixed A F.U hTI hAU hd a.property
      (fun he => ha1 (Subtype.ext he))
    exact ⟨hv,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp he)⟩)
  have hh := Nat.card_le_card_of_injective f hf
  rw [hc,show Nat.card (F.Vi 1)=2 by simpa using F.card 1 (by decide)] at hh
  omega

private theorem ti_four_moving_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (A : Subgroup G) (hA : A ≤ F.Ri L 1) (hc : Nat.card A=4)
    (hTI : IsTISubgroup A) (hmove : ¬ A ≤ centralizer (F.U : Set G)) :
    ⁅A,F.U⁆ = F.Vi 1 ∧ F.Vi 1 ≤ A := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let C := A ⊓ F.U
  have hC : C ≠ ⊥ := extraspecial_ti_four_meets_span h hab structural previous he A hA hc hTI hmove
  have hAH : A ≤ F.H := hA.trans ((pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hUA : F.U ≤ normalizer (A : Set G) :=
    ((le_centralizer_iff.mp ((show C ≤ F.U from inf_le_right).trans (le_centralizer _))).trans
      (Subgroup.centralizer_le_normalizer _)).trans (hTI.normalizer_le_of_ne_bot hC inf_le_left)
  have hcomm : ⁅A,F.U⁆ ≤ C := le_inf
    (le_normalizer_iff_commutator_le_left.mp hUA)
    (le_normalizer_iff_commutator_le_right.mp (hAH.trans s.normalized))
  have hC2 : Nat.card C ≤ 2 := by
    have hd := card_dvd_of_le (show C ≤ A from inf_le_left)
    rw [hc] at hd
    have hmem := Nat.mem_divisors.mpr ⟨hd,(by decide : (4:ℕ) ≠ 0)⟩
    have hvals : Nat.divisors 4 = {1,2,4} := by decide
    rw [hvals] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with hh | hh | hh
    · omega
    · omega
    · have heq : C=A := eq_of_le_of_card_ge inf_le_left (by rw [hh,hc])
      exact (hmove (heq ▸ (show C ≤ centralizer (F.U : Set G) from
        inf_le_right.trans (le_centralizer _)))).elim
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro a ha
    let aH : F.H := ⟨a,hAH ha⟩
    apply small_actor_in_core h structural previous he s aH
      (Subtype.ext (by simpa only [hc,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : A)))))
    rw [BinaryOffender.fixedCodim_zpowers_eq_displacement_rank]
    exact s.displacement_rank_le_of_commutator_bound A C ⊥ bot_le hcomm 1
      (by simpa using hC2) aH ha
  have hCZ : ⁅A,F.U⁆ ≤ F.Vi 1 := (commutator_mono hAQ le_rfl).trans
    (section_core_commutator_le_point h s)
  have hCn : ⁅A,F.U⁆ ≠ ⊥ := fun hh => hmove (commutator_eq_bot_iff_le_centralizer.mp hh)
  have hZ2 : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  have hdiv := card_dvd_of_le hCZ
  rw [hZ2] at hdiv
  have hcardC : Nat.card (⁅A,F.U⁆ : Subgroup G)=2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun hh => hCn (card_eq_one.mp hh))
  have heq : ⁅A,F.U⁆ = F.Vi 1 := eq_of_le_of_card_ge hCZ (by rw [hcardC,hZ2])
  exact ⟨heq,heq ▸ hcomm.trans inf_le_left⟩

/-- Every conjugate of the selected central four-group lying in R₁ centralizes
U. This discharges the moving-conjugate premise in the p.1054 argument. -/
theorem extraspecial_four_conjugate_centralizes_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) (hZD : F.Vi 1 ≤ D)
    (hDK : D ≤ (center (K F)).map (K F).subtype) (hcard : Nat.card D=4)
    (hTI : IsTISubgroup D) (g : G)
    (hg : D.map (MulAut.conj g).toMonoidHom ≤ F.Ri L 1) :
    D.map (MulAut.conj g).toMonoidHom ≤ centralizer (F.U : Set G) := by
  by_contra hmove
  let A := D.map (MulAut.conj g).toMonoidHom
  have hA4 : Nat.card A=4 := (card_map_of_injective (MulAut.conj g).injective).trans hcard
  have hZA := (ti_four_moving_commutator h hab structural previous he A hg hA4
    (hTI.map_equiv (MulAut.conj g)) hmove).2
  have hAD : A=D := (hTI.eq_or_disjoint_conjugate g).resolve_right (by
    intro hd
    have hz := (le_inf hZA hZD).trans hd.le_bot
    have hz2 := F.card 1 (by decide)
    rw [le_bot_iff.mp hz,card_bot] at hz2
    norm_num at hz2)
  apply hmove
  change A ≤ centralizer (F.U : Set G)
  rw [hAD]
  have hCU : (center (K F)).map (K F).subtype ≤ centralizer (F.U : Set G) := by
    rintro x ⟨z,hz,rfl⟩ u hu
    let uK : K F := ⟨u,(span_le_residual_core h hab).trans (pCoreIn_le 2 (K F)) hu⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz uK)
  exact hDK.trans hCU
/-- The actual weak closure is normal in both original overgroups, giving the
source contradiction at the end of the extraspecial branch. -/
theorem extraspecial_residual_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) := by
  intro he
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨D,hZD,hDK,hD4,hDT,hND,hTI⟩ := extraspecial_center_four_ti
    d h hab structural previous faithful earlier he
  let X := ChapterE.indexedWeakClosure D (F.Ri L 1) 0
  have hXU : X ≤ centralizer (F.U : Set G) := by
    change ChapterE.indexedWeakClosure D (F.Ri L 1) 0 ≤ _
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g,rfl,hg⟩ := (ChapterE.mem_gamma_zero_iff D (F.Ri L 1) A).mp hA
    exact extraspecial_four_conjugate_centralizes_span h hab structural previous he
      D hZD hDK hD4 hTI g hg
  have hQX : X ≤ Q T L :=
    (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans
      ((pCoreIn_le 2 _).trans Rechoice.group_le_LT))
      (hXU.trans (centralizer_le (le_conjugateSpanBy V F.H)))).trans
      (h.centralizer_LT structural).le
  have hQHX : X ≤ F.H.pCoreIn 2 := hXU.trans
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s)
  have hQT : Q T L ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hQHT : F.H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype (F.invariant 1))).trans_eq
      (map_subgroupOf_eq_of_le (F.invariant 1))
  have hQR : Q T L ≤ F.Ri L 1 :=
    (le_inf (hQT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_LT)
  have hQHR : F.H.pCoreIn 2 ≤ F.Ri L 1 :=
    (le_inf (hQHT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)
  have heq : X = ChapterE.indexedWeakClosure D (Q T L) 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hQX)
      (ChapterE.weakClosure_mono D 0 hQR)
  have heqH : X = ChapterE.indexedWeakClosure D (F.H.pCoreIn 2) 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hQHX)
      (ChapterE.weakClosure_mono D 0 hQHR)
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) := by
    rw [heq]
    exact ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))).trans
      (ChapterE.normalizer_le_weakClosure_normalizer D (Q T L) 0)
  have hH : F.H ≤ normalizer (X : Set G) := by
    rw [heqH]
    exact (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 F.H))).trans
      (ChapterE.normalizer_le_weakClosure_normalizer D (F.H.pCoreIn 2) 0)
  have hDcore : D ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (p := 2) (n := 2) hD4)
    (hDK.trans ((map_subtype_le _).trans (K_le_H F))) hND.ge
  have hXne : X ≠ ⊥ := by
    intro hx
    have hd : D=⊥ := le_bot_iff.mp (hx ▸ ChapterE.self_le_weakClosure_zero (hDcore.trans hQHR))
    rw [hd,card_bot] at hD4
    omega
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro Y _ _ hY S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hY S hM
  have hn : normalizer (X : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
      (fun M hM hLM => Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M}
          from ⟨hM,hLM⟩)) ((isPGroup_pCoreIn 2 _).to_le hQX) hXne hLT
  exact h.flag_escape F previous (hH.trans hn)

/-- The source's star formulation, transported by the canonical comparison
of O²(H/O₂(H)) with the original K/O₂(K). -/
theorem extraspecial_star_residual_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Nonempty (pResidual 2 (HStar F.H) ≃* HeisenbergPrime 3) := by
  rintro ⟨e⟩
  exact extraspecial_residual_impossible d h hab structural previous faithful earlier
    ⟨(residualStarEquiv F).trans e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
