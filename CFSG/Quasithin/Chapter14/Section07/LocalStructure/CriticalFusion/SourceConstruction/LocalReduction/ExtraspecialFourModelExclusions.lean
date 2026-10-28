module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourClassical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourSpan
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.AutomorphismRankBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Model reduction for the actual extraspecial ordinary component

The embedded original elementary span of order 128 excludes every small
sporadic row, the odd-characteristic rows, and both central two-covers in
1.1.5. For J₄, the actual inner involution centralizers have order divisible
by seven. Fixed-point lifting through the original central cover forces
seven into its fixed subgroup, which embeds in the original {2,3}-group H.
The intrinsic J₄ calculation and fixed-cover argument are adapted from
`Source/ResidualFusion/FixedCentralizers/Quasisimple/Recognition/Sporadic/SevenPrimes.lean`;
no Data or recognition conclusion is assumed here.

The full 1.1.5 case split now leaves only binary PSL₃ with even exponent at
least four, binary PSU₃ with odd exponent at least seven, triality, Ree F₄
and Tits quotients. The original Heisenberg action supplies the linear
parity restriction. All alternatives describe the literal B/O₂(B), and
the final application retains the original normal component, point-residual
inclusion, movement and marked inner involution. These five remaining
families, centralizer containment and TI are not asserted to be excluded.

Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
1.1.5(3), printed pp.501–503; GLS3 Table 5.3i for the J₄ centralizers.
Imported concrete model proofs retain their source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
private theorem fixed_card_conj {A : Type*} [Group A] {x y : A} (h : IsConj x y) :
    Nat.card (MulAut.conj x).fixedSubgroup = Nat.card (MulAut.conj y).fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he := Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj c) (MulAut.conj x)).toEquiv
  rw [MulAut.congr_conj] at he
  exact he.trans (congrArg (fun z : A => Nat.card (MulAut.conj z).fixedSubgroup) hc)

private theorem j4_seven [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model] (y : Janko4.Model) (hy : orderOf (MulAut.conj y) = 2) :
    7 ∣ Nat.card (MulAut.conj y).fixedSubgroup := by
  have ho : orderOf y = 2 := (MulAut.conj_orderOf_of_center_eq_bot Subgroup.center_eq_bot_of_simple_perfect y).symm.trans hy
  have hfirst : 7 ∣ Nat.card (MulAut.conj Janko4.a).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj, Janko4.OuterReduction.OddIndex.modelCentralizer_card]
    norm_num
  have hseed : 7 ∣ Nat.card
      (MulAut.conj (Janko4.InvolutionCentralizers.Second.seed : Janko4.Model)).fixedSubgroup := by
    rw [MulAut.fixedSubgroup_conj]
    change 7 ∣ Nat.card Janko4.InvolutionCentralizers.Second.ambientCentralizer
    rw [Janko4.InvolutionCentralizers.Second.ambient_card]
    norm_num
  have hsecond : 7 ∣ Nat.card
      (MulAut.conj ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b) ^ 5)).fixedSubgroup := by
    obtain ⟨c, hc⟩ := Janko4.Simplicity.Max1Fusion.seed_fuses_second
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four
    have hw : Janko4.Simplicity.word
        (Janko4.Simplicity.a Janko4.matrixA_mul_self)
        (Janko4.Simplicity.b Janko4.matrixB_pow_four) "ababb" =
        Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
      change Janko4.Simplicity.word Janko4.a Janko4.b "ababb" = _
      simp [Janko4.Simplicity.word, mul_assoc]
    rw [hw] at hc
    have hf := fixed_card_conj (isConj_iff.mpr ⟨c, hc.symm⟩)
    exact hf ▸ hseed
  rcases Janko4.OuterReduction.involution_isConj_of_max1_odd_index
    Janko4.OuterReduction.max1_odd_index_unconditional ho with h | h
  · exact fixed_card_conj h ▸ hfirst
  · exact fixed_card_conj h ▸ hsecond

private theorem seven_of_cover {A B : Type*} [Group A] [Finite A] [Group B]
    (f : PerfectCentralCovering.Cover A B) (α : MulAut A) (hα : TwoCentralInner α)
    (hseven : ∀ y : B, orderOf (MulAut.conj y) = 2 →
      7 ∣ Nat.card (MulAut.conj y).fixedSubgroup) :
    7 ∣ Nat.card α.fixedSubgroup := by
  let := f.isPerfect
  obtain ⟨⟨x, hx⟩, ho, P, hP⟩ := hα
  let β := MulAut.conj (f.toMonoidHom x)
  have heq (a : A) : f.toMonoidHom (α a) = β (f.toMonoidHom a) := by
    rw [← hx]
    simp only [β, MulAut.conj_apply, map_mul, map_inv]
  have ha2 : α ^ 2 = 1 := ho ▸ pow_orderOf_eq_one α
  have hb2 : β ^ 2 = 1 := by
    ext b
    obtain ⟨a, rfl⟩ := f.surjective b
    change β (β (f.toMonoidHom a)) = f.toMonoidHom a
    rw [← heq, ← heq]
    exact congrArg f.toMonoidHom (show α (α a) = a from
      DFunLike.congr_fun ha2 a)
  have hbne : β ≠ 1 := by
    intro hb
    have ha : α = 1 := MulAut.eq_one_of_central_displacement α (fun a => by
      apply f.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, hb, MulAut.one_apply, inv_mul_cancel])
    rw [ha, orderOf_one] at ho
    contradiction
  have hb : orderOf β = 2 := orderOf_eq_prime hb2 hbne
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α β f.toMonoidHom
    f.surjective f.ker_le_center heq ha2 P (fun a ha => hP ⟨a, ha⟩)
  exact (hseven _ hb).trans (card_dvd_of_surjective _ hsurj)


private theorem small_sporadic_rank (name : SporadicName)
    [Finite name.Carrier] [IsSimpleGroup name.Carrier] [Group.IsPerfect name.Carrier]
    (h3 : name ≠ .j3) (h4 : name ≠ .j4) : primeRank 2 name.Carrier ≤ 6 := by
  have hi : primeRank 2 name.Carrier ≤ primeRank 2 (MulAut name.Carrier) :=
    _root_.primeRank_le_of_injective 2 MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot Subgroup.center_eq_bot_of_simple_perfect)
  cases name with
  | m11 => exact hi.trans (Sporadic.Mathieu.m11_automorphism_twoRank_le_two.trans (by decide))
  | m12 => exact Sporadic.Mathieu.m12_twoRank_le_three.trans (by decide)
  | m22 => exact Sporadic.Mathieu.m22_twoRank_le_four.trans (by decide)
  | m23 => exact Sporadic.Mathieu.m23_twoRank_le_four.trans (by decide)
  | m24 => exact Sporadic.Mathieu.m24_twoRank_le_six
  | j2 => exact hi.trans Sporadic.LeechRelated.J2.automorphism_primeRank_le_six
  | j3 => exact (h3 rfl).elim
  | j4 => exact (h4 rfl).elim
  | hs => exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  | he => exact Held.primeRank_two_le_six
  | ru => exact Rudvalis.primeRank_le_six

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem original_fixed_not_seven
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {x : G} (B : Subgroup (centralizer ({x} : Set G)))
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹) :
    ¬ 7 ∣ Nat.card α.fixedSubgroup := by
  let C := centralizer ({x} : Set G)
  have hm (a : α.fixedSubgroup) : ((a.val : C) : G) ∈ F.H := by
    apply Subgroup.centralizer_le_normalizer (F.Vi 1 : Set G)
    have hα : α a.val = a.val := (MulAut.mem_fixedSubgroup _ _).mp a.property
    have hh : z * (a.val : G) * z⁻¹ = (a.val : G) := by
      rw [←ha,hα]
    have hc : Commute z (a.val : G) := mul_inv_eq_iff_eq_mul.mp hh
    rw [←hz]
    intro y hy
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
    exact (hc.zpow_left n).eq
  let f : α.fixedSubgroup →* F.H :=
    (C.subtype.comp (B.subtype.comp α.fixedSubgroup.subtype)).codRestrict F.H hm
  have hf : Function.Injective f := by
    intro a b hh
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : F.H => (y : G)) hh
  intro h7
  have hH7 := h7.trans (card_dvd_of_injective f hf)
  have hd := odd_prime_dvd_twoCore_quotient_residual (by decide : Nat.Prime 7) (by decide) hH7
  obtain ⟨e⟩ := he
  rw [Nat.card_congr ((residualStarEquiv F).symm.trans e).toEquiv,HeisenbergPrime.card] at hd
  norm_num at hd

/-- Every sporadic row of the actual 1.1.5 marking is excluded. Small rows
contradict the embedded original U; the J₄ row forces seven in its actual
fixed subgroup, which lies in the original {2,3}-group H. -/
theorem extraspecial_four_ordinary_not_sporadic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (ht : TwoCentralInner α) (name : SporadicName) (h3 : name ≠ .j3)
    (e : (B ⧸ pCore 2 B) ≃* name.Carrier) : False := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ pCore 2 B) := (extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.2.2.1
  let : Group.IsPerfect (B ⧸ pCore 2 B) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 B)) (QuotientGroup.mk'_surjective _)
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect name.Carrier := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hr := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  rw [primeRank_equiv 2 e] at hr
  by_cases hn : name = .j4
  · subst name
    let e' : (B ⧸ pCore 2 B) ≃* Janko4.Model := e
    let : IsSimpleGroup Janko4.Model := e'.symm.isSimpleGroup
    let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
      (f := e'.toMonoidHom) e'.surjective
    let c : PerfectCentralCovering.Cover B Janko4.Model :=
      { toMonoidHom := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
        surjective := e'.surjective.comp (QuotientGroup.mk'_surjective _)
        isPerfect := inferInstance
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
          exact IsQuasisimple.pCore_le_center 2 }
    exact original_fixed_not_seven he B z hz α ha (seven_of_cover c α ht j4_seven)
  · have hb := small_sporadic_rank name h3 hn
    omega
private theorem binary_three_parameter {Q : Type*} [Group Q] [Finite Q]
    (hr : 7 ≤ primeRank 2 Q)
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL Q 3 (2^n)) :
    4 ≤ n ∧ Even n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hrF : 7 ≤ 2*n := by
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hr
    exact hr
  refine ⟨by omega,Nat.not_odd_iff_even.mp ?_⟩
  intro ho
  have hmod : Nat.card F % 3 = 2 := by
    rw [hF,Nat.BinaryTorusParity.two_pow_mod_three,
      if_neg (by have hh := Nat.odd_iff.mp ho; omega)]
  have hcop : Nat.Coprime 3 (Nat.card F - 1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hpos := Finite.one_lt_card (α := F)
    omega
  have hz : center SL(3,F) = ⊥ := (eq_bot_iff_card _).mpr (by
    rw [Atlas.ExceptionalSupport.card_sl_center]
    simpa only [Fintype.card_fin] using hcop.gcd_eq_one)
  let ep : SL(3,F) ≃* PSL(3,F) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  let ea := MulAut.congr (e.trans ep.symm)
  exact Matrix.SL3.no_heisenberg_automorphism_action (by omega) hF hz
    (ea.toMonoidHom.comp f) (ea.injective.comp hf)

/-- The literal ordinary component cannot belong to either odd-characteristic
row of 1.1.5: its original elementary subgroup has order 128. -/
theorem extraspecial_four_ordinary_not_odd
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (hm : ClassicalGroup.IsPSL B 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL B 2 p) : False := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨i,_,hi⟩ := extraspecial_four_ordinary_span_embedding
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hii : Function.Injective i := fun a b hh => hi (congrArg (QuotientGroup.mk' _) hh)
  let : IsElementaryAbelian 2 (⊤ : Subgroup F.U) :=
    IsElementaryAbelian.of_injective _ (⊤ : Subgroup F.U).subtype_injective
  have hru : 7 ≤ primeRank 2 F.U :=
    IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup F.U) (by
      simpa only [card_top, Nat.reducePow] using (extraspecial_source_reduction h hab structural previous he).2.1)
  have hr : 7 ≤ primeRank 2 B := hru.trans (_root_.primeRank_le_of_injective 2 i hii)
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,F,_,_,hF,⟨e⟩⟩
  · rw [primeRank_equiv 2 e] at hr
    have hb := Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
      (by decide : Nat.Prime 3) (by decide) hF
    omega
  · by_cases hp2 : p = 2
    · rcases hp2 with rfl
      let : Fintype F := Fintype.ofFinite F
      have hc : Nat.card (GL (Fin 2) F) = 6 := by
        rw [Matrix.card_GL_field]
        simp only [←Nat.card_eq_fintype_card,hF]
        norm_num
      have hdiv : 128 ∣ Nat.card B := by
        rw [←(extraspecial_source_reduction h hab structural previous he).2.1]
        exact card_dvd_of_injective i hii
      rw [Nat.card_congr e.toEquiv] at hdiv
      have hquot : Nat.card PSL(2,F) ∣ Nat.card SL(2,F) :=
        (center SL(2,F)).card_quotient_dvd_card
      have hSL : Nat.card SL(2,F) ∣ 6 := by
        rw [←hc]
        exact card_dvd_of_injective Matrix.SpecialLinearGroup.toGL
          Matrix.SpecialLinearGroup.toGL_injective
      exact (by decide : ¬128 ∣ 6) (hdiv.trans (hquot.trans hSL))
    · have ho := hp.1.odd_of_ne_two hp2
      let P : Sylow 2 PSL(2,F) := default
      obtain ⟨n,_,⟨en⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
        ⟨p,1,hp.1,ho,by omega,by simpa using hF⟩ P
      rw [primeRank_equiv 2 e,P.primeRank_eq,primeRank_equiv 2 en] at hr
      have hb := Theory.GroupTheory.dihedral_rank_le_two n
      omega

/-- Neither central two-cover row of 1.1.5 can be the original component. -/
theorem extraspecial_four_ordinary_not_twoCover
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 4 ∨ IsG2At (B ⧸ pCore 2 B) 4) : False := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | hg
  · have hr := extraspecial_four_ordinary_twoRank
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
    have hb := Matrix.PSL3Even.two_rank F (n := 2) (by decide) hF
    rw [primeRank_equiv 2 e,hb] at hr
    omega
  · exact (extraspecial_four_ordinary_quotient_exclusions
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB).2.2.1
        2 (by decide) hg

/-- The full original 1.1.5 model list leaves only the indicated large linear,
large unitary, triality, Ree and Tits quotients. The bounds and parity refer
to the actual quotient and follow from the original U and Heisenberg actions. -/
theorem extraspecial_four_ordinary_model_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hz : zpowers z = F.Vi 1) (α : MulAut B)
    (ha : ∀ b : B, ((α b : centralizer ({x} : Set G)) : G) = z * (b : G) * z⁻¹)
    (hm : ModelAction115 B α) :
    (∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
    (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
    (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
    (∃ m, 1 ≤ m ∧ IsReeF4At (B ⧸ pCore 2 B) m) ∨
    Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup) := by
  let : IsQuasisimple B := hB.2
  have hs := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hc := hs.2.2.2.1
  have hno := extraspecial_four_ordinary_quotient_exclusions
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hr := extraspecial_four_ordinary_twoRank
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have halt {n : ℕ} (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
      (hm : AlternatingAction α n σ) : False := by
    rcases hm with ⟨e,_⟩ | ⟨_,⟨ez⟩,_,_⟩
    · have hcenter : center B = ⊥ := (eq_bot_iff_card _).mpr (by
        rw [Nat.card_congr (centerCongr e).toEquiv,
          alternatingGroup.center_eq_bot (by simpa only [Nat.card_fin] using (show 4 ≤ n by omega)),card_bot])
      let eq : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin n) :=
        (QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hcenter)).trans
          (QuotientGroup.quotientBot.trans e)
      exact hno.2.2.2.2.2.2 n (by omega) ⟨eq⟩
    · have hz3 : Nat.card (pCore 2 B) = 3 := by
        rw [←hc,Nat.card_congr ez.toEquiv]
        simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
      rcases (pCore_isPGroup (p := 2) (G := B)).card_eq_or_dvd with hh | hh
      · omega
      · rw [hz3] at hh
        norm_num at hh
  cases hm with
  | lie hsimple hmodel _ =>
    let : IsSimpleGroup B := hsimple
    have hpc : pCore 2 B = ⊥ := hc.symm.trans Subgroup.center_eq_bot_of_simple_perfect
    let eq : (B ⧸ pCore 2 B) ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    rcases hmodel with hm | hm | ⟨n,hn,hm⟩
    · cases hm with
      | linear n _ hm => exact (hno.1 n (hm.of_mulEquiv eq)).elim
      | unitary n hn hm =>
        have hmQ := hm.of_mulEquiv eq
        have hn7 : 7 ≤ n := by
          obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := hmQ
          rw [primeRank_equiv 2 e,
            BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hF hJ] at hr
          exact hr
        have hodd : Odd n := Nat.not_even_iff_odd.mp (fun heven => hno.2.2.2.2.2.1 n hn heven hmQ)
        exact Or.inr (Or.inl ⟨n,hn7,hodd,hmQ⟩)
      | suzuki m hm iso =>
        exact (extraspecial_four_not_suzuki_component
          d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB
          (by omega) iso.some).elim
    · cases hm with
      | linear n hn hm =>
        obtain ⟨hnA,haA⟩ := extraspecial_four_ordinary_action
          d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
        let := hnA
        obtain ⟨_,_,_,_,_,_,f,hf,_⟩ := haA
        let g := (normalQuotientAction B (pCore 2 B)).range.subtype.comp f
        have hp := binary_three_parameter hr g (Subtype.val_injective.comp hf) hn (hm.of_mulEquiv eq)
        exact Or.inl ⟨n,hp.1,hp.2,hm.of_mulEquiv eq⟩
      | symplectic n hn hm => exact (hno.2.1 n hn (hm.of_mulEquiv eq)).elim
      | g2 n hn hm => exact (hno.2.2.1 n hn (hm.of_mulEquiv eq)).elim
      | triality n hn hm => exact Or.inr (Or.inr (Or.inl ⟨n,hn,hm.of_mulEquiv eq⟩))
      | ree m hm iso =>
        obtain ⟨r,⟨e⟩⟩ := iso
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m,hm,r,⟨eq.trans e⟩⟩)))
      | symplectic_derived iso =>
        let es := (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).symm
        let ed := (es.subgroupMap (commutator (ClassicalGroup.PSp 2 (ZMod 2)))).trans
          (MulEquiv.subgroupCongr (by rw [map_commutator_eq,MonoidHom.range_eq_top.mpr es.surjective]))
        let ea := (eq.trans iso.some).trans (ed.trans
          (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
        exact (hno.2.2.2.2.2.2 6 (by omega) ⟨ea⟩).elim
      | g2_derived iso => exact (hno.2.2.2.1 ⟨eq.trans iso.some⟩).elim
      | tits iso => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eq.trans iso.some⟩)))
    · exact (hno.2.2.2.2.1 n hn (hm.of_mulEquiv eq)).elim
  | two_cover _ _ hm _ =>
    exact (extraspecial_four_ordinary_not_twoCover
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm).elim
  | six σ _ hm => exact (halt (Or.inl rfl) σ hm).elim
  | seven σ _ hm => exact (halt (Or.inr rfl) σ hm).elim
  | odd hm _ =>
    exact (extraspecial_four_ordinary_not_odd
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB hm).elim
  | sporadic name hn iso ht =>
    exact (extraspecial_four_ordinary_not_sporadic
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
      z hz α ha ht name hn iso.some).elim

/-- Apply the model exclusions to the original escaping centralizer, preserving
its normal component, point-residual inclusion and marked inner involution.
The five remaining quotient families are not yet excluded. -/
theorem extraspecial_four_ordinary_reduced_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        ModelAction115 B α ∧
        ((∃ n, 4 ≤ n ∧ Even n ∧ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 7 ≤ n ∧ Odd n ∧ ClassicalGroup.IsPSU (B ⧸ pCore 2 B) 3 (2^n)) ∨
        (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2^n) (B ⧸ pCore 2 B)) ∨
        (∃ m, 1 ≤ m ∧ IsReeF4At (B ⧸ pCore 2 B) m) ∨
        Nonempty ((B ⧸ pCore 2 B) ≃* Tits.ParrottGroup)) := by
  obtain ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel⟩ :=
    extraspecial_four_ordinary_inner_source
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  exact ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,α,ha,hi,hmodel,
    extraspecial_four_ordinary_model_reduction
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
      z hzp α ha hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
