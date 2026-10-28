module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRows
public import Theory.Mathieu.M22.Properties.LocalA5Placement
public import Theory.Mathieu.M22.Properties.LocalA5Shape
public import Theory.Mathieu.M22.Properties.MarkedA5Fixer
public import Theory.Mathieu.M22.Properties.InvolutionFixedOrders
public import Theory.Mathieu.M23.Properties.A5Fixer
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import GorensteinWalter.PSL2Cardinality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.Source
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.GeneralLinearNatural
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.OddCharacteristicExclusion
public import Theory.Alternating.PrimeRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Quotient and low-degree exclusions before ordinary normalizer identification

The literal image of the original L in K/Z(K) retains L/O₂(L). Its perfectness,
rank-one order and faithful binary representation bound therefore survive the
quotient. The original fixed-radical involution and full Sylow placement exclude
M₂₂ and M₂₃; the degree bound and local A₅ section calculation exclude the
higher binary linear rows and all alternating rows.

Every theorem starts from the aligned OutsideChoice, without H = N_G(K).
SourceSelectionOrdinaryCatalogue consumes these exclusions on the original
component. The full source module below is distinct from the chosen V.
Source: Aschbacher–Smith C.3.1, pp.149–151, E.2.13(4), p.225, and 4.3.6, p.614.
The quotient and model arguments extend OrdinaryRecognitionMathieu/Linear to
this earlier boundary; their existing public interfaces remain unchanged.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (c : OutsideChoice T L) (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (K : Subgroup c.H) (ho : IsComponent c.H K)
  (hLK : L ≤ K.map c.H.subtype)
  (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
include D h ho hLK hout hKN
open ChapterA.Section02 ChapterA.Section03.SourceEmbeddings FiveLocalFF ClassificationModels

omit D ho hout hKN in
/-- The original local subgroup remains perfect under both inclusions. -/
theorem ordinaryLocal_perfect : Group.IsPerfect (c.ordinaryLocal K) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  exact Group.IsPerfect.ofSurjective (f := (c.ordinaryLocalEquiv hLK).symm.toMonoidHom)
    (c.ordinaryLocalEquiv hLK).symm.surjective

omit [Finite G] h ho hLK hout hKN in
/-- The original component Sylow normalizes L before normalizer identification. -/
theorem ordinary_component_sylow_normalizes_local :
    (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K ≤
      normalizer (c.ordinaryLocal K : Set K) := by
  intro s hs l
  exact D.sylow_normalizes_component hs.1 ((l : c.H) : G)

omit [Finite G] D h ho hLK hout hKN in
/-- The source span is L because its original actor lies in N_G(L). -/
theorem ordinary_span_eq : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
  le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)

/-- The full source module, without changing the chosen module V. -/
noncomputable abbrev ordinaryModule (_c : OutsideChoice T L) : Subgroup G :=
  Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)

omit hout hKN in
/-- Passing to the actual central-quotient model preserves the quotient of the
original local subgroup by its two-core. -/
theorem ordinary_model_local_quotient_equiv
     {S : Type*} [Group S] [Finite S]
    (e : (K ⧸ center K) ≃* S) :
    let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    Nonempty ((L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B)) := by
  let := ho.2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let k : L ≃* (c.ordinaryLocal K) := (c.ordinaryLocalEquiv hLK).symm
  let f := (q.subgroupMap (c.ordinaryLocal K)).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective (c.ordinaryLocal K)).comp k.surjective
  have hqker : q.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 q.ker := by
    rw [hqker,IsQuasisimple.center_eq_pCore (ho.1.pPrimeCore_eq_bot (c.c28 D h).oddCore_eq_bot)]
    exact pCore_isPGroup
  have hker : f.ker = q.ker.comap ((c.ordinaryLocal K).subtype.comp k.toMonoidHom) := by
    ext x
    exact Subtype.ext_iff
  have hfp : IsPGroup 2 f.ker := by
    rw [hker]
    exact hp.comap_of_injective _ ((c.ordinaryLocal K).subtype_injective.comp k.injective)
  exact ⟨f.pCoreQuotientEquiv hf hfp⟩

omit hout hKN in
/-- The original rank-one quotient forces its order to divide the order of the
literal local image in every central-quotient model. -/
theorem ordinary_model_local_order_dvd
     {S : Type*} [Group S] [Finite S]
    (e : (K ⧸ center K) ≃* S) {n : ℕ}
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card
      ((c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) := by
  let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hcard : Nat.card (B ⧸ pCore 2 B) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr b.toEquiv,←Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
  rw [←hcard]
  exact card_quotient_dvd_card (pCore 2 B)

omit c D h K ho hLK hout hKN in
private theorem binary_order_not_dvd_2688 {n : ℕ} (hn : 1 < n)
    (hd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 2688) : False := by
  have hd2 : 2 ^ n ∣ 2688 := (dvd_mul_right _ _).trans hd
  have hb : n < 8 := by
    by_contra! hn8
    have hh := (Nat.pow_dvd_pow 2 hn8).trans hd2
    norm_num at hh
  interval_cases n <;> norm_num at hd

/-- The actual R₀ involution excludes every M₂₃ central quotient of the ordinary
component, using the original local image and rank-one field size. -/
theorem ordinary_no_m23
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M23) : False := by
  let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e
  have hB : B ≤ a.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup a b).mpr (hfix b hb)
  obtain ⟨g,hg⟩ := Sporadic.Mathieu.m23_conj_surjective a
  obtain ⟨b⟩ := Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.fixedSubgroup_equiv_representative_of_inner
    a ha ⟨g,hg.symm⟩
  have hc : Nat.card a.fixedSubgroup = 2688 :=
    (Nat.card_congr b.toEquiv).trans
      Sporadic.Mathieu.M23Geometry.involutionRepresentative_centralizer_card
  exact binary_order_not_dvd_2688 hn
    (hc ▸ (c.ordinary_model_local_order_dvd D h K ho hLK e hpsl).trans (card_dvd_of_le hB))

omit c D h K ho hLK hout hKN in
private theorem binary_degree_of_dvd_m22 {n : ℕ} (hn : 1 < n)
    (hd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 443520) : n = 2 ∨ n = 3 := by
  have hd2 : 2 ^ n ∣ 443520 := (dvd_mul_right _ _).trans hd
  have hb : n < 8 := by
    by_contra! hn8
    have hh := (Nat.pow_dvd_pow 2 hn8).trans hd2
    norm_num at hh
  interval_cases n <;> first | exact Or.inl rfl | exact Or.inr rfl | norm_num at hd

/-- The original full-Sylow local data and actual R₀ action exclude every M₂₂
central quotient of the ordinary component. The natural A₅ placement is derived
inside this proof, including the original field-size-four case. -/
theorem ordinary_no_m22
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M22) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  have hd := c.ordinary_model_local_order_dvd D h K ho hLK e hpsl
  have hdn : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 443520 := by
    rw [←Sporadic.Mathieu.m22_order]
    exact hd.trans B.card_subgroup_dvd_card
  rcases binary_degree_of_dvd_m22 hn hdn with hn2 | hn3
  · obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
    have hF4 : Nat.card F = 4 := by
      norm_num [hn2] at hF
      exact hF
    obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
    let eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5) := b.trans d
    obtain ⟨P,hP,hlocal,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K)))
    have hnorm : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans ((c.ordinaryLocal K).le_normalizer_map f)
      rw [hP]
      exact (c.ordinary_component_sylow_normalizes_local D K)
    obtain ⟨hE,h16⟩ := Sporadic.Mathieu.M22LocalA5Shape.core_shape_of_normalized S B hnorm eB
    let := (c.ordinaryLocal_perfect h K hLK)
    let : Group.IsPerfect B := Group.IsPerfect.map f
    obtain ⟨v,hv⟩ := Sporadic.Mathieu.M22LocalA5Placement.exists_marking S B hlocal.subnormal hE h16 eB
    let e' := e.trans v
    have he' : (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
        B.map v.toMonoidHom := by
      rw [map_map]
      rfl
    obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e'
    rw [he'] at hfix
    have hh := Sporadic.Mathieu.m22_marked_involutory_fixer_eq_one (B.map v.toMonoidHom)
      hv r (hr ▸ pow_orderOf_eq_one r) hfix
    simp only [hh,orderOf_one] at hr
    omega
  · obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e
    have hB : B ≤ r.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup r b).mpr (hfix b hb)
    have hd9 : 9 ∣ Nat.card B := (by norm_num [hn3] : 9 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1)).trans hd
    exact Sporadic.Mathieu.m22_involution_not_nine_dvd_fixed_card r hr
      (hd9.trans (card_dvd_of_le hB))
omit hout hKN in
/-- The same original local quotient bounds every faithful binary linear model. -/
theorem ordinary_binary_linear_degree_bound
     {n d : ℕ} (hn : 1 < n)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* SL(d,ZMod 2)) : 2 * n ≤ d := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let b' := b.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let := (c.ordinaryLocal_perfect h K hLK)
  let : Group.IsPerfect B := Group.IsPerfect.map f
  have hB : B ≠ ⊥ := by
    intro he
    have hs : Group.IsSolvable B := he ▸ inferInstanceAs (Group.IsSolvable (⊥ : Subgroup SL(d,ZMod 2)))
    let := hs
    let j : ((c.ordinaryLocal K).map (QuotientGroup.mk' (center K))) →* B :=
      (e.toMonoidHom.comp ((c.ordinaryLocal K).map (QuotientGroup.mk' (center K))).subtype).codRestrict B (by
        rintro ⟨x,⟨l,hl,rfl⟩⟩
        exact ⟨l,hl,rfl⟩)
    exact c.ordinary_quotient_local_nonsolvable h K hLK (MulEquiv.refl (K ⧸ center K))
      (Group.isSolvable_of_isSolvable_injective (f := j) (by
        intro x y hh
        exact Subtype.ext (e.injective (congrArg Subtype.val hh))))
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  let ρ := (Representation.specialLinearNatural (k := ZMod 2) d).comp B.subtype
  have hi : Function.Injective ρ := (Representation.specialLinearNatural_injective d).comp B.subtype_injective
  obtain ⟨x,hx⟩ := exists_ne (1 : B)
  have hnt : ∃ x, ρ x ≠ 1 := ⟨x,fun he => hx (hi (he.trans ρ.map_one.symm))⟩
  simpa only [Module.finrank_fin_fun] using
    Representation.SL2.perfect_core_quotient_finrank_bound b' ρ hnt (by omega) hF

omit c D h K ho hLK hout hKN in
private theorem binaryLinearCoordinates {A : Type*} [Group A] {d : ℕ}
    (hd : 0 < d) (hm : IsPSL A d 2) : Nonempty (A ≃* SL(d,ZMod 2)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact ⟨((e.trans (Atlas.fieldEquivPSL d k)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear hd)).trans
      (BinaryLinear.OuterCyclic.slEquivLinear d).symm⟩

/-- Both higher binary linear quotient rows are impossible for the original local pair. -/
theorem ordinary_no_higher_binary_linear
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (hm : IsPSL (K ⧸ center K) d 2) : False := by
  have hb := c.ordinary_binary_linear_degree_bound D h K ho hLK hn hpsl
    (binaryLinearCoordinates (by rcases hd with rfl | rfl <;> decide) hm).some
  have hn2 : n = 2 := by rcases hd with rfl | rfl <;> omega
  let e := MulEquiv.refl (K ⧸ center K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hl,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  have hF4 : Nat.card F = 4 := by simpa [hn2] using hF
  obtain ⟨k⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.BinaryLinear.not_section_binary_linear
    (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    ((c.ordinaryLocal K).map f) hl (b.trans k) hd hm

omit hout hKN in
/-- The binary endpoint of the degree-three row violates the original field degree. -/
theorem ordinary_no_pslThree_binary
     {n : ℕ} (hn : 1 < n)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hm : IsPSL (K ⧸ center K) 3 2) : False := by
  have h := c.ordinary_binary_linear_degree_bound D h K ho hLK hn hpsl
    (binaryLinearCoordinates (by decide) hm).some
  omega

/-- All alternating quotient carriers of Theorem C are excluded, including A₈. -/
theorem ordinary_no_alternating
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {d : ℕ} (hd : d ≤ 8) (e : (K ⧸ center K) ≃* alternatingGroup (Fin d)) : False := by
  by_cases h8 : d = 8
  · subst d
    exact c.ordinary_no_higher_binary_linear D h K ho hLK hout hKN hn hpsl (Or.inl rfl)
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩
  · have hr := (c.c28 D h).ordinary_quotient_twoRank_ge_three K ho
    rw [primeRank_congr 2 e,
      (GLS3.Chapter5.PRank.alternating_hasPRank_two d).primeRank_eq Nat.prime_two] at hr
    omega

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
