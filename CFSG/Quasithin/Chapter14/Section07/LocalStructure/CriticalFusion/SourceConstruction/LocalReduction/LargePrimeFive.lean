module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableThreeCore
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction

/-!
# Quintic reduction of the original large-prime cores

In every original member of H_z, the proved F.9 construction supplies a
quadratic actor inside the image of R₁ on the literal U_J/V₁. When the
prime core supplements L₁T, that image acts faithfully on the prime core:
its intersection with the core centralizer would be a normal two-group.
Restricting to the prime core and this actor gives a genuine prime-by-two
action with cubic ratio at most two. D.2.13 forces the prime to be five
and constructs an order-two actor whose prime commutator has order five
and whose moved space has dimension four, with its actual fixed complement.

The minimal normal lift constructed earlier supplies the supplement premise
without an additional callback. Thus every prime core above three except
five vanishes, and the solvable-local application leaves only the five-core
and the previously constructed E₉/Heisenberg lifts. The surviving minimal
five-core has order five or twenty-five, and retains its normal two-perfect
lift, its exact quotient kernel and the four-dimensional reflection action.
The full normal dihedral factor decomposition and ambient exclusions remain;
this does not prove vanishing of the five-core or the final classification.

Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045, and its use in
14.7.28–29, p.1055; D.2.13, pp.184–185; F.9.16, p.324,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem prime_five_reflection_of_faithful_quadratic_actor
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (X A : Subgroup D) [X.Normal] (hXp : IsPGroup p X)
    (hA : IsElementaryTwo A) (hfaith : A ⊓ centralizer (X : Set D) = ⊥)
    (hquad : IsQuadratic ρ A) (hcod : fixedCodim ρ A ≤ 2 * rank A) :
    p = 5 ∧ ∃ R : Subgroup D, R ≤ X ⊔ A ∧ IsElementaryTwo R ∧ Nat.card R = 2 ∧
      IsCubic ρ R ∧ fixedCodim ρ R = 2 ∧ Nat.card (⁅X,R⁆ : Subgroup D) = 5 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅X,R⁆) = 4 ∧
      IsCompl (subspaceCommutator ρ ⊤ ⁅X,R⁆) (fixedSpace ρ (⁅X,R⁆ ⊔ R)) := by
  let E := X ⊔ A
  let X₀ := X.subgroupOf E
  let A₀ := A.subgroupOf E
  let σ := ρ.comp E.subtype
  let := hA.2
  have hA2 : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  have hgen : X₀ ⊔ A₀ = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hfaith₀ : A₀ ⊓ centralizer (X₀ : Set E) = ⊥ := by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1,?_⟩
    intro x hx
    exact congrArg Subtype.val (ha.2 ⟨x,mem_sup_left hx⟩ hx)
  have hdis : Disjoint X₀ A₀ := IsPGroup.disjoint_of_ne p 2 (by omega)
    _ _ hXp.comap_subtype hA2.comap_subtype
  have hcompl : X₀.IsComplement' A₀ :=
    isComplement'_of_disjoint_and_mul_eq_univ hdis (by rw [←normal_mul,hgen]; rfl)
  have hodd : Odd (Nat.card X₀) := by
    obtain ⟨n,hn⟩ := (show IsPGroup p X₀ from hXp.comap_subtype).exists_card_eq
    exact hn ▸ ((Fact.out : p.Prime).odd_of_ne_two (by omega)).pow
  let S : Sylow 2 E := hA2.comap_subtype.toSylow
    (by change ¬ 2 ∣ A₀.index; rw [hcompl.index_eq_card]; exact hodd.not_two_dvd_nat)
  have hcore : pCore 2 E = ⊥ := by
    have hc : pCore 2 E ≤ centralizer (X₀ : Set E) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint
        (IsPGroup.disjoint_of_ne 2 p (by omega) _ _ pCore_isPGroup hXp.comap_subtype))
    exact bot_unique ((le_inf (pCore_isPGroup.le_sylow_of_normal S) hc).trans hfaith₀.le)
  have hq : IsPGroup 2 (E ⧸ pCore p E) :=
    isPGroup_quotient_of_sup_eq_top _ A₀ hA2.comap_subtype
      (top_unique (hgen ▸ sup_le_sup_right (show X₀ ≤ pCore p E from
        le_sSup ⟨inferInstance,hXp.comap_subtype⟩) A₀))
  have hA₀ : IsElementaryTwo A₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf le_sup_right⟩
    intro hz
    have hh := congrArg (map E.subtype) hz
    rw [map_subgroupOf_eq_of_le le_sup_right,Subgroup.map_bot] at hh
    exact hA.1 hh
  have hbound : cubicRatio σ ≤ 2 := by
    apply (cubicRatio_le_nat_iff σ 2).mpr
    refine ⟨A₀,hA₀,isCubic_of_isQuadratic ?_,?_⟩
    · intro a ha b hb v
      exact hquad a ha b hb v
    · rw [fixedCodim_subgroupOf ρ le_sup_right,rank_subgroupOf le_sup_right]
      exact hcod
  obtain ⟨B,hB⟩ := (ChapterD.QhatStar_nonempty_iff σ).mpr hbound
  have hCX := centralizer_pCore_le_of_quotient_isPGroup p 2 hcore hq
  let := hB.1.2.1.2
  have hm : ⁅pCore p E,B⁆ ≠ ⊥ := by
    intro he
    have hBX : B ≤ pCore p E :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans hCX
    have hd : Disjoint B (pCore p E) := IsPGroup.disjoint_of_ne 2 p (by omega)
      _ _ (IsElementaryAbelian.isPGroup 2 B) pCore_isPGroup
    exact hB.1.2.1.1 (bot_unique ((le_inf le_rfl hBX).trans hd.le_bot))
  obtain ⟨hp35,hfive⟩ := ChapterD.source_lemma_D_2_13_one_two σ
    (hf.comp E.subtype_injective) hB ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hm
  have hp5 : p = 5 := hp35.resolve_left (by omega)
  obtain ⟨hratio,hr,he,hcomplW,hdim⟩ := hfive hp5
  have hcoreX : pCore p E = X₀ := by
    have hqX : IsPGroup 2 (E ⧸ X₀) :=
      isPGroup_quotient_of_sup_eq_top X₀ A₀ hA2.comap_subtype hgen
    have hzero : (pCore p E).map (QuotientGroup.mk' X₀) = ⊥ := by
      have hd := IsPGroup.disjoint_of_ne p 2 (by omega) _ _
        (pCore_isPGroup.map (QuotientGroup.mk' X₀)) (hqX.to_subgroup ⊤)
      simpa using hd.eq_bot
    refine le_antisymm ?_ (show X₀ ≤ pCore p E from le_sSup ⟨inferInstance,hXp.comap_subtype⟩)
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hzero
  rw [hcoreX] at he hcomplW hdim
  let R := B.map E.subtype
  have hcomm : (⁅X₀,B⁆).map E.subtype = ⁅X,R⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le le_sup_left]
  have hmove : subspaceCommutator σ ⊤ ⁅X₀,B⁆ = subspaceCommutator ρ ⊤ ⁅X,R⁆ := by
    rw [subspaceCommutator_comp_map,hcomm]
  have hfix : fixedSpace σ (⁅X₀,B⁆ ⊔ B) = fixedSpace ρ (⁅X,R⁆ ⊔ R) := by
    rw [fixedSpace_comp_map,Subgroup.map_sup,hcomm]
  have hcodB : fixedCodim σ B = 2 := by
    have hh := hB.1.2.2.2
    rw [actionRatio,hr,hratio] at hh
    norm_num at hh
    exact_mod_cast hh
  refine ⟨hp5,R,map_subtype_le B,⟨?_,IsElementaryAbelian.map E.subtype⟩,?_,?_,?_,?_,
    hmove ▸ hdim,hmove ▸ hfix ▸ hcomplW⟩
  · intro hz
    exact hB.1.2.1.1 ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp hz)
  · rw [card_map_of_injective E.subtype_injective,hB.1.2.1.card_eq_two_pow_rank,hr]
    rfl
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩ v
    exact hB.1.2.2.1 a ha b hb c hc v
  · change Module.finrank (ZMod 2) (W ⧸ fixedSpace ρ (B.map E.subtype)) = 2
    rw [←fixedSpace_comp_map]
    exact hcodB
  · rw [←hcomm,card_map_of_injective E.subtype_injective,
      Nat.card_congr he.some.toEquiv]
    simp


/-- The literal edge supplies a quadratic actor faithful on a normal prime supplement. -/
theorem local_prime_supplement_quadratic_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup (HStar I)) [X.Normal]
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ A : Subgroup I,
          A ≤ (F.Ri L 1).subgroupOf I ∧
          IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          IsQuadratic a.representation (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          fixedCodim a.representation (A.map (QuotientGroup.mk' (pCore 2 I))) ≤
            2 * rank (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          A.map (QuotientGroup.mk' (pCore 2 I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  let earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u} :=
    ⟨structural,uniqueness,previous⟩
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod⟩ :=
    Chapter12.Section09.NaturalSource.abelian_local_quadratic_actor h earlier F hab I hI
  let := hU
  refine ⟨hU,a,hq,A,hAR,hA,hquad,hcod,?_⟩
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let B₀ := (B.subgroupOf I).map q
  let R₀ := ((F.Ri L 1).subgroupOf I).map q
  have hBR₀ : B.subgroupOf I ≤ normalizer ((F.Ri L 1).subgroupOf I : Set I) := by
    apply le_normalizer_iff.mpr
    intro b hb r hr
    exact le_normalizer_iff.mp (le_normalizer_pCoreIn 2 B) b hb r hr
  have hBR : B₀ ≤ normalizer (R₀ : Set (HStar I)) :=
    (map_mono hBR₀).trans (le_normalizer_map q)
  have hR2 : IsPGroup 2 R₀ := (isPGroup_pCoreIn 2 B).comap_subtype.map q
  have hfaith := centralizer_inf_eq_bot_of_supplement X B₀ R₀ hgen hR2 hBR
    (pCore_quotient_pCore_eq_bot 2)
  exact bot_unique ((inf_le_inf_right _ (map_mono hAR)).trans hfaith.le)

/-- A prime above three with a normal prime-group supplement in a source local
quotient is necessarily five. -/
theorem local_prime_supplement_eq_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (X : Subgroup (HStar I)) [X.Normal] (hXp : IsPGroup p X)
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) : p = 5 := by
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous I hI X hgen
  let := hU
  exact (prime_five_reflection_of_faithful_quadratic_actor a.representation a.faithful hp X
    (A.map (QuotientGroup.mk' (pCore 2 I))) hXp hA hfaith hquad hcod).1

/-- In every actual local overgroup, a nontrivial prime core above three
has prime five. The minimal normal lift supplies the supplement premise. -/
theorem local_largePrime_eq_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hne : pCore p (HStar J) ≠ ⊥) : p = 5 := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXne,hXle,hXp,hXmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hcard,hcore,hdis,hgenStar,hirr⟩ :=
    local_largePrime_minimal_reduction h structural J hJ hp hne
  let := hXn
  let := hXp
  exact local_prime_supplement_eq_five h hab structural previous I hI hp X
    (IsElementaryAbelian.isPGroup p X) hgenStar

/-- All prime cores above three except five vanish on the literal local quotient. -/
theorem local_largePrime_core_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp5 : p ≠ 5) :
    pCore p (HStar J) = ⊥ := by
  by_contra hn
  exact hp5 (local_largePrime_eq_five h hab structural previous J hJ hp hn)

/-- The surviving five-core has a minimal source overgroup with its actual
normal two-perfect lift and a reflection moving a binary four-space. All
subgroups and both quotient kernels are those of this same overgroup. -/
theorem local_minimal_five_reflection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X.Normal ∧ IsElementaryAbelian 5 X ∧ X = pCore 5 (HStar I) ∧
      (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      (∀ W : Subgroup (HStar I), W.Normal → W ≤ X → W = ⊥ ∨ W = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          ∃ (A : Subgroup I) (R : Subgroup (HStar I)),
            A ≤ (F.Ri L 1).subgroupOf I ∧
            IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
            A.map (QuotientGroup.mk' (pCore 2 I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ ∧
            R ≤ X ⊔ A.map (QuotientGroup.mk' (pCore 2 I)) ∧
            IsElementaryTwo R ∧ Nat.card R = 2 ∧
            IsCubic a.representation R ∧ fixedCodim a.representation R = 2 ∧
            Nat.card (⁅X,R⁆ : Subgroup (HStar I)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,R⁆) = 4 ∧
            IsCompl (subspaceCommutator a.representation ⊤ ⁅X,R⁆)
              (fixedSpace a.representation (⁅X,R⁆ ⊔ R)) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXne,hXle,hXp,hXmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hcard,hcore,hdis,hgenStar,hirr⟩ :=
    local_largePrime_minimal_reduction h structural J hJ (by decide : 3 < 5) hne
  let := hXn
  let := hXp
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous I hI X hgenStar
  let := hU
  obtain ⟨_,R,hR,hRE,hRc,hcub,hfixed,hcomm,hmove,hcompl⟩ :=
    prime_five_reflection_of_faithful_quadratic_actor a.representation a.faithful (by decide : 3 < 5)
      X (A.map (QuotientGroup.mk' (pCore 2 I)))
      (IsElementaryAbelian.isPGroup 5 X) hA hfaith hquad hcod
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hXmin,hYn,hYp,hYle,
    hYm,hYk,he,hout,hgen,hs,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,hcub,hfixed,
    hcomm,hmove,hcompl⟩

/-- The actual solvable-local reduction now leaves only the five-core and
normal E9/Heisenberg lifts; all other large primes have been excluded. -/
theorem local_solvable_five_or_threeCore_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    pCore 5 (HStar J) ≠ ⊥ ∨
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  rcases local_solvable_reduction h hab structural J hJ hs with hp | hm
  · obtain ⟨p,hp,hbig,hne⟩ := hp
    let : Fact p.Prime := ⟨hp⟩
    exact Or.inl (local_largePrime_eq_five h hab structural previous J hJ hbig hne ▸ hne)
  · exact Or.inr hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
