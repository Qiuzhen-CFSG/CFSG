module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceData
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceImages
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveActions
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Quotient
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

/-!
This additive source variant uses only `SecondaryActionData`; it does not
assume whole-radical torus movement. The legacy conditional API is preserved.

# Source model inputs on the literal nonblock component

The nonsolvable secondary subgroup lies in the normal root centralizer,
so C-component minimality forces the whole secondary component to centralize
the root. Faithfulness of the torus then supplies actual outside elements of
each prime order dividing its order. Their split extensions retain normality,
C-component membership and the original quasisimple two-core quotient. The
same elements rule out the residual and theta equalities in A.3.18.

The diagonal torus in the secondary PSL₂ quotient gives rank exactly one
at each such prime. SQTK bounds the containing component's rank by two.
Finally Theorems A and C apply to the actual inner image, using its literal
surjection from the component; no quasithin quotient inheritance is assumed.

These are inputs to the still unproved prime-rank refinement and four-row
inspection. They do not assert SourceAlternatives. Their final assembly
remains with qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith, original 4.3.12 and 4.3.16, printed pp.617–618;
A.2.1–3 and A.3.18, printed pp.33 and 51–53.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The literal K₂ is a nontrivial perfect group, hence nonsolvable. -/
theorem SecondaryActionData.secondary_not_solvable (s : SecondaryActionData c n) :
    ¬ Group.IsSolvable (secondary c) := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := s.secondary_model
  let : Nontrivial (secondary c ⧸ pCore 2 (secondary c)) := e.surjective.nontrivial
  let : Nontrivial (secondary c) :=
    (QuotientGroup.mk'_surjective (pCore 2 (secondary c))).nontrivial
  let := secondary_perfect c
  exact Group.IsPerfect.not_isSolvable (secondary c)

/-- C-component minimality puts all of K_Z in C_G(Z_S). -/
theorem SecondaryActionData.component_centralizes_root (s : SecondaryActionData c n) :
    s.component.map (rootNormalizer c).subtype ≤ centralizer (root c : Set G) := by
  let C := (centralizer (root c : Set G)).subgroupOf (rootNormalizer c)
  let B := (secondary c).subgroupOf (rootNormalizer c)
  have hB : secondary c ≤ rootNormalizer c := s.secondary_le.trans (map_subtype_le _)
  let : C.Normal := normal_subgroupOf_centralizer_normalizer (root c : Set G)
  have hBC : B ≤ C := comap_mono (secondary_le_centralizer c)
  have hBI : B ≤ s.component := by
    intro x hx
    obtain ⟨y, hy, he⟩ := s.secondary_le hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hBn : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact SecondaryActionData.secondary_not_solvable s
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hB).toMonoidHom)
        (subgroupOfEquivOfLe hB).surjective)
  have hC := s.isComponent.le_normal_of_nonsolvable_subgroup hBn hBI hBC
  rintro x ⟨y, hy, rfl⟩
  exact hC hy

/-- Root faithfulness separates the original torus from the entire component. -/
theorem SecondaryActionData.torus_disjoint_component (s : SecondaryActionData c n) :
    s.torus ⊓ s.component.map (rootNormalizer c).subtype = ⊥ :=
  bot_unique ((inf_le_inf_left _ (SecondaryActionData.component_centralizes_root s)).trans_eq
    s.torus_faithful)

/-- Cauchy supplies an actual prime-order actor outside K_Z. -/
theorem SecondaryActionData.exists_outside_prime_actor (s : SecondaryActionData c n)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    ∃ a : rootNormalizer c,
      (a : G) ∈ s.torus ∧ orderOf a = p ∧ a ∉ s.component := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := s.torus) p
    (by rwa [s.torus_card])
  let a' : rootNormalizer c := ⟨a, s.torus_le a.property⟩
  refine ⟨a', a.property, ?_, ?_⟩
  · exact (orderOf_injective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective a').symm.trans
        ((orderOf_injective s.torus.subtype s.torus.subtype_injective a).trans ha)
  · intro hac
    have h1 : (a : G) = 1 := mem_bot.mp
      ((SecondaryActionData.torus_disjoint_component s).le
        ⟨a.property, mem_map.mpr ⟨a', hac, rfl⟩⟩)
    have ha1 : a = 1 := Subtype.ext h1
    rw [ha1, orderOf_one] at ha
    exact hp.ne_one ha.symm

/-- The genuine split-prime extensions to which the A.3.18 source theorem
applies. The actor has order p before passage to any action image. -/
theorem SecondaryActionData.exists_split_prime_extension (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    ∃ a : rootNormalizer c, (a : G) ∈ s.torus ∧ orderOf a = p ∧ a ∉ s.component ∧
      let E := s.component ⊔ zpowers a
      let B := s.component.subgroupOf E
      let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
      IsSQTK KnownSimple.IsKnownSimple E ∧ B.Normal ∧ B.IsCComponent ∧
        IsQuasisimple (B ⧸ pCore 2 B) ∧ B ⊔ zpowers a' = ⊤ ∧
        primeRank p B = primeRank p s.component := by
  obtain ⟨a, hat, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s hp hd
  refine ⟨a, hat, ha, han, ?_⟩
  let E := s.component ⊔ zpowers a
  let B := s.component.subgroupOf E
  let a' : E := ⟨a, (le_sup_right : zpowers a ≤ E) (mem_zpowers a)⟩
  let := s.normal
  let e : B ≃* s.component := subgroupOfEquivOfLe (show s.component ≤ E from le_sup_left)
  let := s.quasisimple
  refine ⟨(rootNormalizer_sqtk c D h).subgroup E, inferInstance,
    s.isComponent.subgroupOf le_sup_left,
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm,
    ?_, primeRank_congr p e⟩
  apply map_injective E.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- The first alternative of A.3.18 is incompatible with the faithful torus.
The prime-order element belongs to the residual in the original group. -/
theorem SecondaryActionData.component_ne_primeToResidual (s : SecondaryActionData c n)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ n - 1) :
    s.component ≠ primeToResidual p (rootNormalizer c) := by
  obtain ⟨a, _, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s hp hd
  intro he
  apply han
  rw [he]
  apply mem_primeToResidual_of_pow (n := 1)
  simpa only [pow_one, ← ha] using pow_orderOf_eq_one a

/-- The theta alternative of A.3.18(3a) is also excluded before quotienting. -/
theorem SecondaryActionData.component_ne_theta (s : SecondaryActionData c n)
    (hd : 3 ∣ 2 ^ n - 1) :
    s.component ≠ ChapterA.Section03.OddPrime.SourceModels.theta (rootNormalizer c) := by
  obtain ⟨a, _, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s Nat.prime_three hd
  intro he
  apply han
  rw [he]
  exact subset_closure ha

/-- The odd-rank bound applies to the full component quotient, before any
further central quotient is taken. -/
theorem SecondaryActionData.componentQuotient_sqtk (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple (s.component ⧸ pCore 2 s.component) := by
  have hs := (rootNormalizer_sqtk c D h).subgroup s.component
  refine ⟨?_, hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 s.component) pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

/-- Each prime in the source torus has rank exactly one in the literal K₂.
The diagonal torus in its binary SL₂ quotient supplies the lower bound. -/
theorem SecondaryActionData.secondary_primeRank_eq_one (s : SecondaryActionData c n)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p (secondary c) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hu := odd_primeRank_le_one s.secondary_model ho
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := s.secondary_model
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  have hdF : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have ht : Nat.card Fˣ ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) :=
      card_dvd_of_injective (BenderSuzuki.Converse.torHom F)
        BenderSuzuki.Converse.torHom_injective
    rw [Nat.card_units, hF] at ht
    exact hd.trans ht
  have hdQ : p ∣ Nat.card (secondary c ⧸ pCore 2 (secondary c)) := by
    rwa [Nat.card_congr e'.toEquiv]
  have hds := hdQ.trans
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (secondary c)))
      (QuotientGroup.mk'_surjective _))
  have hl : primeRank p (secondary c) ≠ 0 := fun hz =>
    PrimeRank.eq_zero_iff_not_dvd_card.mp hz hds
  omega

/-- The source component has rank one or two at every torus prime.
This is only the initial bound; excluding rank two outside the diagonal
cubic case still requires the source automorphism analysis. -/
theorem SecondaryActionData.component_primeRank_one_or_two (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p s.component = 1 ∨ primeRank p s.component = 2 := by
  have hu := ((rootNormalizer_sqtk c D h).subgroup s.component).stronglyQuasithin p hp ho
  have hl := Theory.GroupTheory.primeRank_le_of_injective p (SecondaryActionData.secondaryToComponent s)
    (SecondaryActionData.secondaryToComponent_injective s)
  rw [SecondaryActionData.secondary_primeRank_eq_one s hp ho hd] at hl
  omega

/-- Theorem C classifies the literal inner image on K_Z/O₂(K_Z). -/
theorem SecondaryActionData.componentImage_theoremC (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ChapterA.Section02.IsTheoremCModel (SecondaryActionData.componentImage s) := by
  let J := s.component ⧸ pCore 2 s.component
  let := s.quasisimple
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let I := MulAut.innerSubgroup J
  let e : I ≃* J ⧸ center J := innerEquivCentralQuotient
  let : IsSimpleGroup I := e.isSimpleGroup
  let : Group.IsPerfect I := Group.IsPerfect.range MulAut.conj
  have hn : ¬ IsMulCommutative I := by
    intro hcomm
    let := hcomm
    exact Group.IsPerfect.not_isSolvable I inferInstance
  let : IsQuasisimple I :=
    IsQuasisimple.of_surjective (MulAut.conj : J →* MulAut J).rangeRestrict
      MulAut.conj.rangeRestrict_surjective
  have hsem : ChapterA.Section02.IsSemisimple I := by
    apply top_unique
    exact le_sSup (show IsComponent I ⊤ from
      ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  let f : s.component →* I :=
    MulAut.conj.rangeRestrict.comp (QuotientGroup.mk' (pCore 2 s.component))
  have hf : Function.Surjective f :=
    MulAut.conj.rangeRestrict_surjective.comp (QuotientGroup.mk'_surjective _)
  have hsec : ChapterA.Section02.IsSectionOf I (rootNormalizer c) := ⟨s.component, f, hf⟩
  have hs := rootNormalizer_sqtk c D h
  have hr := ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple hs.stronglyQuasithin hs.isKGroup hsec hsem
  have hm := ChapterA.Section02.theoremC_knownSimple inferInstance hn hr
    (hsec.isKGroup hs.isKGroup)
  rw [SecondaryActionData.componentImage_eq_inner]
  exact hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
