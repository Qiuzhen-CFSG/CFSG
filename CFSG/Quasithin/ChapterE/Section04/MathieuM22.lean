module

public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu.TwentyTwoReduction
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M22.ValueBoundParabolics.Transport
public import Theory.Mathieu.M22.ValueBoundParabolics.CoverGeneration
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.GroupTheory.GeneralizedFitting.CentralizerQuotient
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The M₂₂ reduction for E.4.3(2)

If F*(G) is a quasisimple cover of M₂₂, G/F*(G) embeds in the outer
automorphism group of that cover. Perfectness embeds the latter in
Out(M₂₂), and the proved automorphism coverage makes it a two-group.
Consequently every Sylow two-subgroup supplements F*(G). This argument
allows nontrivial odd centers and outer extensions.

When O₂(G) is trivial, the centralizer of F*(G) has odd order and lies in
F*(G). Quotienting by this centralizer gives a faithful almost simple M₂₂
group, where the concrete pair and partition stabilizers supply the local
pair. Characteristic complements in the inner inverse images, adjoined to
the specified Sylow subgroup, lift the pair through the odd kernel. This
includes nonsplit odd central covers and outer extensions.

The generating-family adapter transports the small symmetric-group
calculations through the actual intrinsic two-core quotient isomorphisms,
then forms the two-member finset. The final existence theorem discharges
the pair and all four small-group inputs, giving total rank budget at most
three. The construction uses neither full inverse images as local lifts
nor a purported universal multiplier cover.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(2),
printed pp. 241–242 (PDF pp. 252–253). This file owns the M₂₂ family assembly;
the representation bound is assembled by the section's parent module.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValueBound.MathieuM22
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound
variable {G : Type*} [Group G] [Finite G]

/-- Every outer extension of a quasisimple generalized-Fitting cover of M₂₂
has two-power quotient by its generalized Fitting subgroup. -/
theorem quotient_fitting_isPGroup
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22) :
    IsPGroup 2 (G ⧸ generalizedFitting G) := by
  let L := generalizedFitting G
  let : IsQuasisimple L := hL
  have ho : IsPGroup 2 (MulAut.Outer M22) :=
    Chapter1.XiEmbedding.OuterModels.m22_outer_isPGroup_two_of_coverage
      m22DesignAutToAut_surjective
  have hcov : IsPGroup 2 (MulAut.Outer L) :=
    ho.of_injective (MulAut.centralQuotientOuter e)
      (MulAut.centralQuotientOuter_injective e)
  apply hcov.of_injective (MulAut.outerAction L)
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.map _ _ _ _).ker = ⊥
  rw [QuotientGroup.ker_map, MulAut.conjNormal_comap_innerSubgroup,
    sup_eq_left.mpr ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le,
    QuotientGroup.map_mk'_self]

/-- The required G = LT assertion, including central covers and outer extensions.
It does not require the additional trivial-two-core hypothesis. -/
theorem fitting_sup_sylow
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22)
    (T : Sylow 2 G) : generalizedFitting G ⊔ (T : Subgroup G) = ⊤ := by
  let q := QuotientGroup.mk' (generalizedFitting G)
  have hq := quotient_fitting_isPGroup hL e
  have htop : (T : Subgroup G).map q = ⊤ :=
    top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal
      (T.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hh := congrArg (fun A : Subgroup (G ⧸ generalizedFitting G) => A.comap q) htop
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using hh

/-- The kernel of the action on F*(G) has odd order when O₂(G) is trivial.
This uses self-centralization, rather than a claimed multiplier classification. -/
theorem centralizer_fitting_odd (hcore : pCore 2 G = ⊥) :
    Odd (Nat.card (centralizer (generalizedFitting G : Set G))) := by
  let C := centralizer (generalizedFitting G : Set G)
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp he)
  have hA : Nat.card (zpowers (z : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective C.subtype C.subtype_injective z).trans hz
  have hp : IsPGroup 2 (zpowers (z : G)) := IsPGroup.of_card (n := 1) hA
  have hbot : zpowers (z : G) = ⊥ :=
    (ChapterB.QuasisimpleSections.disjoint_centralizer_fitting
      hcore _ hp).eq_bot_of_le (zpowers_le.mpr z.property)
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := hbot ▸ mem_zpowers (z : G)
  have hzone : z = 1 := Subtype.ext hzbot
  simp [hzone] at hz

/-- Construct the two genuine Sylow overgroups for every quasisimple
generalized-Fitting cover of M₂₂ with trivial two-core. The subgroups generate
G and have intrinsic two-core quotients S₅ and S₃, including in odd central
covers and outer extensions. -/
theorem nonempty_parabolicPair
    (hcore : pCore 2 G = ⊥)
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22)
    (T : Sylow 2 G) : Nonempty (ParabolicPair T) := by
  let L := generalizedFitting G
  let : IsQuasisimple L := hL
  let C := centralizer (L : Set G)
  let q := QuotientGroup.mk' C
  let S := L.map q
  let : S.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective C)
  have hc : centralizer (S : Set (G ⧸ C)) = ⊥ :=
    centralizerQuotientComponent_centralizer L
  let eS : S ≃* M22 := (centralizerQuotientComponentEquiv L).symm.trans e
  obtain ⟨d⟩ := Concrete.nonempty_innerCompatiblePair S hc eS
    (T.mapSurjective (QuotientGroup.mk'_surjective C))
  exact OddCoverLifting.parabolicPair_of_oddCentralKernel L C
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    le_rfl (centralizer_fitting_odd hcore) T (fitting_sup_sylow hL e T) d

omit [Finite G] in
/-- An actual quotient isomorphism transports the local generalized-Fitting condition. -/
theorem isLocalOvergroup_of_quotientEquiv {K : Type*} [Group K]
    (H : Subgroup G) (e : (H ⧸ pCore 2 H) ≃* K)
    (h : IsQuasisimple (generalizedFitting K) ∨ (Nat.card (generalizedFitting K)).Prime) :
    IsLocalOvergroup H := by
  rcases h with h | h
  · let := h
    exact Or.inl (IsQuasisimple.of_mulEquiv (generalizedFittingEquiv e).symm)
  · exact Or.inr ((Nat.card_congr (generalizedFittingEquiv e).toEquiv) ▸ h)

/-- Construct the finite generating family from the actual pair and proved
small-quotient facts. Existence of the pair remains a separate obligation. -/
theorem generatingFamily_of_parabolicPair (T : Sylow 2 G) (P : ParabolicPair T)
    (h₅ : IsQuasisimple (generalizedFitting (Equiv.Perm (Fin 5))))
    (h₃ : (Nat.card (generalizedFitting (Equiv.Perm (Fin 3)))).Prime)
    (r₅ : primeRank 2 (Equiv.Perm (Fin 5)) ≤ 2)
    (r₃ : primeRank 2 (Equiv.Perm (Fin 3)) ≤ 1) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 3 := by
  classical
  have hl₁ : IsLocalOvergroup P.first :=
    isLocalOvergroup_of_quotientEquiv P.first P.firstQuotient (Or.inl h₅)
  have hl₂ : IsLocalOvergroup P.second :=
    isLocalOvergroup_of_quotientEquiv P.second P.secondQuotient (Or.inr h₃)
  have hr₁ : primeRank 2 (P.first ⧸ pCore 2 P.first) ≤ 2 :=
    (primeRank_equiv 2 P.firstQuotient).le.trans r₅
  have hr₂ : primeRank 2 (P.second ⧸ pCore 2 P.second) ≤ 1 :=
    (primeRank_equiv 2 P.secondQuotient).le.trans r₃
  refine ⟨{P.first, P.second}, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl
    · exact P.sylow_le_first
    · exact P.sylow_le_second
  · simpa only [Finset.coe_insert, Finset.coe_singleton, sSup_pair] using P.generate
  · intro H hH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hH
    rcases hH with rfl | rfl <;> assumption
  · by_cases he : P.first = P.second
    · simp only [he, Finset.insert_eq_of_mem (Finset.mem_singleton_self P.second),
        localRankBudget, Finset.sum_singleton]
      exact hr₂.trans (by decide : 1 ≤ 3)
    · simpa only [localRankBudget, Finset.sum_pair he] using Nat.add_le_add hr₁ hr₂

/-- The M₂₂ generating family needed in E.4.3(2). Every member contains the
specified Sylow two-subgroup, the family generates G, and the intrinsic local
quotients satisfy E.4.2 with total two-rank at most three. -/
theorem exists_generatingFamily
    (hcore : pCore 2 G = ⊥)
    (hL : IsQuasisimple (generalizedFitting G))
    (e : (generalizedFitting G) ⧸ center (generalizedFitting G) ≃* M22)
    (T : Sylow 2 G) :
    ∃ Δ : Finset (Subgroup G), IsGeneratingFamily T Δ ∧ localRankBudget Δ ≤ 3 := by
  obtain ⟨P⟩ := nonempty_parabolicPair hcore hL e T
  exact generatingFamily_of_parabolicPair T P
    SmallQuotients.symmetricFive_generalizedFitting_isQuasisimple
    SmallQuotients.symmetricThree_generalizedFitting_card_prime
    SmallQuotients.symmetricFive_primeRank_le_two
    SmallQuotients.symmetricThree_primeRank_le_one

end CFSG.Quasithin.ChapterE.ValueBound.MathieuM22
