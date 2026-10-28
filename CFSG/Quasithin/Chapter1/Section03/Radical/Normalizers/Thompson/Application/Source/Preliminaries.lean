module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import Stellmacher.SectionTwo.NativeBaumannActionFactors
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The source module and rank assertions of solvable Thompson factorization

For the original finite solvable group with F*(G)=O₂(G), the actual
normal closure of Ω₁Z(T) is elementary and has two-reduced centralizer
quotient. The central-Thompson case gives the literal product
N_G(J(T)) C_G(Ω₁Z(T)). In both cases B.1.8 excludes strong offenders in
the actual quotient action, so B.2.4 gives full centralizer two-rank
and the asserted Thompson containment. No factor or action is assumed.

Source: Aschbacher--Smith B.2.16, printed p.79.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem sectionTwo_of_sylow_ne_bot (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G)
    (ht : (T : Subgroup G) ≠ ⊥) : SectionTwo.Hypotheses G := by
  refine ⟨hs, ?_, ?_⟩
  · apply even_iff_two_dvd.mpr
    have hc := T.isPGroup'.card_eq_or_dvd
    rcases hc with hc | hc
    · exact (ht (Subgroup.card_eq_one.mp hc)).elim
    · exact hc.trans (T : Subgroup G).card_subgroup_dvd_card
  · simpa only [hf] using centralizer_generalizedFitting_le G

theorem closure_elementary_reduced (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G) :
    IsElementaryAbelian 2 (closure T) ∧
      pCore 2 (CentralQuotient (closure T)) = ⊥ := by
  by_cases ht : (T : Subgroup G) = ⊥
  · have hv : closure T = ⊥ := by
      unfold closure
      have hz : omegaOneCenterAmbient (T : Subgroup G) = ⊥ := by
        apply bot_unique
        intro z hz
        simpa only [ht] using (mem_omegaOneCenterAmbient_iff _ _).mp hz |>.1
      rw [hz, normalClosure_eq_self]
    constructor
    · rw [hv]
      exact { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subsingleton.elim _ _) }
    · have hc : centralizer (closure T : Set G) = ⊤ := by
        rw [hv]
        ext x
        simp [Subgroup.mem_centralizer_iff]
      let : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
      let e := QuotientGroup.quotientMulEquivOfEq hc
      let : Subsingleton (CentralQuotient (closure T)) := e.injective.subsingleton
      exact Subgroup.eq_bot_of_subsingleton _
  · have h := sectionTwo_of_sylow_ne_bot hs hf T ht
    refine ⟨(SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian h T).2, ?_⟩
    exact SectionTwo.lemma_two_one h T (starMap (closure T))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

theorem factorization_of_central_thompson (T : Sylow 2 G)
    (hc : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (closure T : Set G)) :
    (Set.univ : Set G) =
      (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Set G) *
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G) := by
  apply Set.Subset.antisymm ?_ (Set.subset_univ _)
  intro g _
  obtain ⟨n,hn,c,hc,rfl⟩ := ChapterB.thompson_normalizer_factorization (closure T) T hc g
  exact Set.mem_mul.mpr ⟨n,hn,c,centralizer_le le_normalClosure hc,rfl⟩

private theorem log_card_eq_finrank (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] : Nat.log 2 (Nat.card W) = Module.finrank (ZMod 2) W := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow Nat.one_lt_two]

theorem noStrong_of_solvable_quotient (V : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V]
    (hs : Group.IsSolvable (CentralQuotient V))
    (hr : pCore 2 (CentralQuotient V) = ⊥) (R : Subgroup G) :
    ChapterB.BaumannArgument.NoStrongOffenders V R := by
  let q := starMap V
  let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  have hn (A : Subgroup (CentralQuotient V)) : ¬ IsStrongOffender ρ A := by
    intro hA
    exact (ChapterB.Glauberman.numerical_conclusions hs hr
      (NormalElementaryQuotient.representation_injective V q _ _) ⟨A,hA.1,hA.2.le⟩).2 A hA
  intro A _ hAe hne
  have hc : rank (A.map q) ≤ fixedCodim ρ (A.map q) := by
    by_contra h
    exact hn _ ⟨⟨hne,hAe⟩,Nat.lt_of_not_ge h⟩
  have hfix : Nat.card (fixedSpace ρ (A.map q)) =
      Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) :=
    Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv V q _ _ A)
  have hdim := fixedCodim_add_finrank ρ (A.map q)
  rw [← log_card_eq_finrank (fixedSpace ρ (A.map q)),hfix,
    ← log_card_eq_finrank (Additive V)] at hdim
  change Nat.log 2 (Nat.card (A.map q)) ≤ Nat.log 2 (Nat.card V) - _
  change Nat.log 2 (Nat.card (A.map q)) ≤ _ at hc
  change _ + _ = Nat.log 2 (Nat.card V) at hdim
  omega

theorem source_rank_assertions (hs : Group.IsSolvable G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G) :
    ChapterB.twoRank ((T : Subgroup G) ⊓ centralizer (closure T : Set G)) =
      ChapterB.twoRank (T : Subgroup G) ∧
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (closure T : Set G)) ≤
        elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨he,hr⟩ := closure_elementary_reduced hs hf T
  let := he
  let := hs
  have hv : closure T ≤ (T : Subgroup G) := (IsElementaryAbelian.isPGroup 2 _).le_sylow_of_normal T
  obtain ⟨hrank,hfamily,_,_⟩ := ChapterB.BaumannArgument.centralizer_rank_and_alpha
    (closure T) (T : Subgroup G) hv (noStrong_of_solvable_quotient (closure T) inferInstance hr _)
  exact ⟨hrank,sSup_le fun A hA => le_sSup (hfamily hA)⟩
end CFSG.Quasithin.Chapter1.RadicalNormalizers.ThompsonSource
