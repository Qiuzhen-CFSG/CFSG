module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OddThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryFive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.RemainingApplication

/-!
# Four remaining classical rows for the actual escaping Hall kernel

The small-Frattini pair argument excludes both odd ternary rows, J₃, McL,
Sp₆(2) and PSU₄(2); the two-action flag also excludes PSU₅(4). Combined with the earlier complete shared-C sieve, this
leaves four actual classical model alternatives. The original elementary
Hall actor supplies all permutation and coprimality premises; local Thompson
movement also supplies full-module fixation in the second application.

The four remaining rows and quiet-branch module fixation remain obligations.
This is not an unconditional faithfulness theorem. Source: Aschbacher--Smith
4.4.10--14 and 10.2.3(2), printed pp.621--625,745.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- Actual model alternatives after all sporadic, ternary and small binary rows. -/
inductive SourceHallNormalizerClassicalRemainder (Q : Type*) [Group Q] : Prop
  | symplectic_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassicalGroup.IsPSp Q 2 p)
  | g2_odd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (model : ClassificationModels.IsG2At Q p)
  | linear_four (r : ℕ) (hp : r.Prime) (hf : ∃ k : ℕ, r = 2^(2^k)+1)
      (model : ClassicalGroup.IsPSL Q 4 r)
  | unitary_four (s : ℕ) (hp : s.Prime) (hm : ∃ b : ℕ, s+1 = 2^b)
      (model : ClassicalGroup.IsPSU Q 4 s)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The complete old remainder narrows on the original permuting odd actor. -/
theorem source_nonnormal_oddNormalizer_remaining_classical_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) (hm : SourceHallNormalizerRemainder (K ⧸ center K)) :
    SourceHallNormalizerClassicalRemainder (K ⧸ center K) := by
  cases hm with
  | linear_three_square r hr ho hm =>
    exact (source_nonnormal_oddNormalizer_no_odd_linear_three_component
      D hn hp B hB hBC hBV hperm K hK hout ho.pow hm).elim
  | unitary_three_square r hr ho hm =>
    exact (source_nonnormal_oddNormalizer_no_odd_unitary_three_component
      D hn hp B hB hBC hBV hperm K hK hout ho.pow hm).elim
  | symplectic_odd r hr ho hm => exact .symplectic_odd r hr ho hm
  | g2_odd r hr ho hm => exact .g2_odd r hr ho hm
  | linear_four r hr hf hm => exact .linear_four r hr hf hm
  | unitary_four r hr hf hm => exact .unitary_four r hr hf hm
  | unitary_four_two hm =>
    exact (source_nonnormal_oddNormalizer_no_binary_unitary_four_two_component
      D hn hp B hB hBC hBV hperm K hK hout hm).elim
  | unitary_five_four hm =>
    exact (source_nonnormal_oddNormalizer_no_unitary_five_component
      D hn hp B hB hBC hBV hperm K hK hout hm).elim
  | symplectic_six_two hm =>
    exact (source_nonnormal_oddNormalizer_no_binary_symplectic_component
      D hn hp B hB hBC hBV hperm K hK hout hm).elim
  | janko_three hm =>
    exact (source_nonnormal_oddNormalizer_no_jankoThree_component
      D hn hp B hB hBC hBV hperm K hK hout hc hm.some).elim
  | mcl hm =>
    exact (source_nonnormal_oddNormalizer_no_mcl_component
      D hn hp B hB hBC hBV hperm K hK hout hc hm.some).elim

/-- The literal escaping kernel has one of four remaining classical components. -/
theorem source_hstar_hall_kernel_escaping_component_classical_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥)
    (hfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ SourceHallNormalizerClassicalRemainder (K ⧸ center K) := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel⟩ :=
    source_hstar_hall_kernel_escaping_component_remaining_models D hn hH hlarge hP d hk hfix
  let : Fact p.Prime := ⟨hp⟩
  let := hKn
  let := hAe
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,
    source_nonnormal_oddNormalizer_remaining_classical_models D hn ho A
      (IsElementaryAbelian.isPGroup p A) hAC ((le_inf hAY hAC).trans hfix) hAT
      K hK houtK hcK hmodel⟩

/-- Local Thompson movement discharges fixation in the four-row consumer. -/
theorem source_hstar_hall_kernel_classical_models_of_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ SourceHallNormalizerClassicalRemainder (K ⧸ center K) := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  exact source_hstar_hall_kernel_escaping_component_classical_models D hn hH hlarge hP d hk
    (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ d.witness.abelianGroup
      (he ▸ d.hall_le) (he ▸ d.hall))

end CFSG.Quasithin.Chapter10
