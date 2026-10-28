module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.ClassicalRemainder
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OddG2
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LinearFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SymplecticFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryFour

/-!
# The remaining unitary component in the literal Hall kernel

The G₂, symplectic-four and Fermat linear-four exclusions reduce the four
remaining classical rows to PSU₄ over a Mersenne prime field. Its full
covering component contains the actual residual, and the original full
module has order 64. The escaping-kernel application preserves its literal
Hall subgroup, normalizer, quotient maps and movement conclusions. Local
Thompson movement supplies the already-proved module fixation when available.

Source: the opening argument of Aschbacher--Smith 10.2.3(2), printed p.745,
using 4.4.3 and 4.4.13--14. The remaining unitary exclusion and quiet-branch
module generation are still needed for unconditional Hall faithfulness.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Only the Mersenne PSU₄ row remains, with residual placement and module order 64. -/
theorem source_nonnormal_oddNormalizer_unitary_four_models
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) (hm : SourceHallNormalizerClassicalRemainder (K ⧸ center K)) :
    (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s+1 = 2^b) ∧
      ClassicalGroup.IsPSU (K ⧸ center K) 4 s) ∧
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ∧ Nat.card D.fullModule = 64 := by
  cases hm with
  | symplectic_odd r hr ho hm =>
    let : Fact r.Prime := ⟨hr⟩
    exact (source_nonnormal_oddNormalizer_no_odd_symplectic_four_component
      D hn hp B hB hBC hBV hperm K hK hout hc ho hm).elim
  | g2_odd r hr ho hm =>
    let : Fact r.Prime := ⟨hr⟩
    exact (source_nonnormal_oddNormalizer_no_odd_g2_component
      D hn hp B hB hBC hBV hperm K hK hout hc ho hm).elim
  | linear_four r hr hf hm =>
    exact (source_nonnormal_oddNormalizer_no_fermat_linear_four_component
      D hn hp B hB hBC hBV hperm K hK hout hc hf hm).elim
  | unitary_four s hs hpow hm =>
    let : Fact s.Prime := ⟨hs⟩
    have ho : Odd s := by
      obtain ⟨b,hb⟩ := hpow
      have hb0 : b ≠ 0 := by
        intro he
        simp only [he,pow_zero] at hb
        have := hs.two_le
        omega
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp
        (show Even (s+1) from hb.symm ▸ even_two.pow_of_ne_zero hb0))
    have hodd : Odd (Nat.card B) := by
      obtain ⟨n,he⟩ := hB.exists_card_eq
      rw [he]
      exact hp.pow
    have hFK := source_nonnormal_oddNormalizer_unitary_four_residual_le
      D hn hp B hB hBC hBV hperm K hK hout ho hm
    exact ⟨⟨s,hs,hpow,hm⟩,hFK,
      source_nonnormal_oddNormalizer_placed_unitary_four_module_card D hn B hBC hodd hBV K hc hFK ho hm⟩

/-- The literal escaping kernel reduces to a Mersenne unitary four-space,
with residual placement and the original module order determined. -/
theorem source_hstar_hall_kernel_escaping_component_unitary_four
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
        pCore 2 K = ⊥ ∧
        (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s+1 = 2^b) ∧
          ClassicalGroup.IsPSU (K ⧸ center K) 4 s) ∧
        ((solvableResidual
          (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
            (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
              (normalizer (A : Set G)) ≤ K ∧ Nat.card D.fullModule = 64 := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel⟩ :=
    source_hstar_hall_kernel_escaping_component_classical_models D hn hH hlarge hP d hk hfix
  let : Fact p.Prime := ⟨hp⟩
  let := hKn
  let := hAe
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,
    source_nonnormal_oddNormalizer_unitary_four_models D hn ho A
      (IsElementaryAbelian.isPGroup p A) hAC ((le_inf hAY hAC).trans hfix) hAT
      K hK houtK hcK hmodel⟩

/-- Local Thompson movement discharges fixation in the final unitary consumer. -/
theorem source_hstar_hall_kernel_unitary_four_of_local_thompson
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
        pCore 2 K = ⊥ ∧
        (∃ s : ℕ, s.Prime ∧ (∃ b : ℕ, s+1 = 2^b) ∧
          ClassicalGroup.IsPSU (K ⧸ center K) 4 s) ∧
        ((solvableResidual
          (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
            (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
              (normalizer (A : Set G)) ≤ K ∧ Nat.card D.fullModule = 64 := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  exact source_hstar_hall_kernel_escaping_component_unitary_four D hn hH hlarge hP d hk
    (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ d.witness.abelianGroup
      (he ▸ d.hall_le) (he ▸ d.hall))

end CFSG.Quasithin.Chapter10
