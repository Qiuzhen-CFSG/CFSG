module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.InvariantLargeSieve
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.InvariantSource

/-!
# The strict closure comparison for both original primes

The original exchanged-factor quotient has noncyclic complement automizer
at both three and five. The invariant large-prime F.9.18 sieve therefore
excludes five in the invariant branch. Combining this with the checked
cubic invariant and exchanged branches proves StrictClosureComparison,
both literal prime-to-prime residual identities, and the full
Mc/O₂(Mc) generalized-Fitting layer.

The final theorem applies the comparison to the original outside H and
its global MaximalOddPrime choice. It leaves only the full outer action
of the exchanged PSL₂(4), PSL₂(16), and PSL₃(2) components; each is an
actual relative component with the original inverse-conjugation product.
The invariant branch already gives the full automorphism quotient.
This is not yet the four-way SourceClosureAlternatives theorem: the
exchanged wreath recognition and parabolic normalizers remain with
qt-e-suitable-odd-normalizer. No p=3 conclusion from 14.6.15 is used here.

The earlier primitive and exchanged-factor inputs retain their producers
qt-e-quintic-recognition and qt-e-14612-singleton. Final suitable-choice
assembly remains with qt-e-suitable-existence.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.XiEmbedding
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The original exchanged factors exclude the invariant component at five.
Only the actual earlier primitive residual and 14.6.12 input are used. -/
theorem source_invariant_closure_prime_eq_three
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    {P L : Subgroup G}
    (hi : LocalInput p (T : Subgroup G) (residual H) P Mc)
    (hL : L ∈ cComponentsIn Mc) (hq : IsQuasisimple (XiQuotient L))
    (hn : (L.subgroupOf Mc).Normal) (hPL : P ≤ L) (hcomm : ⁅L,P⁆ = L) : p = 3 := by
  rcases d.prime with h3 | h5
  · exact h3
  · subst p
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
    have hSyl : IsSylowIn 2 (T : Subgroup G) Mc :=
      ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    have hTL : (T : Subgroup G) ≤ normalizer L := hTMc.trans
      ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn)
    let hs : Chapter1.XiEmbedding.InvariantLarge.SylowInput KnownSimple.IsKnownSimple
        5 (T : Subgroup G) (residual H) P Mc L :=
      ⟨hi,hG.twoLocal_sqtk hMc.1.1,hSyl,hL,hn,hq,hTL,hPL,hcomm⟩
    have hm := source_invariant_closure_f918_models
      hG T hempty hM hunique hmany hcard e hab H hH hi hL.1 hL.2 hq hn hPL
    exact (exchanged_odd_automizer_not_cyclic a T hH.1.2 hH.1.1 5 H0 H1 H2 hprim d hi
      (invariant_large_f918_automizer_cyclic hs (by decide) hm)).elim

/-- The strict closure's invariant branch is cubic, and the exchanged
branch retains its literal prime-to-p and prime-to-three residuals and
full generalized-Fitting layer. This proves the comparison without any
assumed model classification or use of the later 14.6.15 theorem. -/
theorem source_strict_closure_models_and_layer
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hne : residualClosure H Mc ≠ residual H) :
    StrictClosureComparison (T : Subgroup G) Mc (residualClosure H Mc) p ∧
      residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
      residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure H Mc) := by
  obtain ⟨P,L,hi,hL,hcl,hn,hcomm⟩ := source_strict_closure_component_orbit
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hne
  by_cases hTL : (T : Subgroup G) ≤ normalizer (L : Set G)
  · have ho : componentOrbit L (T : Subgroup G) = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L (T : Subgroup G))
    have hPL : P ≤ L := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq (hcl.trans ho)
    rw [ho] at hn hcomm
    have hp := source_invariant_closure_prime_eq_three
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d
      hi hL.mem hL.quasisimple hn hPL hcomm
    subst p
    have hr := source_invariant_cubic_closure_alternative
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax
      hi hL.mem hL.quasisimple hn hPL hcomm (hcl.trans ho)
    obtain ⟨n,hn',he⟩ := hr.2.1
    have hMc : Mc = L ⊔ (T : Subgroup G) := by simpa only [hcl,ho] using hr.2.2.2.2
    let ej := MulEquiv.subgroupCongr hMc
    let eqj := QuotientGroup.congr _ _ ej (pCore_map_iso 2 ej)
    refine ⟨⟨L,hL.mem.1,hL.mem.2,hL.quasisimple,hcl,Or.inr ?_⟩,
      hr.2.2.1,hr.2.2.1,hr.2.2.2.1⟩
    exact ⟨rfl,hcl.trans ho,hTL,n,hn',he.map (eqj.symm.trans ·)⟩
  · have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
    let hs : SwappedSylowInput KnownSimple.IsKnownSimple p (T : Subgroup G) (residual H) P Mc L :=
      { toLocalInput := hi
        sqtk := hG.twoLocal_sqtk hMc.1.1
        component := hL.mem
        quasisimple := hL.quasisimple
        orbit_normal := hn
        complement_le_orbit := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq hcl
        orbit_commutator := hcomm
        noncentral := hL.noncentral_component_core
        not_invariant := hTL
        sylow_two := ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩ }
    have hm := source_swapped_closure_model hG T hempty hM hunique hmany hcard e hab H hH hs hprim d.prime hmax
    rw [←hcl] at hm
    exact ⟨⟨L,hL.mem.1,hL.mem.2,hL.quasisimple,hcl,Or.inl hm⟩,
      source_strict_exchanged_closure_layer
        hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax hne L hL.mem.1 hL.mem.2 hm⟩

/-- All source closure work remaining after the invariant sieve is the full
outer action of an actual exchanged pair. Its component field is already
four or sixteen, or it is the cubic PSL₃(2) row. Both residual identities
and the full generalized-Fitting layer are retained on the same Mc. -/
theorem source_closure_alternatives_or_exchanged_models
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        ((p = 3 ∧ ClassicalGroup.IsPSL
            ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 4) ∨
          (p = 5 ∧ ClassicalGroup.IsPSL
            ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) ∨
          (p = 3 ∧ ClassicalGroup.IsPSL
            ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2)) ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
  have hremaining : SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
    rcases d.prime with hp | hp
    · subst p
      rcases source_cubic_closure_alternatives_or_exchanged
          hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax with
        hc | ⟨L,hL,hcomp,hq,hm,hr,hlayer⟩
      · exact Or.inl hc
      · exact Or.inr ⟨L,hL,hcomp,hq,hm,hr,hr,hlayer⟩
    · subst p
      by_cases he : residualClosure H Mc = residual H
      · exact Or.inl (source_closure_alternatives_of_normal_residual
          hG T hempty hM hunique hmany hcard e hab H hH a 5 H0 H1 H2 hprim d hmax he)
      · obtain ⟨⟨L,hL,hcomp,hq,_,hm⟩,hr,hr3,hlayer⟩ := source_strict_closure_models_and_layer
          hG T hempty hM hunique hmany hcard e hab H hH a 5 H0 H1 H2 hprim d hmax he
        rcases hm with hm | hm
        · exact Or.inr ⟨L,hL,hcomp,hq,hm,hr,hr3,hlayer⟩
        · have hh := hm.1
          norm_num at hh
  rcases hremaining with hc | ⟨L,hL,hcomp,hq,hm,hr,hr3,hlayer⟩
  · exact Or.inl hc
  · exact Or.inr ⟨L,hL,hcomp,hq,hm,
      source_strict_exchanged_component_models
        hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax L hcomp hm,
      hr,hr3,hlayer⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
