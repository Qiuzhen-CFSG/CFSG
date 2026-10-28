module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.InvariantLayer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Automizer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Comparison
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.NormalClosureBranch

/-!
# Original 14.6.14 in the invariant cubic branch

Apply the intrinsic F.9.18 sieve to the actual relative component obtained
from the strict residual closure. The original exchanged factors exclude
the cyclic-automizer symplectic case. The surviving binary-linear component
has literal full quotient Aut(PSL₄(2)) or Aut(PSL₅(2)); its quotient image is
F*(Mc/O₂(Mc)), and it generates Mc with the original Sylow subgroup.

The second theorem applies this to the source component-orbit dichotomy.
Together with the proved normal branch, this leaves only the exchanged
components for the cubic closure classification. No closure classification
or normalizer conclusion is assumed.

The earlier primitive and exchanged-factor inputs retain their producers
qt-e-quintic-recognition and qt-e-14612-singleton. The independent p=3
exclusion belongs to qt-e-14615-quintic-exclusion. The exchanged quotient
recognition, parabolic normalizers and original 14.6.14--16 assembly remain
with qt-e-suitable-odd-normalizer; qt-e-suitable-existence owns final suitable
choice. This module does not assert their completion.

Source: Aschbacher--Smith 14.6.14, printed pp.1032--1033.
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

/-- Original 14.6.14(2) for the detected invariant cubic closure, including
its literal full Mc/O₂(Mc) automorphism group. The noncyclic automizer is
proved from the original exchanged factors. -/
theorem source_invariant_cubic_closure_alternative
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3)
    {P L : Subgroup G}
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P Mc)
    (hL : L ∈ cComponentsIn Mc) (hq : IsQuasisimple (XiQuotient L))
    (hn : (L.subgroupOf Mc).Normal) (hPL : P ≤ L) (hcomm : ⁅L,P⁆ = L)
    (hcl : residualClosure H Mc = L) :
    ((residualClosure H Mc).subgroupOf Mc).IsCComponent ∧
      (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) ∧
      residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
      StrictClosureLayer Mc (residualClosure H Mc) ∧
      Mc = residualClosure H Mc ⊔ (T : Subgroup G) := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hsq := hG.twoLocal_sqtk hMc.1.1
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hSyl : IsSylowIn 2 (T : Subgroup G) Mc :=
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
  have hmodels := source_invariant_closure_f918_models
    hG T hempty hM hunique hmany hcard e hab H hH hi hL.1 hL.2 hq hn hPL
  rcases invariant_cubic_f918_model hi hsq hSyl hL.1 hn hq hPL hcomm hmodels with
    ⟨_,hcy⟩ | ⟨⟨n,hn',hm⟩,_⟩
  · exact (exchanged_cubic_automizer_not_cyclic a T hH.1.2 hH.1.1 H0 H1 H2 hprim d hi hcy).elim
  · have hbound := source_solvable_overgroup_prime_bound hG T hunique H hH d.prime hmax
    have hno := source_no_suzuki_components hG T hunique hH hHMc d.prime hmax hprim
    obtain ⟨hr,hlayer⟩ := invariant_binary_closure_layer hi hsq hHMc
      (primitiveResidual_isSolvable H hprim) hbound hno hL hn hq hcl hn' hm
    have hfull := invariant_binary_full_quotient hi hSyl hL hn hcl hlayer hn' hm
    have hjoin := invariant_binary_join_eq hi hSyl hL hn
      ((le_conjugateSpanBy _ _).trans_eq hcl) hn' hm hfull
    exact ⟨by simpa only [hcl] using hL.2,⟨n,hn',hfull⟩,hr,hlayer,
      by simpa only [hcl] using hjoin⟩

/-- With the independent quintic exclusion explicit, all remaining closure
classification work is confined to the exchanged components. The invariant
branch already supplies the full source alternative and no local callback. -/
theorem source_cubic_closure_alternatives_or_exchanged
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3) :
    SourceClosureAlternatives (T : Subgroup G) Mc H 3 ∨
      (∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3 ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
  by_cases he : residualClosure H Mc = residual H
  · exact Or.inl (source_closure_alternatives_of_normal_residual
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d hmax he)
  obtain ⟨P,L,hi,hL,hcl,hn,hcomm⟩ := source_strict_closure_component_orbit
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d he
  by_cases hTL : (T : Subgroup G) ≤ normalizer (L : Set G)
  · have ho : componentOrbit L (T : Subgroup G) = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hTL)
      (le_componentOrbit L (T : Subgroup G))
    have hPL : P ≤ L := (hi.complement_le.trans (le_conjugateSpanBy _ _)).trans_eq (hcl.trans ho)
    rw [ho] at hn hcomm
    have hr := source_invariant_cubic_closure_alternative
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d hmax
      hi hL.mem hL.quasisimple hn hPL hcomm (hcl.trans ho)
    exact Or.inl (Or.inr (Or.inl ⟨rfl,(hcl.trans ho).symm ▸ hL.mem.1,hr.1,hr.2.1⟩))
  · have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hunique.symm ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := le_sup_right.trans hi.overgroup
    let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P Mc L :=
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
    obtain ⟨hr,_,hlayer⟩ := source_strict_exchanged_closure_layer
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d hmax he L hL.mem.1 hL.mem.2 hm
    exact Or.inr ⟨L,hL.mem.1,hL.mem.2,hL.quasisimple,hm,hr,hlayer⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
