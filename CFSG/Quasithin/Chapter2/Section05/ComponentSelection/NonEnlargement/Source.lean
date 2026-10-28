module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.SourceReduction
public import Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.RemainingTargets

/-!
# Original non-enlargement for the nonbinary rank-two source components

The completed source containment theorem supplies an ordinary component C
of N_G(E) containing K, with the original central involution and full Sylow
marking. Source 2.5.2 classifies C. Concrete Sylow intersections, odd ranks,
and two-parts exclude the Bender, prime-linear and small rows. In each larger
binary rank-two row, K together with the full Sylow of C maps onto the actual
simple target; the proved parabolic exclusion and central-supplement argument
force K=C. All rank, center, action, and Sylow-placement inputs are supplied
from the original hypotheses. The independent earlier C.1.29 source input
is the same one used by the complete 2.5.2 classifier.

Source: Aschbacher–Smith 2.5.6, printed p.554, specialized to the original
PSL₃(2ⁿ) and PSp₄(2ⁿ) quotient cases with n>1, as used in 2.5.7.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
open ComponentRefinement ClassificationModels Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {M H K S T E : Subgroup G} {z : G}

theorem component_in_normalizer_of_binary_rank_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC : LocalC129Input KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀:Subgroup G)≤M)
    (hunique : ∀ N:Subgroup G, IsMaximalTwoLocal N → (T₀:Subgroup G)≤N → N=M)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H=K⊔S)
    {n:ℕ} (hn:1<n)
    (hm : ClassicalGroup.IsPSL (K⧸center K) 3 (2^n) ∨ ClassicalGroup.IsPSp (K⧸center K) 2 (2^n))
    (hE:E≠⊥) (hEC:E≤S⊓centralizer (K:Set G)) (hSE:S≤normalizer (E:Set G)) :
    IsComponentIn K (normalizer (E:Set G)) := by
  have hHgam : H∈gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h=>h.1.1) (fun h=>h.1)
  obtain ⟨R,hR⟩ := d.sylow_intersection
  obtain ⟨Q,hQ⟩ := (intersection_sylow hHgam R).2
  obtain ⟨cK⟩ := exists_setup_of_same_sylow T₀ hM hT₀M hunique d d.gamma_zero Q (hQ.trans hR) hK
  have hZ : IsPGroup 2 (center K) := by
    rw [MathieuSourceSetup.center_eq_twoCore cK hG sourceC hempty]
    exact pCore_isPGroup
  let : IsQuasisimple K := hK.quasisimple
  obtain ⟨p,hp,ho,hr⟩ := odd_rank_two_of_model hZ hn hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P,C,hP,hC,hKC,hZC,⟨cC⟩,U,hUK⟩ :=
    exists_normalizing_containing_component hG sourceC T₀ hM hT₀M hunique hempty d hK hgen
      hZ ho hr hE hEC hSE
  let : IsQuasisimple C := hC.quasisimple
  let i := inclusion hKC
  have hi : Function.Injective i := inclusion_injective hKC
  have hb : ¬IsBenderModel C := by
    intro hb
    exact not_injective_bender hZ hm hb i hi
  have hmodels := MathieuSourceSetup.nonBender_model cC hG sourceC hempty hb
  let eK : K.subgroupOf C ≃* K := subgroupOfEquivOfLe hKC
  let : IsQuasisimple (K.subgroupOf C) := IsQuasisimple.of_mulEquiv eK.symm
  have hZKC : IsPGroup 2 (center (K.subgroupOf C)) := hZ.of_equiv (centerCongr eK.symm)
  have hrank : 2≤primeRank p (K.subgroupOf C) := by rwa [primeRank_equiv p eK]
  have heq : K.subgroupOf C=⊤ := by
    rcases hmodels with hs | hl | (ht | ht) | ht
    · obtain ⟨F,_,_,m,hm₀,hF,⟨e⟩⟩ := hs
      by_cases hm₁ : m=1
      · have hF₂ : Nat.card F=2 := by simpa [hm₁] using hF
        exact (not_injective_small_targets hn hm
          (Or.inr (Or.inr ⟨e.trans (Binary.derivedEquivAlternatingSix hF₂)⟩)) i hi).elim
      let : CharP F 2 := EvenProjective.charTwo_of_card hF
      have hcard : 2<Nat.card F := by
        rw [hF]
        calc 2=2^1 := by norm_num
             _<2^m := Nat.pow_lt_pow_right (by decide) (by omega)
      exact Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity.symplectic
        (K.subgroupOf C) hZKC ho hrank U hUK hcard (e.trans (derivedEquivFull_of_card_gt_two hcard))
    · obtain ⟨F,_,_,m,hm₀,hF,⟨e⟩⟩ := hl
      by_cases hm₁ : m=1
      · exact (not_injective_binary_linear_cover hZ hZC hn hm
          ⟨F,inferInstance,inferInstance,by simpa [hm₁] using hF,⟨e⟩⟩ i hi).elim
      exact Theory.SpecificGroups.Classical.EvenRankTwoSylowRigidity.linear
        (K.subgroupOf C) hZKC ho hrank U hUK (n:=m) (by omega) hF e
    · obtain ⟨e⟩ := ht
      exact (not_injective_small_targets hn hm (Or.inl ⟨e⟩) i hi).elim
    · obtain ⟨e⟩ := ht
      exact (not_injective_small_targets hn hm (Or.inr (Or.inl ⟨e⟩)) i hi).elim
    · obtain ⟨r,hr,hrlarge,⟨e⟩⟩ := ht
      let : Fact r.Prime := ⟨hr.1⟩
      exact (not_injective_prime_linear hZ hn hm hr.1 (by omega)
        ⟨ZMod r,inferInstance,inferInstance,Nat.card_zmod r,⟨e⟩⟩ i hi).elim
  have hKCeq : K=C := by
    have he := congrArg (Subgroup.map C.subtype) heq
    simpa only [map_subgroupOf_eq_of_le hKC,←MonoidHom.range_eq_map,range_subtype] using he
  simpa only [hKCeq] using hC

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
