module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.OddFields
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalDiagram
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ThreeRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# The terminal symplectic component branch

The binary derived subgroup embeds in every characteristic-two symplectic
model, so the component quotient has three-rank at least two and the source
rank bound forces relative normality. Odd nonbinary degrees are excluded by
the original-action Borel argument. In even degree, the actual Borel has
three-rank at least two; its lift lies in M by 14.6.18, contradicting the
three-rank-one bound on M intersect K.

Thus the defining field is binary. The explicit derived symplectic
identification gives A₆, and the original Sylow action exchanges its two
parabolics. The final consumer keeps H=Mc. Original 14.6.18 remains with
qt-e-14625-source; the other component rows and natural support assembly
remain with qt-e-suitable-component-supports.

Source: Aschbacher--Smith 14.6.20, printed p.1037, and the Borel calculation
in 15.3.49, p.1144.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The three-rank of the actual derived carrier forces relative normality. -/
theorem source_component_sp_four_normal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hm : IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    (K.subgroupOf H).Normal := by
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_equiv 3 eF]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
  exact (normal_subgroupOf_iff_le_normalizer hKH).mpr
    (source_component_normal_of_quotient_threeRank hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hr)

omit hab in
/-- An even-degree symplectic Borel contradicts the literal overlap rank bound. -/
theorem source_component_not_even_sp_four
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 2 ≤ f) (he : Even f) :
    ¬ IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  let eK := eF.trans (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two hlarge)
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  have hplaced := source_component_sylow_normalizer_le_image T M hsolv H hH.1 K hKH hK eK P hP
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hu := (primeRank_mono 3 hplaced).trans
    (source_component_overlap_image_threeRank_le_one hG T hempty hM hunique hmany hcard e
      H hH K hKH q (hk.symm ▸ pCore_isPGroup))
  have hl := Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.two_le_normalizer_threeRank
    hF (by omega) he Pq
  change primeRank 3 (normalizer (Pq : Set (Theory.SpecificGroups.SymplecticFour.Sp F))) ≤ 1 at hu
  omega

/-- Both parity branches force the original defining degree to be one. -/
theorem source_component_sp_four_degree_one
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) (hm : IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) : f = 1 := by
  by_contra he
  have hn := source_component_sp_four_normal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hm
  rcases Nat.even_or_odd f with heven | hodd
  · exact source_component_not_even_sp_four hG T hempty hM hunique hmany hcard e hsolv
      H hH K hKH hK (by omega) heven hm
  · exact source_normal_component_not_odd_sp_four hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn (by omega) hodd hm

/-- Identify the original two-core quotient with the actual six-point alternating group. -/
theorem source_component_sp_four_alternating_six
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) (hm : IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  have he := source_component_sp_four_degree_one hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hf hm
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  have htwo : Nat.card F = 2 := by simpa only [he,pow_one] using hF
  exact ⟨eF.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix htwo)⟩

/-- The recognized quotient has a genuine parabolic exchange under the original Sylow action. -/
theorem source_component_sp_four_diagram
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) (hm : IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    ∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      ∃ hn : H ≤ normalizer (K : Set G),
        QuotientParabolicSwap T K (hH.1.2.trans hn) eK := by
  obtain ⟨eK⟩ := source_component_sp_four_alternating_six hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hf hm
  exact ⟨eK,source_a6_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK eK⟩

/-- Apply the entire symplectic branch at the unchanged terminal Mc. -/
theorem terminal_component_sp_four_diagram
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) (hm : IsSp4DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    ∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      ∃ hn : Mc ≤ normalizer (K : Set G),
        QuotientParabolicSwap T K
          ((terminal_outside hG T hempty hM hunique hmany hcard e).1.2.trans hn) eK :=
  source_component_sp_four_diagram hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hf hm

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
