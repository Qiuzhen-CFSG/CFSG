module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# The original A₃ block centralizer product

The intrinsic quotient has order three, so C.1.8 identifies O₂(K)=U.
This U is itself Sylow. Every U-fixer has displacement in U and fixes
that actual Sylow, so odd-index averaging gives an inner displacement.

Source: Aschbacher–Smith, C.5.6(7), printed p.159 (the cubic case of C.1.13).
-/
public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem cubic_core_eq_module (hA : IsAlternatingBlock K 3) : K.pCoreIn 2 = U K := by
  obtain ⟨τ,⟨m⟩,_⟩ := hA.2.2
  have hcard : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr m.quotientIso.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact congrArg (map K.subtype) (hA.2.1.core_eq_blockU_of_quotient_three hcard)

theorem cubic_module_fixer_le (hA : IsAlternatingBlock K 3) :
    normalizer (K : Set G) ⊓ centralizer (U K : Set G) ≤ U K ⊔ centralizer (K : Set G) := by
  obtain ⟨τ,⟨m⟩,_⟩ := hA.2.2
  have hcard : Nat.card (K ⧸ pCore 2 K) = 3 := by
    rw [Nat.card_congr m.quotientIso.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcore := hA.2.1.core_eq_blockU_of_quotient_three hcard
  let := hA.2.1.elementary
  let : IsElementaryAbelian 2 (U K) := IsElementaryAbelian.map K.subtype
  have hindex : ¬ 2 ∣ (blockU K).index := by
    change ¬ 2 ∣ Nat.card (K ⧸ blockU K)
    rw [← hcore,hcard]
    decide
  let T : Sylow 2 K := (IsElementaryAbelian.isPGroup 2 (blockU K)).toSylow hindex
  have hKU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  let P := normalizer (K : Set G) ⊓ centralizer (U K : Set G)
  have hd : ⁅K,P⁆ ≤ U K := block_fixer_displacement hA.2.1 inf_le_left inf_le_right
  intro c hc
  obtain ⟨u,hu,huc⟩ := fixed_coset_of_sylow K (U K) hKU
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) T c
    (fun k hk => hd (commutator_mem_commutator hk hc)) (fun k hk =>
      hc.2 k (mem_map_of_mem K.subtype hk))
  have hh : u⁻¹*(u*c) ∈ U K ⊔ centralizer (K : Set G) :=
    mul_mem_sup ((U K).inv_mem hu) huc
  simpa only [inv_mul_cancel_left] using hh
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
