module
public import Theory.SpecificGroups.Alternating.FiveSquareBorelNormalizer
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.FourSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Source

/-!
# The original normalizer in the symmetric-five wreath branch

The actual quotient Mc/O₂(Mc) contains its normal A₅ square. The original
outside H is solvable and its two-core quotient has order 72 by 14.6.12.
The square's Sylow normalizer has order 1152, forcing the H-image to be
that full normalizer and its two-core to be the square's Sylow subgroup.
This subgroup is weakly closed in the quotient Sylow, and both assertions
lift through O₂(Mc) to the original Q_H and H.

For S = N_T(H₁), the earlier source gives Q_H ≤ S ≤ T and N_H(S) = T.
Weak closure then gives N_Mc(S) = T, with the original index two retained.
No normalizer, weak-closure, parabolic-marking or suitability premise is
assumed. FourClosureChoice applies this branch to the original support.
The other strict-closure models and the complete 14.6.14--16 assembly
remain with qt-e-suitable-odd-normalizer; earlier primitive and exchanged
inputs retain qt-e-quintic-recognition and qt-e-14612-singleton.

Source: Aschbacher--Smith 14.6.14(3), 14.6.16, printed pp.1033,1035.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
variable {G : Type*} [Group G] [Finite G]
local notation "A5" => alternatingGroup (Fin 5)
local notation "W5" => RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

private theorem pair_control : SolvableSylowControl 2 (A5 × A5) := by
  have hm : ClassicalGroup.IsPSL A5 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
      ⟨Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
    exact GaloisField.card 2 2 (by decide)
  intro S B hs hSB
  let : Group.IsSolvable (B ⊔ (S : Subgroup (A5 × A5)) : Subgroup (A5 × A5)) := by
    rw [sup_eq_left.mpr hSB]
    exact hs
  exact Chapter1.XiEmbedding.SwappedSylow.binary_model_prod_le_normalizer (by decide) hm S B

/-- The S₅ wreath quotient determines the original core normalizer and its
weak closure in the given Sylow. No parabolic marking is assumed. -/
theorem four_closure_core_normalizer
    (T : Sylow 2 G) {H Mc : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hHsol : Group.IsSolvable H)
    (hcard : Nat.card (H ⧸ pCore 2 H) = 72)
    (eW : (Mc ⧸ pCore 2 Mc) ≃* W5) :
    Mc ⊓ normalizer (H.pCoreIn 2 : Set G) = H ∧
      ∀ g ∈ Mc, (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  obtain ⟨N,hN,⟨eN⟩⟩ := Theory.AlternatingFive.wreath_normal_square eW
  let := hN
  have hQcard : Nat.card (Mc ⧸ pCore 2 Mc) = 28800 := by
    rw [Nat.card_congr eW.toEquiv,RegularWreathProduct.card,Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card,Nat.factorial]
  let B := H.subgroupOf Mc
  let eb := subgroupOfEquivOfLe hHMc
  let := hHsol
  have hs : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := eb.toMonoidHom) eb.injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hb : Nat.card (B ⧸ pCore 2 B) = 72 := by
    rw [Nat.card_congr eqb.toEquiv]
    exact hcard
  have hTMc := hTH.trans hHMc
  obtain ⟨hn,hw⟩ := Theory.AlternatingFive.square_cover_solvable_overgroup q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    N eN hQcard (SolvableSylowControl.of_equiv eN pair_control)
    (T.subtype hTMc) B (fun _ hx => hTH hx) hs hb
  have hC : B.pCoreIn 2 = (H.pCoreIn 2).subgroupOf Mc := pCoreIn_subgroupOf 2 H Mc hHMc
  have hCMc : H.pCoreIn 2 ≤ Mc := (pCoreIn_le 2 H).trans hHMc
  have hCG : (B.pCoreIn 2).map Mc.subtype = H.pCoreIn 2 := by
    rw [hC,map_subgroupOf_eq_of_le hCMc]
  refine ⟨?_,?_⟩
  · rw [hC,←subgroupOf_normalizer_eq hCMc] at hn
    have hh := congrArg (map Mc.subtype) hn
    change ((normalizer (H.pCoreIn 2 : Set G)).subgroupOf Mc).map Mc.subtype =
      (H.subgroupOf Mc).map Mc.subtype at hh
    simpa only [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hHMc,inf_comm] using hh
  · intro g hg hle
    let t : Mc := ⟨g,hg⟩
    have hconj : ((B.pCoreIn 2).map (MulAut.conj t).toMonoidHom).map Mc.subtype =
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
      rw [map_map,←hCG,map_map]
      rfl
    have hcT : (B.pCoreIn 2).map (MulAut.conj t).toMonoidHom ≤
        (T.subtype hTMc : Subgroup Mc) := by
      intro x hx
      change (x : G) ∈ (T : Subgroup G)
      exact hle (hconj ▸ mem_map_of_mem Mc.subtype hx)
    have hh := congrArg (map Mc.subtype) (hw t hcT)
    rwa [hconj,hCG] at hh

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- In the S₅ wreath branch, the literal QH is weakly closed relative to Mc
and its relative normalizer is the original outside H. -/
theorem source_four_core_normalizer
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (eW : (Mc ⧸ pCore 2 Mc) ≃* W5) :
    Mc ⊓ normalizer (H.pCoreIn 2 : Set G) = H ∧
      ∀ g ∈ Mc, (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  exact four_closure_core_normalizer T hH.1.2 hHMc (primitiveResidual_isSolvable H hprim)
    (by simpa using OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 H0 H1 H2 d) eW

/-- Both original 14.6.16 conclusions in the literal S₅ wreath branch.
The normalizer equality and weak closure are proved, rather than supplied. -/
theorem source_normalizer_four_closure_case
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (eW : (Mc ⧸ pCore 2 Mc) ≃* W5) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨hi,hHN,hQS,hTN⟩ := source_exchanged_normalizer_initial
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  obtain ⟨hQ,hw⟩ := source_four_core_normalizer
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d eW
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  refine ⟨hi,le_antisymm ?_ hTN⟩
  intro g hg
  rw [←hHN]
  refine ⟨?_,hg.2⟩
  rw [←hQ]
  refine ⟨hg.1,mem_normalizer_iff_map_conj_eq.mpr (hw g hg.1 ?_)⟩
  have hn : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hg.2
  exact ((map_mono (f := (MulAut.conj g).toMonoidHom) hQS).trans_eq hn).trans inf_le_left

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
