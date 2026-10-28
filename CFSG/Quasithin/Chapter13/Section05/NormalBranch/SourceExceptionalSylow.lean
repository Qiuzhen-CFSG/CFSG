module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveBlock
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalNormalizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.LocalFamily
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# The original pair in the exceptional centralizer's local family

Put C=C_T(K) and T₀=C_T(C). The actual image of U_H in K/O₂(K)=A₅
has order four, hence its preimage has odd index fifteen in K. Both U_H
and O₂(K)=V lie in T₀. Once the earlier centralizer argument shows that
T₀ normalizes K, the normalized-supplement index theorem makes T₀ Sylow
in KT₀. The original A₅ block then belongs to the literal local family,
including after restriction to C_G(C).

Source: Aschbacher--Smith 13.5.15(7), printed p.920, the assertion
K ∈ L(C_G(D₀),C_T(D₀)) immediately before the application of 1.2.5.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSylow
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬ IsMulCommutative D.UH) (g : D.L)
  (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
  (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
    FivePair.five.map (MulAut.conj a.val).toMonoidHom)
  (hS : (NormalBranch.K D g.val).pCoreIn 2 = D.V)
include d h e hseed hn hU g hK a hi hS

local notation "C₀" => ((D.T : Subgroup G) ⊓ centralizer (NormalBranch.K D g.val : Set G))
local notation "T₀" => ((D.T : Subgroup G) ⊓ centralizer (C₀ : Set G))

/-- The original closure image gives the required Sylow subgroup in KT₀. -/
theorem sylow_pair_join
    (hT0K : T₀ ≤ normalizer (NormalBranch.K D g.val : Set G)) :
    ∃ P : Sylow 2 (NormalBranch.K D g.val ⊔ T₀ : Subgroup G),
      (P : Subgroup (NormalBranch.K D g.val ⊔ T₀ : Subgroup G)).map
        (NormalBranch.K D g.val ⊔ T₀).subtype = T₀ := by
  let K := NormalBranch.K D g.val
  let U := D.UH.subgroupOf K
  let f := restrictedActor d hK a hi
  let W := (U.map f).comap f
  have hcard : Nat.card (U.map f) = 4 :=
    SourceCoreProduct.closure_image_card d h e hseed hn hU g hK a hi
  have hindex : (U.map f).index = 15 := by
    have hh := (U.map f).card_mul_index
    rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hWindex : ¬ 2 ∣ W.index := by
    rw [show W.index = (U.map f).index from
      (U.map f).index_comap_of_surjective (restrictedActor_surjective d hK a hi),hindex]
    decide
  have hKC : K ≤ centralizer (C₀ : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  have hUC : D.UH ≤ T₀ :=
    le_inf (h.UH_le_QH.trans h.QH_le_T) (le_sup_left.trans hKC)
  have hVC : D.V ≤ T₀ :=
    le_inf h.V_le_T ((hS ▸ pCoreIn_le 2 K).trans hKC)
  have hW : W.map K.subtype ≤ T₀ := by
    rw [show W = U ⊔ f.ker from comap_map_eq f U,
      Subgroup.map_sup,restrictedActor_ker_eq_twoCore d hK a hi e,
      map_subgroupOf_eq_of_le (show D.UH ≤ K from le_sup_left)]
    exact sup_le hUC (hS.le.trans hVC)
  exact (D.T.isPGroup'.to_le inf_le_left).exists_sylow_sup_of_coprime_index
    K T₀ hT0K W hWindex hW

/-- The actual five-letter block is a member of L(G,T₀). -/
theorem pair_mem_local_family
    (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (hT0K : T₀ ≤ normalizer (NormalBranch.K D g.val : Set G)) :
    NormalBranch.K D g.val ∈ Chapter1.L G T₀ := by
  have hB := SourceFiveBlock.alternatingBlock d e g hK hp a hi hS
  have h3 : ¬ ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 3 := by
    intro h3
    obtain ⟨e3⟩ := h3.2.2.quotient_iso
    have hh := Nat.card_congr ((quotientEquiv d hK a hi e).symm.trans e3).toEquiv
    simp only [nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
  obtain ⟨P,hP⟩ := sylow_pair_join d h e hseed hn hU g hK a hi hS hT0K
  exact ChapterC.Section05.NormalizerControl.noncubic_mem_local_family
    _ _ (Or.inr (Or.inr hB)) h3 hT0K P hP

/-- Restriction gives the literal source local component inside C_G(C). -/
theorem pair_mem_centralizer_local_family
    (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (hT0K : T₀ ≤ normalizer (NormalBranch.K D g.val : Set G)) :
    (NormalBranch.K D g.val).subgroupOf (centralizer (C₀ : Set G)) ∈
      Chapter1.L (centralizer (C₀ : Set G))
        ((T₀).subgroupOf (centralizer (C₀ : Set G))) := by
  have hKC : NormalBranch.K D g.val ≤ centralizer (C₀ : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  exact (Chapter1.mem_LIn_iff_subgroupOf inf_le_right hKC).mp
    ⟨hKC,pair_mem_local_family d h e hseed hn hU g hK a hi hS hp hT0K⟩

/-- The order-two branch supplies the normalization internally, using the
original core split and the already proved C_T(L)=1. -/
theorem exceptional_pair_mem_centralizer_local_family
    (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (hsplit : D.LT.pCoreIn 2 = D.V ⊔ C₀)
    (hCL : (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) = ⊥)
    (hcard : Nat.card (C₀ : Subgroup G) = 2) :
    (NormalBranch.K D g.val).subgroupOf (centralizer (C₀ : Set G)) ∈
      Chapter1.L (centralizer (C₀ : Set G))
        ((T₀).subgroupOf (centralizer (C₀ : Set G))) := by
  exact pair_mem_centralizer_local_family d h e hseed hn hU g hK a hi hS hp
    (SourceExceptionalNormalizer.exceptional_sylow_centralizer_normalizes_pair
      d h e g hK hp a hi hS hsplit hCL hcard)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalSylow
end
