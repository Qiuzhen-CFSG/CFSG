module

public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedRecognition
public import BenderSuzuki.SE.BorelLifting
public import BenderSuzuki.SE.StrongEmbeddingConjugacy
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification.DerivedQuotient

/-!
# The normal closure and Sylow omega conclusion of I.8.5

The Borel in the odd-core quotient lifts to the original local subgroup.
It is strongly embedded, so all involutions of the normal closure are
conjugate. The unique-fixed-coset transporter forces its involutions lying
in M into V. Thus V is exactly the first omega subgroup of the actual
Sylow subgroup in that Borel, and M intersect L is its Borel normalizer.

This completes the structural alternative I.8.5(1) from the source
hypotheses. The induced-automorphism solvability in I.8.5(2) is separate.
Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed p.430.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterI.Section06To08
open Theory.GroupTheory BenderSuzuki PFAppendixIII PFchapter1section1 Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem involution_mem_of_unique_fixed_cosets
    {V M L : Subgroup G} (hVM : V ≤ M) (hVL : V ≤ L) (hVne : V ≠ ⊥)
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G))
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q)
    (hN : BenderSuzuki.IsStronglyEmbedded (M.comap L.subtype))
    (x : L) (hxM : (x : G) ∈ M) (hx : BenderSuzuki.PFAppendixIII.IsInvolution x) : (x : G) ∈ V := by
  obtain ⟨⟨v, hv⟩, hne⟩ := ne_bot_iff_exists_ne_one.mp hVne
  let z : L := ⟨v, hVL hv⟩
  have hz : BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨fun he => hne (Subtype.ext (congrArg (fun y : L => (y : G)) he)),
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v hv)⟩
  obtain ⟨g, hg⟩ := hN.involutions_conjugate hz hx
  have he : (g : G)⁻¹ * v * (g : G) = (x : G) := congrArg Subtype.val hg
  have hconj : (g : G)⁻¹ * v * (g : G) ∈ V := by
    simpa only [inv_inv] using
      conj_mem_of_unique_fixed_cosets hVM hn hfix (g := (g : G)⁻¹) hv
        (by simpa only [inv_inv, he] using hxM)
  exact he ▸ hconj

/-- The full structural alternative I.8.5(1): the original normal closure
is either O(L)V with V of order two, or quasisimple with simple Bender
central quotient, the original Borel, and the actual Sylow omega subgroup. -/
public theorem lemma_I_8_5_structure
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    let L := normalClosure (V : Set G)
    let N := M.comap L.subtype
    (Nat.card V = 2 ∧ pPrimeCore 2 L ⊔ V.subgroupOf L = ⊤) ∨
      (IsQuasisimple L ∧ BenderSuzuki.IsSimpleBenderGroup (L ⧸ center L) ∧
        N = normalizer (V.subgroupOf L : Set L) ∧ IsBorelSubgroup N ∧
        ∃ S : Sylow 2 L, (S : Subgroup L) ≤ N ∧
          V.subgroupOf L = (omega₁ S (p := 2)).map (S : Subgroup L).subtype) := by
  rcases lemma_I_8_5_oddCore_recognition V M hVM hVne hproper hfix with
    hr | ⟨hquasi, hmodel, hcent, hO, hB⟩
  · exact Or.inl hr
  · right
    let L := normalClosure (V : Set G)
    let O := pPrimeCore 2 L
    let N := M.comap L.subtype
    let q : L →* L ⧸ O := QuotientGroup.mk' O
    have hqker : q.ker = O := QuotientGroup.ker_mk' O
    have hBorel : IsBorelSubgroup N :=
      IsBorelSubgroup.of_central_kernel q (QuotientGroup.mk'_surjective O)
        (by rw [hqker]; exact hcent.le) N (by rw [hqker]; exact hO) hB
    have hStrong : BenderSuzuki.IsStronglyEmbedded N :=
      BenderSuzuki.IsStronglyEmbedded.of_odd_quotient O N hO
        (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := L) (p := 2)))
        (ZD.LocalDerivedQuotient.borel_stronglyEmbedded hmodel hB)
    have hVL : V ≤ L := le_normalClosure
    have hn : M ≤ normalizer (V : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hVM).mp inferInstance
    have hnEq := normalizer_eq_of_unique_fixed_cosets hVM hVne hn hfix
    have hNEq : N = normalizer (V.subgroupOf L : Set L) := by
      change M.subgroupOf L = _
      rw [← subgroupOf_normalizer_eq hVL, hnEq]
    refine ⟨hquasi, hmodel.map_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcent),
      hNEq, hBorel, ?_⟩
    obtain ⟨S, hS⟩ := hBorel.2
    change N = normalizer (S : Set L) at hS
    have hSN : (S : Subgroup L) ≤ N := hS.symm ▸ (S : Subgroup L).le_normalizer
    let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
    have hVS : V.subgroupOf L ≤ (S : Subgroup L) := by
      have h := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf L)).inf_normalizer_sylow S
      rw [← hS, inf_eq_left.mpr (show V.subgroupOf L ≤ N from fun _ hv => hVM hv)] at h
      exact inf_eq_left.mp h.symm
    refine ⟨S, hSN, le_antisymm ?_ ?_⟩
    · intro v hv
      refine ⟨⟨v, hVS hv⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      change (⟨v, hVS hv⟩ : S) ^ (2 ^ 1) = 1
      apply Subtype.ext
      change v ^ 2 = 1
      exact elemPow_eq_one_of_isElementaryAbelian v hv
    · apply map_le_iff_le_comap.mpr
      change closure {x : S | x ^ (2 ^ 1) = 1} ≤ _
      apply (closure_le _).mpr
      intro x hx
      change x ^ (2 ^ 1) = 1 at hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · have hxI : BenderSuzuki.PFAppendixIII.IsInvolution x :=
          ⟨hx1, by simpa only [pow_one] using hx⟩
        exact involution_mem_of_unique_fixed_cosets hVM hVL hVne hn hfix hStrong x
          (hSN x.property) (BenderSuzuki.IsInvolution.map_of_injective hxI (S : Subgroup L).subtype
            Subtype.val_injective)

end CFSG.Quasithin.ChapterI.Section06To08
