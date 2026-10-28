module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.RadicalCentralizationComplete
public import CFSG.Quasithin.Chapter13.Section01

/-!
# TI and weak closure from the original involution-centralizer analysis

For the literal U=[R₂(N_G(L)),L], radical centralization places Ξ_p(L)
inside every C_M(u). The proved 13.1.11 then makes these centralizers
conjugate-rigid whenever their action on the odd Frattini plane is
irreducible. The centralizer containment of 13.1.12(3) gives TI, and the
fully moved weak-closure theorem applies to every module branch.

The two original 13.1.12 inputs remain explicit; neither a TI assertion nor
a conjugate-rigidity assertion is assumed. The final application uses the
same maximal overgroup of the actual Hypothesis 13.3.1 counterexample.

Source: Aschbacher--Smith, 13.1.11--14, printed pp.872--876.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter3.RadicalCentralization
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal local centralizer action in 13.1.12(1). -/
@[expose] def RadicalCentralizerIrreducible (L : Subgroup G) (p : ℕ) (u : G) : Prop :=
  ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
    (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
      ∀ a ∈ A, xiFrattiniAction
        (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
        (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤

/-- The Sylow-central branch of 13.1.12(1) follows directly from the
canonical radical's original T-irreducibility. -/
theorem radicalCentralizerIrreducible_of_sylow_centralizes
    {T : Sylow 2 G} (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    {u : G} (hTu : (T : Subgroup G) ≤ centralizer ({u} : Set G)) :
    RadicalCentralizerIrreducible L p u := by
  have hQ := uniqueness_local_quotient_sqtk hG hL.2.2
  have hTL := radicalLocal_invariant_source hL hQ hn
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  intro A hA
  apply RadicalActions.XiP_irreducible_of_A36 h36 hL hQ hn hTL ho hd A
  intro t a ha
  exact hA ⟨t,hTL t.property,hTu t.property⟩ a ha

/-- Radical centralization supplies the containment needed by the actual
13.1.11 actor; it is not an additional orbit-analysis premise. -/
theorem XiP_le_moved_centralizer
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (p : ℕ) [Fact p.Prime] {u : G} (hu : u ∈ normalizerMoved L) :
    XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G) := by
  refine le_inf ((XiP_le p L).trans L.le_normalizer) ?_
  exact ((XiP_le_solvableRadical L p).trans
    (solvableRadical_centralizes_normalizerMoved h hmany hL hn)).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hu))

/-- The unique-conjugate theorem for Ξ_p(L) proves the exact centralizer
rigidity used in 13.1.13, with the original conjugating element retained. -/
theorem moved_centralizer_conjugate_rigidity
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    {u : G} (hu : u ∈ normalizerMoved L)
    (hirr : RadicalCentralizerIrreducible L p u)
    (g : G)
    (hg : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)).map
      (MulAut.conj g).toMonoidHom ≤ normalizer (L : Set G)) :
    g ∈ normalizer (L : Set G) ∧
      (normalizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
        normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer ({u} : Set G)
  have hi : C ≤ M.conjBy g⁻¹ := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    change (C.conjBy g).conjBy g⁻¹ ≤ M.conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  obtain ⟨hgi, _⟩ := RadicalConjugateRigidity.maximal_radical_unique_conjugate
    h.simpleQTKE T hL hn ho hd C
    (XiP_le_moved_centralizer h hmany hL hn p hu) inf_le_left hirr g⁻¹ hi
  have hgm : g ∈ M := (M.inv_mem_iff).mp hgi
  exact ⟨hgm,mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hgm)⟩

/-- Original 13.1.13 from the two mathematical centralizer conclusions of
13.1.12. All radical containment and conjugate-rigidity inputs are discharged. -/
theorem normalizerMoved_ti_of_centralizer_analysis
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hirr : ∀ u ∈ normalizerMoved L, u ≠ 1 →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) → RadicalCentralizerIrreducible L p u)
    (hc : ∀ u ∈ normalizerMoved L, u ≠ 1 →
      centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    IsTISubgroup (normalizerMoved L) ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨_,hne,_,hN⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  have hm := (RadicalConjugateRigidity.maximal_radical_structure
    h.simpleQTKE T hL.1 hn ho hd).2.2
  apply ti_and_normalizer_of_centralizer_rigidity hm hne hN.ge hc
  intro u hu hne g hg
  apply (moved_centralizer_conjugate_rigidity h hmany hL.1 hn ho hd hu ?_ g hg).2
  by_cases hTu : (T : Subgroup G) ≤ centralizer ({u} : Set G)
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd hTu
  · exact hirr u hu hne hTu

/-- The centralization and parameter clauses of 13.1.14(1--2), for every
module branch, retain only the two original 13.1.12 centralizer conclusions.
The normalizer bound for W₀ and part (3) remain separate source obligations. -/
theorem normalizerMoved_weakClosure_of_centralizer_analysis
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hirr : ∀ u ∈ normalizerMoved L, u ≠ 1 →
      ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) → RadicalCentralizerIrreducible L p u)
    (hc : ∀ u ∈ normalizerMoved L, u ≠ 1 →
      centralizer ({u} : Set G) ≤ normalizer (L : Set G)) :
    IsTISubgroup (normalizerMoved L) ∧
      (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) i ≤
        centralizer (normalizerMoved L : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved L) := by
  have hTI := (normalizerMoved_ti_of_centralizer_analysis h hmany hL hn ho hd hirr hc).1
  exact ⟨hTI,normalizerMoved_weakClosure_bound_source h hmany hL hn hTI⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
open Chapter13.Section01.SourceNonquasisimple ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The literal nonquasisimple branch of 13.3.2 supplies one maximal
counterexample with the TI, movement, size and weak-closure conclusions
needed by the terminal 13.1.7 argument. Only the original centralizer
analysis is retained for its source producers. -/
theorem Hypothesis1331.nonquasisimple_ti_counterexample_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn0 : ¬ IsQuasisimple (XiQuotient L₀))
    (hcentralizers : ∀ K : Subgroup G, L₀ ≤ K → FaithfulMaximalLocal T K →
      ¬ IsQuasisimple (XiQuotient K) →
      ∀ (p : ℕ) [Fact p.Prime], Odd p →
        p ∣ Nat.card (fittingSubgroup (XiQuotient K)) →
        ∀ u ∈ normalizerMoved K, u ≠ 1 →
          (¬ (T : Subgroup G) ≤ centralizer ({u} : Set G) →
            RadicalCentralizerIrreducible K p u) ∧
            centralizer ({u} : Set G) ≤ normalizer (K : Set G)) :
    ∃ K : Subgroup G, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      ¬ IsQuasisimple (XiQuotient K) ∧
      IsElementaryAbelian 2 (normalizerMoved K) ∧
      ⁅normalizerMoved K,K⁆ = normalizerMoved K ∧
      8 ≤ Nat.card (normalizerMoved K) ∧
      normalizer (normalizerMoved K : Set G) = normalizer (K : Set G) ∧
      IsTISubgroup (normalizerMoved K) ∧
      (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved K) (T : Subgroup G) i ≤
        centralizer (normalizerMoved K : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved K) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved K) := by
  obtain ⟨K,hK,hLK,hf,hkn,_,hjoin,_⟩ := h.maximal_counterexample_of_many hmany hn0
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  obtain ⟨p,hp,ho,_,hd,_⟩ := exists_odd_radical_source h.qtke h36 hkn
  let : Fact p.Prime := ⟨hp⟩
  have hc := hcentralizers K hLK hf hkn.2 p ho hd
  obtain ⟨he,hne,_,hN⟩ := faithful_maximal_normalizer_moved h.qtke hf
    (le_sup_right.trans hjoin)
  obtain ⟨hmoved,hsize⟩ := normalizerMoved_commutator_and_card hK.1 hne
  exact ⟨K,hLK,hf,hkn.2,he,hmoved,hsize,hN,
    normalizerMoved_weakClosure_of_centralizer_analysis h.hypothesis1311 hmany hf hkn.2
      ho hd (fun u hu hne => (hc u hu hne).1) (fun u hu hne => (hc u hu hne).2)⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
