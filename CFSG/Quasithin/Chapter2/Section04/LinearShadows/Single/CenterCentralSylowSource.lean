module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import Theory.GroupTheory.NormalizedCentralizerSylow

/-!
# The original Sylow subgroup in the module normalizer and center centralizer

The original 2.4.3 puts S in Sylow₂(N_G(O₂(H))), while 2.4.8 identifies
O₂(H) with the actual natural module U. The distinguished subgroup Z is
normalized by S. Restricting the Sylow subgroup to its relative centralizer
therefore makes C_S(Z) Sylow in N_G(U) ∩ C_G(Z). The source kernel identity
C_S(Z) = R completes the required literal statement in both branches of Z.

Source: Aschbacher–Smith, proof of Lemma 2.4.21, printed p.536,
using Lemmas 2.4.3(1), 2.4.8(2), 2.4.16(1) and 2.4.17(1).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original R is Sylow in the literal N_G(U) ∩ C_G(Z), as used in the
centralizing-involution exclusion of original 2.4.21. -/
theorem source_module_normalizer_center_centralizer_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    let U := sourceModule (d.block.map d.H.subtype)
    let K := normalizer (U : Set G) ⊓ centralizer (distinguishedZ d : Set G)
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let U := sourceModule (d.block.map d.H.subtype)
  have hU : U = twoCore d.H := (lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  obtain ⟨_,_,P,hP⟩ := lemma_2_4_3_1 hG.evenCharacteristic hMe d.mem_gammaEvenZero d.full_pair d.S le_rfl
  have hSZ : S ≤ normalizer (distinguishedZ d : Set G) :=
    (source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique).2.2.2
  have hCS := source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique
  dsimp only
  change sourceModule (d.block.map d.H.subtype) = _ at hU
  rw [hU]
  obtain ⟨Q,hQ⟩ := Subgroup.exists_sylow_centralizer_of_normalizes _ S (distinguishedZ d) P hP hSZ
  exact ⟨Q,hQ.trans hCS⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
