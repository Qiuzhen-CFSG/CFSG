module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelAction
public import Theory.GroupTheory.Commutator.ReciprocalFixedPoints
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer

/-!
# The full second-kernel quotient: fixed cosets and exact dual cardinality

Reciprocal full movement removes every fixed coset.  The original central
binary commutator pairing identifies the full quotient with the dual of
the original span modulo its actual core centralizer.  Its exact cardinal
identity bounds this quotient by32, without bounding the full kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The original full quotient has no fixed coset, the exact binary-dual
cardinality, and order between sixteen and thirty-two. -/
theorem source_quintic_second_kernel_fixed_and_dual_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let UH := conjugateSpanBy (localModule T M) H
    let QH := H.pCoreIn 2
    let C := H ⊓ centralizer (UH : Set G)
    commutatorPreimage QH H C = C ∧
      ∃ hN : (C.subgroupOf QH).Normal,
        letI := hN
        IsElementaryAbelian 2 (QH ⧸ C.subgroupOf QH) ∧
          Nat.card (QH ⧸ C.subgroupOf QH) *
            Nat.card (UH ⊓ centralizer (QH : Set G) : Subgroup G) = Nat.card UH ∧
          16 ≤ Nat.card (QH ⧸ C.subgroupOf QH) ∧
          Nat.card (QH ⧸ C.subgroupOf QH) ≤ 32 := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let Z := centralInvolutions T
  let E := U ⊓ centralizer (Q : Set G)
  obtain ⟨hCQ,hN,hE,α,hker,hnot,hlo,hα⟩ :=
    source_quintic_faithful_second_kernel_action hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let := hE
  obtain ⟨hel,hUcard⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 U := hel
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hQH : Q ≤ H := pCoreIn_le 2 H
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hfull : U = ⁅U,H⁆ := by
    obtain ⟨g,hg,hDQ,hne,hVI,hTI,hprod,hcomm,hfull⟩ :=
      source_quintic_middle_core_product hG T hempty hM hu hmany hcard e H hH hi
    exact hfull
  have hcomm : ⁅U,Q⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hZH : Z ≤ centralizer (H : Set G) := le_centralizer_iff.mp
    (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hQC : Q ⊓ centralizer (U : Set G) = C :=
    le_antisymm (inf_le_inf_right _ hQH) (le_inf hCQ inf_le_right)
  have hfix : commutatorPreimage Q H C = C := by
    have hh := fixed_preimage_eq_of_reciprocal_centralizer H U Q C Z hHQ hHC
      (hQH.trans hHC) (by rw [inf_eq_right.mpr hCQ,hQC]) hcomm.le hZH hfull.symm
    exact hh.trans (inf_eq_right.mpr hCQ)
  obtain ⟨ρ,sU,sQ,hpair,hmark⟩ := BinaryConjugationSection.exists_central_duality
    H Q U Z hQH (hUQ.trans hQH) hHQ hHU (hZU.trans hUQ) hZH
    (by rw [commutator_comm]; exact hcomm.le) hZcard
  rw [hQC] at sQ
  let A := Additive (U ⧸ E.subgroupOf U)
  have hWcard : Nat.card (Q ⧸ C.subgroupOf Q) = Nat.card A := by
    have hh := Nat.card_congr sQ.quotientEquiv.toEquiv
    change Nat.card (Q ⧸ C.subgroupOf Q) = Nat.card (Module.Dual (ZMod 2) A) at hh
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) A),
      Subspace.dual_finrank_eq,←Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)] at hh
    exact hh
  have hpaircard : Nat.card (Q ⧸ C.subgroupOf Q) * Nat.card E = Nat.card U := by
    rw [hWcard]
    exact sU.card_section.symm
  have hZle : Z ≤ E := le_inf hZU (hZH.trans (centralizer_le hQH))
  have hElo : 2 ≤ Nat.card E := hZcard ▸ card_le_of_le hZle
  change Nat.card U = 32 ∨ Nat.card U = 64 at hUcard
  have hUhi : Nat.card U ≤ 64 := by rcases hUcard with h | h <;> omega
  have hhi : Nat.card (Q ⧸ C.subgroupOf Q) ≤ 32 := by nlinarith
  exact ⟨hfix,hN,hE,hpaircard,hlo,hhi⟩

end CFSG.Quasithin.Chapter14.Section06
