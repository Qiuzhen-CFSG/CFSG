module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Centralizer radicals for a normal cubic section

Let B be normal in H with B/O₂(B) of order three. Let B normalize an
elementary abelian two-subgroup C, with fixed subgroup C_C(B)
equal to Z, where Z is centralized by H and [C,O₂(H)] is contained in Z.
Then C has the same centralizer intersection with O₂(B) and O₂(H).

Set R=C_C(O₂(B)). Relative normality puts [O₂(H),B] inside O₂(B).
The three-subgroups lemma therefore makes [R,B] centralize O₂(H).
A cubic complement in B acts coprimely on R; its fixed subgroup lies in
Z. Coprime decomposition proves that all of R centralizes O₂(H).
No equality of the two cores or prescribed size of Z is needed.

Source application: Aschbacher–Smith, 14.5.21(1) and 14.7.6, printed
pp.1019 and1044–1045, refs/quasithin.pdf. The application retains the
full central factor when comparing the two endpoint actions.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The two cores have the same centralizer intersection on a normalized
binary subgroup whose prescribed fixed subgroup is centralized by the ambient group. -/
theorem cubic_core_centralizer_eq (H B C Z : Subgroup G) [IsElementaryAbelian 2 C]
    (hBH : B ≤ H) (hBN : H ≤ normalizer (B : Set G))
    (hBC : B ≤ normalizer (C : Set G))
    (hcomm : ⁅C,H.pCoreIn 2⁆ ≤ Z)
    (hZ : Z ≤ centralizer (H : Set G))
    (hfixed : C ⊓ centralizer (B : Set G) = Z)
    (hquot : Nat.card (B ⧸ pCore 2 B) = 3) :
    C ⊓ centralizer (B.pCoreIn 2 : Set G) =
      C ⊓ centralizer (H.pCoreIn 2 : Set G) := by
  let Q := H.pCoreIn 2
  let P := B.pCoreIn 2
  let R := C ⊓ centralizer (P : Set G)
  have hPQ : P ≤ Q := pCoreIn_mono_of_normalizes hBH hBN
  have hNQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hBP : B ≤ normalizer (P : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hBR : B ≤ normalizer (R : Set G) :=
    (le_inf hBC (hBP.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hQB : ⁅Q,B⁆ ≤ P := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 hBH)
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 H).trans hBN)
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hBH.trans hNQ)
  have h₁ : ⁅⁅R,Q⁆,B⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono inf_le_left le_rfl).trans hcomm).trans
        (hZ.trans (centralizer_le hBH)))
  have h₂ : ⁅⁅Q,B⁆,R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hQB.trans (le_centralizer_iff.mp (inf_le_right : R ≤ centralizer (P : Set G))))
  have hm : ⁅R,B⁆ ≤ centralizer (Q : Set G) := by
    have ht := commutator_commutator_eq_bot_of_rotate h₁ h₂
    rw [commutator_comm B R] at ht
    exact commutator_eq_bot_iff_le_centralizer.mp ht
  obtain ⟨x,hx,hgen⟩ := exists_prime_order_sup_pCore_eq_top
    (G := B) (by decide : Nat.Coprime 2 3) hquot
  let A := (zpowers x).map B.subtype
  have hAB : A ≤ B := map_subtype_le _
  have hBPgen : A ⊔ P = B := by
    have hh := congrArg (map B.subtype) hgen
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,A,P,pCoreIn] using hh
  have hfixedR : R ⊓ centralizer (A : Set G) ≤ Z := by
    intro r hr
    apply hfixed.le
    refine ⟨hr.1.1,?_⟩
    have hrc : zpowers r ≤ centralizer (B : Set G) := by
      apply le_centralizer_iff.mp
      rw [←hBPgen]
      exact sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hr.2))
        (le_centralizer_iff.mp (zpowers_le.mpr hr.1.2))
    exact hrc (mem_zpowers r)
  have hR2 : IsPGroup 2 R := (IsElementaryAbelian.isPGroup 2 C).to_le inf_le_left
  have hA3 : IsPGroup 3 A := by
    apply IsPGroup.of_card (n := 1)
    rw [card_map_of_injective B.subtype_injective,Nat.card_zpowers,hx,pow_one]
  have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide) A R hA3 hR2
  let : Group.IsNilpotent R := hR2.isNilpotent
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime R A
    (hAB.trans hBR) inferInstance hcop
  apply le_antisymm ?_ (inf_le_inf_left C (centralizer_le hPQ))
  refine le_inf inf_le_left ?_
  change R ≤ centralizer (Q : Set G)
  rw [hsplit]
  exact sup_le ((commutator_mono le_rfl hAB).trans hm)
    (hfixedR.trans (hZ.trans (centralizer_le (pCoreIn_le 2 H))))
end Subgroup
