module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Core

/-!
# Abelian invariant subgroups of the highest-root radical

An element of the five-root radical commutes with its root-F conjugate only
if its fourth noncentral coordinate vanishes. The short Weyl reflection
kills the opposite coordinate. Conjugation by root-F with parameters one
and a parameter outside the prime field then kills the middle coordinates.
Thus every abelian subgroup of the radical normalized by the full first
local group lies in the highest-root group, for every even field of order
larger than two. No binary irreducibility or chief-factor count is assumed.

This is the radical-action obstruction used for the G₂(4) central-cover
case in Aschbacher–Smith 14.7.68(2), printed p.1071, with the local convention
of F.1.11–12, printed pp.262–264. Root coordinates use the licensed ATLAS
port (LICENSES/ATLAS.txt; LICENSES/ATLAS-CITATION.cff).
-/

public section

open Atlas.G2 Atlas.G2.Explicit
open scoped commutatorElement
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

theorem rootF_fiveRoot_conjugate (s : F) (t : Fin 6 → F) (ht : t 5 = 0) :
    rootF s * unipotentProduct t * (rootF s)⁻¹ =
      unipotentProduct ![t 0 + t 3 ^ 2 * s + t 3 * t 4 * s ^ 2 + t 4 ^ 2 * s ^ 3,
        t 1 + t 2 * s + t 3 * s ^ 2 + t 4 * s ^ 3,
        t 2 + t 4 * s ^ 2, t 3 + t 4 * s, t 4, 0] := by
  have hf : rootF s = unipotentProduct ![0,0,0,0,0,s] := by simp [unipotentProduct]
  rw [hf, unipotentProduct_inv, unipotentProduct_mul, unipotentProduct_mul]
  congr 1
  ext i
  fin_cases i <;> simp [unipotentProductParameters, unipotentInverseParameters, ht,
    CharTwo.neg_eq, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod]

theorem fiveRoot_commutator_rootF_conjugate (t : Fin 6 → F) (ht : t 5 = 0) :
    ⁅unipotentProduct t, rootF 1 * unipotentProduct t * (rootF 1)⁻¹⁆ =
      rootA (t 4 ^ 2) := by
  rw [rootF_fiveRoot_conjugate 1 t ht, fiveRoot_commutator t _ ht rfl]
  congr 1
  simp [CharTwo.neg_eq, CharTwo.sub_eq_add, CharTwo.ofNat_eq_mod]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

theorem abelian_normalized_radical_le_highestRoot [Finite F] (hq : 2 < Nat.card F)
    (B : Subgroup (Model F)) (hB : B ≤ radical₁)
    (hn : local₁ ≤ Subgroup.normalizer (B : Set (Model F)))
    (hab : ∀ x ∈ B, ∀ y ∈ B, Commute x y) : B ≤ highestRoot := by
  have hF (s : F) : rootF s ∈ local₁ (F := F) :=
    unipotent_le_local₁ (Subgroup.subset_closure (by simp))
  have hS : (weylS : Model F) ∈ local₁ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hconj (g : Model F) (hg : g ∈ local₁) (x : Model F) (hx : x ∈ B) :
      g * x * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hn hg) x).mp hx
  have kill4 (t : Fin 6 → F) (ht : t 5 = 0) (hb : unipotentProduct t ∈ B) : t 4 = 0 := by
    have hc := (hab _ hb _ (hconj _ (hF 1) _ hb)).commutator_eq
    rw [fiveRoot_commutator_rootF_conjugate t ht] at hc
    have hz := rootA_injective (hc.trans (rootA_zero (K := F)).symm)
    exact (sq_eq_zero_iff).mp hz
  have kill1 (t : Fin 6 → F) (ht : t 5 = 0) (hb : unipotentProduct t ∈ B) : t 1 = 0 := by
    have hs := hconj _ hS _ hb
    rw [weylS_fiveRoot_conjugate t ht] at hs
    exact kill4 _ rfl hs
  classical
  let := Fintype.ofFinite F
  have hcard : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hs' : s ≠ 0 ∧ s ≠ 1 := by simpa using hs
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hB hx
  have h4 := kill4 t ht hx
  have h1 := kill1 t ht hx
  have he (r : F) : t 2 * r + t 3 * r ^ 2 = 0 := by
    have hr := hconj _ (hF r) _ hx
    rw [rootF_fiveRoot_conjugate r t ht] at hr
    simpa [h1, h4] using kill1 _ rfl hr
  have h23 : t 2 + t 3 = 0 := by simpa using he 1
  have h2 : t 2 = t 3 := by
    exact (eq_neg_of_add_eq_zero_left h23).trans (CharTwo.neg_eq _)
  have h3 : t 3 = 0 := by
    have hp : t 3 * s * (s + 1) = 0 := by
      calc
        _ = t 2 * s + t 3 * s ^ 2 := by rw [h2]; ring
        _ = 0 := he s
    have hs1 : s + 1 ≠ 0 := by
      intro hz
      exact hs'.2 ((eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _))
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hs1)).resolve_right hs'.1
  have h2zero : t 2 = 0 := h2.trans h3
  refine ⟨Multiplicative.ofAdd (t 0), ?_⟩
  change rootA (t 0) = unipotentProduct t
  simp [unipotentProduct, h1, h2zero, h3, h4, ht]
end Atlas.G2.LieParabolicSetup
