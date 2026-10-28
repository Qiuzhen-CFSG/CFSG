module

public import Theory.GroupAction.NormalizerGeneratingFixer
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Two maximal Sylow overgroups detect the full automorphism fixer

In a simple group, a nontrivial maximal subgroup of characteristic p is the
full normalizer of its embedded p-core. The ambient centralizer of that core
lies in the core. Two distinct such maximal subgroups containing one Sylow
subgroup generate the group; their cores lie in that Sylow subgroup.
The displacement argument therefore makes the entire Sylow fixer a p-group.

The geometric existence of two distinct maximal Sylow overgroups is explicit.
A proper-overgroup Fitting bound by itself does not supply it. This formulation
separates that geometric input from local characteristic p, as needed in
Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Theory.GroupAction.NormalizerGeneratingFixer
variable {G : Type*} [Group G]

/-- The geometric condition required in addition to local characteristic p. -/
@[expose] def HasTwoMaximalOvergroups (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (S : Sylow p G) (M N : Subgroup G),
    IsCoatom M ∧ IsCoatom N ∧ M ≠ N ∧ (S : Subgroup G) ≤ M ∧ (S : Subgroup G) ≤ N

/-- Simplicity and maximality identify the literal normalizer of the embedded core. -/
theorem normalizer_pCoreIn_eq [IsSimpleGroup G] (p : ℕ) (M : Subgroup G)
    (hM : IsCoatom M) (hM0 : M ≠ ⊥)
    (hc : centralizer (pCore p M : Set M) ≤ pCore p M) :
    normalizer (M.pCoreIn p : Set G) = M := by
  have hQ0 : M.pCoreIn p ≠ ⊥ := by
    intro hQ
    have hcore : pCore p M = ⊥ :=
      (map_eq_bot_iff_of_injective (pCore p M) M.subtype_injective).mp hQ
    have ht : (⊤ : Subgroup M) ≤ ⊥ := by
      intro x _
      rw [← hcore]
      apply hc
      intro y hy
      have hy1 : y = 1 := by simpa [hcore] using hy
      simp [hy1]
    apply hM0
    apply le_bot_iff.mp
    intro x hx
    have h := ht (show (⟨x, hx⟩ : M) ∈ ⊤ from trivial)
    exact congrArg Subtype.val (mem_bot.mp h)
  have hMN : M ≤ normalizer (M.pCoreIn p : Set G) := by
    have h := (pCore p M).le_normalizer_map M.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using h
  apply (hM.le_iff_eq ?_).mp hMN
  intro hn
  have hnormal : (M.pCoreIn p).Normal := normalizer_eq_top_iff.mp hn
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact hQ0 h
  · exact hM.ne_top (top_unique (h ▸ pCoreIn_le p M))

/-- The intrinsic core centralizer bound holds in the whole simple ambient group. -/
theorem centralizer_pCoreIn_le [IsSimpleGroup G] (p : ℕ) (M : Subgroup G)
    (hM : IsCoatom M) (hM0 : M ≠ ⊥)
    (hc : centralizer (pCore p M : Set M) ≤ pCore p M) :
    centralizer (M.pCoreIn p : Set G) ≤ M.pCoreIn p := by
  have hNM := normalizer_pCoreIn_eq p M hM hM0 hc
  intro x hx
  have hxM : x ∈ M := hNM ▸ centralizer_le_normalizer (M.pCoreIn p : Set G) hx
  have hxm : (⟨x, hxM⟩ : M) ∈ centralizer (pCore p M : Set M) := by
    intro y hy
    exact Subtype.ext (hx y (mem_map_of_mem M.subtype hy))
  exact mem_map_of_mem M.subtype (hc hxm)

/-- Every arbitrary Sylow pointwise fixer normalizes the specified maximal overgroup.
No restriction on the order of the automorphism is required. -/
theorem maximal_map_eq_of_fixes_sylow [IsSimpleGroup G] {p : ℕ}
    (S : Sylow p G) (M : Subgroup G) (hM : IsCoatom M) (hM0 : M ≠ ⊥)
    (hSM : (S : Subgroup G) ≤ M)
    (hc : centralizer (pCore p M : Set M) ≤ pCore p M)
    (a : MulAut G) (ha : ∀ x ∈ S, a x = x) : M.map a.toMonoidHom = M := by
  have hMS : M.pCoreIn p ≤ S := by
    have h := pCoreIn_le_sylow M (S.subtype hSM)
    simpa only [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left hSM,
      Sylow.coe_coe] using h
  have h := fixes_normalizer (S : Subgroup G) (M.pCoreIn p) hMS a ha
  rwa [normalizer_pCoreIn_eq p M hM hM0 hc] at h

/-- Two distinct characteristic-p maximal Sylow overgroups control every full Sylow fixer. -/
theorem sylow_fixer_of_two_maximals [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (M N : Subgroup G)
    (hM : IsCoatom M) (hN : IsCoatom N) (hne : M ≠ N)
    (hSM : (S : Subgroup G) ≤ M) (hSN : (S : Subgroup G) ≤ N)
    (hcM : centralizer (pCore p M : Set M) ≤ pCore p M)
    (hcN : centralizer (pCore p N : Set N) ≤ pCore p N) (T : Sylow p G) :
    IsPGroup p (fixingSubgroup (MulAut G) (T : Set G)) := by
  have hM0 : M ≠ ⊥ := by
    intro h
    exact hne ((hM.le_iff_eq hN.ne_top).mp (h ▸ bot_le)).symm
  have hN0 : N ≠ ⊥ := by
    intro h
    exact hne ((hN.le_iff_eq hM.ne_top).mp (h ▸ bot_le))
  have hMS : M.pCoreIn p ≤ S := by
    have h := pCoreIn_le_sylow M (S.subtype hSM)
    simpa only [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left hSM,
      Sylow.coe_coe] using h
  have hNS : N.pCoreIn p ≤ S := by
    have h := pCoreIn_le_sylow N (S.subtype hSN)
    simpa only [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left hSN,
      Sylow.coe_coe] using h
  apply sylow_fixer_isPGroup (S : Subgroup G) S.isPGroup' _ T
  let Q : Bool → Subgroup G := fun b => if b then N.pCoreIn p else M.pCoreIn p
  apply fixer_isPGroup (S : Subgroup G) S.isPGroup' Q
  · intro b
    cases b
    · exact hMS
    · exact hNS
  · intro b
    cases b
    · exact (centralizer_pCoreIn_le p M hM hM0 hcM).trans hMS
    · exact (centralizer_pCoreIn_le p N hN hN0 hcN).trans hNS
  · apply top_unique
    rw [← hM.sup_eq_top_of_ne hN hne]
    apply sup_le
    · have h := le_iSup (fun b => normalizer (Q b : Set G)) false
      simpa only [Q, Bool.false_eq_true, if_false, normalizer_pCoreIn_eq p M hM hM0 hcM] using h
    · have h := le_iSup (fun b => normalizer (Q b : Set G)) true
      simpa only [Q, if_true, normalizer_pCoreIn_eq p N hN hN0 hcN] using h
end Theory.GroupAction.NormalizerGeneratingFixer
