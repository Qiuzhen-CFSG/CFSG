module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DecompositionConsequences
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralDegree.Actions
import Mathlib.Tactic.LinearCombination

/-!
# Linear algebra for the classified-action centralizer

A commuting endomorphism preserves the actual displacement span. The
inclusion-preserving internal space coordinates and `cross_fix` then show
that each factor acts faithfully on its own displacement summand. Equality
on those summands is equality on the whole module.

An involution on a nonzero binary module has a nonzero fixed vector. If
every nonzero invariant subspace has the full dimension, its fixed space
is the whole module. This reduces the small centralizer calculations to
lower bounds on invariant subspaces.

These are the centralizer steps used in the equality induction of
Aschbacher--Smith G.9.2, printed pp.352--353.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

open DihedralDegree

universe v

variable {G : Type*} [Group G] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

private theorem binary_add_self (w : W) : w + w = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ w
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [hz, zero_smul] at h
  exact h.symm

private theorem involution_fixed_nonzero [Nontrivial W]
    (t : Module.End (ZMod 2) W) (ht : t*t=1) :
    ∃ w : W, w ≠ 0 ∧ t w = w := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  by_cases h : t w = w
  · exact ⟨w, hw, h⟩
  · refine ⟨t w + w, ?_, ?_⟩
    · intro he
      apply h
      have hh := binary_add_self w
      linear_combination (norm := abel) he - hh
    · have htt : t (t w) = w := congrArg (fun f : Module.End (ZMod 2) W => f w) ht
      rw [map_add, htt, add_comm]

theorem involution_eq_one_of_subspace_bound [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) G W)
    (hbound : ∀ U : Submodule (ZMod 2) W, U ≠ ⊥ →
      (∀ g, U ≤ U.comap (σ g)) → Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) U)
    (t : Module.End (ZMod 2) W) (ht : t*t=1) (hc : ∀ g, Commute t (σ g)) : t=1 := by
  cases subsingleton_or_nontrivial W with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    obtain ⟨w, hw, htw⟩ := involution_fixed_nonzero t ht
    let U := LinearMap.ker (t-1)
    have hU : U ≠ ⊥ := by
      intro he
      have hm : w ∈ U := by simpa [U, LinearMap.mem_ker, sub_eq_zero] using htw
      rw [he, Submodule.mem_bot] at hm
      exact hw hm
    have hstable (g : G) : U ≤ U.comap (σ g) := ker_sub_one_stable _ _ (hc g).symm
    have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq
      (Nat.le_antisymm (Submodule.finrank_le _) (hbound U hU hstable))
    ext w
    have hm : w ∈ U := by rw [htop]; trivial
    exact sub_eq_zero.mp hm

theorem movedSpace_stable_of_commuting_end
    (ρ : Representation (ZMod 2) G W) (K : Subgroup G)
    (t : Module.End (ZMod 2) W) (hc : ∀ g : K, Commute t (ρ g)) :
    movedSpace ρ K ≤ (movedSpace ρ K).comap t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, w⟩, rfl⟩
  change t (ρ g w - w) ∈ movedSpace ρ K
  have hh := congrArg (fun a : Module.End (ZMod 2) W => a w) (hc g).eq
  change t (ρ g w) = ρ g (t w) at hh
  rw [map_sub, hh]
  exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp K.subtype) g (t w)

theorem linearMap_eq_of_internal_summands {ρ : Representation (ZMod 2) G W}
    {H : Subgroup G} {r : ℕ} (d : InternalDecomposition ρ H r)
    {f g : Module.End (ZMod 2) W}
    (he : ∀ i (w : movedSpace ρ (d.factor i)), f w = g w) : f = g := by
  ext w
  obtain ⟨v, rfl⟩ := d.spaceEquiv.surjective w
  rw [← Finset.univ_sum_single v, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [d.space_inclusion]
  exact he i (v i)

theorem internal_factor_faithful {ρ : Representation (ZMod 2) G W}
    {H : Subgroup G} {r : ℕ} (d : InternalDecomposition ρ H r)
    (hf : Function.Injective (ρ.comp H.subtype)) (i : Fin r) :
    Function.Injective (Representation.subrepresentation (ρ.comp (d.factor i).subtype)
      (movedSpace ρ (d.factor i)) (coinvariants_stable (ρ.comp (d.factor i).subtype))) := by
  intro g h he
  have hh : ρ g = ρ h := by
    apply linearMap_eq_of_internal_summands d
    intro j w
    by_cases hij : i = j
    · subst j
      exact congrArg Subtype.val (congrArg
        (fun f : Module.End (ZMod 2) (movedSpace ρ (d.factor i)) => f w) he)
    · rw [d.cross_fix hij g w, d.cross_fix hij h w]
  have hh' : (⟨g.val, d.factor_le i g.property⟩ : H) = ⟨h.val, d.factor_le i h.property⟩ := hf hh
  exact Subtype.ext (congrArg (fun z : H => (z : G)) hh')

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
