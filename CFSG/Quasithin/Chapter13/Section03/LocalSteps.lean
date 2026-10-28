module

public import CFSG.Quasithin.Chapter3.Defs
public import Theory.GroupTheory.IntersectingConjugateFusion
public import Theory.GroupTheory.PermutingConjugateClosure
public import Theory.GroupTheory.TINormalizerControl
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Order.Minimal

/-!
# Elementary local steps in the elimination of U₃(3)

The normalizer argument in 13.3.15(6) propagates normalization from `X`
to `L = ⟨X^{N_L(V₃)}⟩`; the TI property inside `N_G(L)` then gives
`C_G(V₃) ≤ N_G(V)`. The fusion argument in 13.3.19(1) moves a nonidentity
intersection element to `z`, using the transitive normalizer action, and
applies abelianness of `⟨V^{C_G(z)}⟩`.

The last lemma constructs the minimal outside subgroup used at the end of
Theorem 13.3.16. An involution belongs to the two-core of its centralizer,
so that centralizer belongs to the actual family `H(T)`. Finite descent
then gives a member of `HStar(T,M)` contained in the centralizer.

The module-specific generation, TI, transitivity and abelianness inputs
are explicit. These lemmas do not assert the complete numbered source
results; their premises must be established in the section's assembly.
Conjugation here is left conjugation, so the source's conjugator is inverted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §13.3, printed pp.893–896 (PDF pp.910–913).
-/

namespace CFSG.Quasithin.Chapter13.Section03

open Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise in
/-- The normalizer and TI step in 13.3.15(6), with the preceding normalizer
containment and the parabolic generation identity supplied explicitly. -/
public theorem centralizer_le_normalizer_of_parabolic_generation
    (V V₃ L X : Subgroup G)
    (hX : centralizer (V₃ : Set G) ≤ normalizer (X : Set G))
    (hgen : L = closure {x : G | ∃ l : (L ⊓ normalizer (V₃ : Set G) : Subgroup G),
      ∃ v : X, x = (l : G) * (v : G) * (l : G)⁻¹})
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hV₃ : V₃ ≠ ⊥) (hV₃V : V₃ ≤ V) :
    centralizer (V₃ : Set G) ≤ normalizer (V : Set G) := by
  have hNC : normalizer (V₃ : Set G) ≤
      normalizer (centralizer (V₃ : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp
      (inferInstance : ((centralizer (V₃ : Set G)).subgroupOf
        (normalizer (V₃ : Set G))).Normal)
  have hperm : ((centralizer (V₃ : Set G)) : Set G) *
      ((L ⊓ normalizer (V₃ : Set G)) : Set G) =
      ((L ⊓ normalizer (V₃ : Set G)) : Set G) *
        ((centralizer (V₃ : Set G)) : Set G) :=
    (set_mul_normalizer_comm _ _ (inf_le_right.trans hNC)).symm
  have hCL : centralizer (V₃ : Set G) ≤ normalizer (L : Set G) := by
    rw [hgen]
    exact le_normalizer_conjugate_closure_of_mul_subset _ _ _ hX hperm.le
  exact fun g hg => inf_centralizer_le_normalizer_of_trivial_intersections
    hTI hV₃ hV₃V ⟨hCL hg, hg⟩

/-- The implication from transitivity and 13.3.18(2) to 13.3.19(1).
Abelianness is required only in the centralizer of the fixed element `z`. -/
public theorem commuting_conjugates_of_transitive_abelian_closure
    (V : Subgroup G) (z g : G) (hz : z ≠ 1)
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G),
      MulAut.conj n z = x)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (hinter : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  apply commutator_conjugate_eq_bot_of_intersection_fusion V z g ?_ hinter ?_
  · intro a ha
    exact htrans _ ha (fun he => hz ((MulAut.conj a).injective (by simpa using he)))
  · intro x hx hx1
    obtain ⟨n, hn, hnz⟩ := htrans x hx.1 hx1
    refine ⟨n⁻¹, (normalizer (V : Set G)).inv_mem hn, ?_⟩
    rw [← hnz]
    simp [MulAut.conj_apply, mul_assoc]

/-- The subgroup selection in the final paragraph of Theorem 13.3.16.
The involution supplies the nontrivial two-core needed for membership in
`H(T)`; no additional core hypothesis or characteristic-two assumption
is needed for this selection. -/
public theorem exists_HStar_le_involution_centralizer [Finite G]
    (T M : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hT : T ≤ centralizer ({z} : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ M) :
    ∃ H ∈ Chapter3.HStar T M, H ≤ centralizer ({z} : Set G) := by
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hz)
  have hzC : zpowers z ≤ centralizer ({z} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCN : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact centralizer_le_normalizer _
  have hcore := le_pCoreIn_of_normalizes hp hzC hCN
  have hne : (centralizer ({z} : Set G)).pCoreIn 2 ≠ ⊥ := by
    intro he
    have hone : z ∈ (⊥ : Subgroup G) := he ▸ hcore (mem_zpowers z)
    have hz1 : z = 1 := hone
    simp [hz1] at hz
  obtain ⟨H, hHC, hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M)
    (centralizer ({z} : Set G)) ⟨⟨hne, hT⟩, hout⟩
  exact ⟨H, hH, hHC⟩

end CFSG.Quasithin.Chapter13.Section03
