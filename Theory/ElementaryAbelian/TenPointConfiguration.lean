module
public import Theory.ElementaryAbelian.BinaryFourConfiguration
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Generating configurations in ten-point subsets of an elementary sixteen

The cardinality formula for finite vector spaces identifies an elementary
abelian two-group of order sixteen with F₂⁴. Transporting the verified binary
four-space configuration gives four generators in any subset of at least ten
nonidentity elements, with all three products with the first generator also
in the subset. The subgroup closure in the conclusion is the actual closure
in the supplied group.

This is the reusable finite geometry underlying the larger-orbit case of
Parrott (1972), Lemma 4, printed pp.674–675.
-/

open scoped IsMulCommutative

namespace Theory.ElementaryAbelian

private abbrev Model := Multiplicative (Fin 4 → ZMod 2)
private theorem model_equiv {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) : Nonempty (V ≃* Model) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ 4 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hV, show (2 : ℕ) ^ 4 = 16 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

/-- A ten-point subset of an elementary abelian group of order sixteen contains
four generators and their three products with the first generator. -/
public theorem exists_generating_configuration_of_ten_le_ncard
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (S : Set V) (hzero : (1 : V) ∉ S) (hcard : 10 ≤ S.ncard) :
    ∃ v : Fin 4 → V, Subgroup.closure (Set.range v) = ⊤ ∧
      (∀ i, v i ∈ S) ∧ (∀ j : Fin 4, j ≠ 0 → v 0 * v j ∈ S) := by
  classical
  obtain ⟨e⟩ := model_equiv hV
  have hzero' : (1 : Model) ∉ e '' S := by
    rintro ⟨x, hx, he⟩
    exact hzero ((e.map_eq_one_iff.mp he) ▸ hx)
  have hcard' : 10 ≤ (e '' S).ncard := by
    rwa [Set.ncard_image_of_injective _ e.injective]
  obtain ⟨v, hv, hi, hp⟩ := binary_four_exists_generating_configuration (e '' S) hzero' hcard'
  refine ⟨fun i => e.symm (v i), ?_, ?_, ?_⟩
  · let D := Subgroup.closure (Set.range (fun i => e.symm (v i)))
    have hD : Subgroup.closure (Set.range v) ≤ D.map e.toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨e.symm (v i), Subgroup.subset_closure ⟨i, rfl⟩, e.apply_symm_apply _⟩
    apply top_unique
    intro x _
    have hx : e x ∈ D.map e.toMonoidHom := hD (hv ▸ Subgroup.mem_top _)
    obtain ⟨y, hy, he⟩ := hx
    exact (e.injective he) ▸ hy
  · intro i
    obtain ⟨x, hx, he⟩ := hi i
    simpa only [← he, e.symm_apply_apply] using hx
  · intro j hj
    obtain ⟨x, hx, he⟩ := hp j hj
    rwa [← map_mul, ← he, e.symm_apply_apply]

end Theory.ElementaryAbelian
