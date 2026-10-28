module

public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Involutions on the natural symplectic four-space

For an involution g in characteristic two, the moved space is totally
isotropic: preservation of the form cancels the two cross terms. Faithfulness
of the matrix action makes this space nonzero for g ≠ 1. Its dimension is
therefore one or two, giving exactly the three Suzuki types. The root-order
calculation uses the original eight matrix root families.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218, and Lemma 16.1.4, printed p.1171.
The identification of root elements with types b₁ and a₂ is a further
conjugacy calculation, not asserted here.
-/

public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
open InvolutionTypes TwoLocalCover
open Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

private theorem moved_pairing_zero (g : Sp F) (hg : g ^ 2 = 1) (x y : Vector F) :
    form F (g • x - x) (g • y - y) = 0 := by
  have hgx : g • (g • x) = x := by rw [← mul_smul, ← pow_two, hg, one_smul]
  have hcross : form F (g • x) y = form F x (g • y) := by
    have h := preserves_form g (g • x) y
    simpa only [hgx] using h.symm
  simp only [map_sub, LinearMap.sub_apply, preserves_form, hcross]
  simp [sub_eq_add_neg, CharTwo.neg_eq, add_comm]

omit [CharP F 2] in
theorem movedSpace_ne_bot (g : Sp F) (hg : g ≠ 1) : movedSpace g ≠ ⊥ := by
  intro h
  apply hg
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hx : g • (Pi.single j (1 : F) : Vector F) - Pi.single j (1 : F) = 0 := by
    have hm : g • (Pi.single j (1 : F) : Vector F) - Pi.single j (1 : F) ∈ movedSpace g :=
      ⟨(Pi.single j (1 : F) : Vector F), rfl⟩
    rwa [h, Submodule.mem_bot] at hm
  have he := congrFun (sub_eq_zero.mp hx) i
  simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec, Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using he

theorem movedSpace_isotropic (g : Sp F) (hg : g ^ 2 = 1) :
    ∀ x ∈ movedSpace g, ∀ y ∈ movedSpace g, form F x y = 0 := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact moved_pairing_zero g hg x y

theorem involution_types (g : Sp F) (hg : orderOf g = 2) :
    IsB1 g ∨ IsA2 g ∨ IsC2 g := by
  have hsq : g ^ 2 = 1 := (orderOf_eq_prime_iff.mp hg).1
  have hne : g ≠ 1 := (orderOf_eq_prime_iff.mp hg).2
  have hdim := finrank_le_two_of_isotropic (movedSpace g) (movedSpace_isotropic g hsq)
  have hpos : Module.finrank F (movedSpace g) ≠ 0 :=
    fun h => movedSpace_ne_bot g hne (Submodule.finrank_eq_zero.mp h)
  have hcases : Module.finrank F (movedSpace g) = 1 ∨
      Module.finrank F (movedSpace g) = 2 := by omega
  rcases hcases with h | h
  · exact Or.inl ⟨hg, h⟩
  · by_cases ha : ∀ v : Vector F, form F v (g • v) = 0
    · exact Or.inr (Or.inl ⟨hg, h, ha⟩)
    · exact Or.inr (Or.inr ⟨hg, h, not_forall.mp ha⟩)

omit [CharP F 2] in
theorem centralizer_le_movedSpace_stabilizer (g : Sp F) :
    centralizer ({g} : Set (Sp F)) ≤ stabilizer (movedSpace g) := by
  intro c hc
  rw [mem_stabilizer_iff]
  rintro _ ⟨v, rfl⟩
  refine ⟨c • v, ?_⟩
  change g • (c • v) - c • v = toLinear c (g • v - v)
  rw [map_sub]
  have hcomm := mem_centralizer_singleton_iff.mp hc
  simp only [toLinear_apply, ← mul_smul, hcomm]

theorem rootElement_sq (r : Fin 8) (t : F) : rootElement r t ^ 2 = 1 := by
  rw [pow_two, RootSubgroup.element_add, CharTwo.add_self_eq_zero,
    RootSubgroup.element_zero]

theorem rootElement_orderOf (r : Fin 8) {t : F} (ht : t ≠ 0) :
    orderOf (rootElement r t) = 2 := by
  apply orderOf_eq_prime (rootElement_sq r t)
  intro he
  rw [← RootSubgroup.element_zero r] at he
  exact ht (RootSubgroup.element_injective r he)

theorem root_orderOf (g : Sp F) (hg : IsRootElement g) : orderOf g = 2 := by
  obtain ⟨h, r, t, ht, rfl⟩ := hg
  have he := rootElement_orderOf r ht
  simpa using ((MulAut.conj h).orderOf_eq (rootElement r t)).trans he

/-- The standard nonalternating rank-two unipotent matrix `[I I; 0 I]`.
Its two long-root factors act on the two different hyperbolic pairs. -/
@[expose] def c2Representative (F : Type*) [Field F] : Sp F :=
  rootElement 0 (1 : F) * rootElement 2 1

end Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers
