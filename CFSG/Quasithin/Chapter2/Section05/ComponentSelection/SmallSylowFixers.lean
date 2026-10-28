module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallModelFacts
public import Theory.SpecificGroups.PSL3Two.FourNormalizers
public import Theory.SpecificGroups.PSL3Three.SylowFixersInner
public import Theory.Mathieu.M11.Properties.FourNormalizer
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.GroupTheory.SemidihedralFourSubgroup

/-!
# Inner pointwise Sylow fixers in the non-A₆ surviving models

Each non-A₆ entry in the exact source catalogue has only inner pointwise
Sylow fixers, implemented by elements of the specified Sylow subgroup.
For PSL₃(2) a four-group suffices; M₁₁ has inner automorphisms and
self-centralizing four-groups; PSL₃(3) uses the two-element fixer bound;
the prime-linear family uses prime-field automorphism coverage.
A₆ is retained as a separate genuine alternative, since its pointwise
Sylow fixer also contains outer automorphisms. Its source diagram movement
is the additional input to the center argument.

Source: Aschbacher--Smith 2.5.8(4), printed pp.556--557.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
open scoped MatrixGroups

/-- Pointwise fixers are inner by the original Sylow subgroup. -/
def SylowPointwiseFixersInner (K : Type*) [Group K] : Prop :=
  ∀ (P : Sylow 2 K) (a : MulAut K), (∀ x ∈ P, a x = x) →
    ∃ z ∈ P, a = MulAut.conj z

private theorem exists_four_of_shape {K : Type*} [Group K] [Finite K]
    (P : Sylow 2 K) (h : SourceSylowTwoShape P) :
    ∃ F : Subgroup K, F ≤ P ∧ IsKleinFour F := by
  unfold SourceSylowTwoShape at h
  rcases h with h | h
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    exact GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (P : Subgroup K) (by omega) e
  · obtain ⟨e⟩ := h
    let a := e.symm (Semidihedral.standardRotation 4 (by omega))
    let b := e.symm (Semidihedral.standardReflection 4 (by omega))
    have ha : orderOf a = 8 := (e.symm.orderOf_eq _).trans (Semidihedral.standardRotation_order 4 (by omega))
    have hb : orderOf b = 2 := (e.symm.orderOf_eq _).trans (Semidihedral.standardReflection_order 4 (by omega))
    have hab : b * a * b⁻¹ = a ^ 3 := by
      have hh := congrArg e.symm (Semidihedral.standard_conjugation 4 (by omega))
      norm_num only [map_mul, map_inv, map_pow] at hh
      exact hh
    have hgen : closure ({a, b} : Set P) = ⊤ := by
      have hh := congrArg (Subgroup.map e.symm.toMonoidHom)
        (Semidihedral.standard_generators 4 (by omega))
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
        map_top_of_surjective _ e.symm.surjective] at hh
      exact hh
    obtain ⟨F, hF, hc, hFP⟩ := Semidihedral.exists_four_le (P : Subgroup K)
      (by omega : 4 ≤ 4) a b ha hb hab hgen
    let := hF
    let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact ⟨F, hFP, ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩⟩

/-- This property follows the actual Sylow map under any carrier equivalence. -/
theorem SylowPointwiseFixersInner.of_mulEquiv {K L : Type*} [Group K] [Finite K]
    [Group L] [Finite L] (h : SylowPointwiseFixersInner L) (e : K ≃* L) :
    SylowPointwiseFixersInner K := by
  intro P a ha
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : ∀ y ∈ Q, b y = y := by
    rintro _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, ha x hx]
  obtain ⟨z, hz, he⟩ := h Q b hb
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨x, hx, ?_⟩
  ext y
  apply e.injective
  have hh := congrArg (fun c : MulAut L => c (e y)) he
  simpa [b, MulAut.congr_apply] using hh

/-- The only exceptional pointwise-fixer branch is precisely A₆. -/
theorem IsSmallRemainingComponent.alternatingSix_or_sylowPointwiseFixersInner
    {K : Type*} [Group K] [Finite K] (h : IsSmallRemainingComponent K) :
    Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ SylowPointwiseFixersInner K := by
  unfold IsSmallRemainingComponent at h
  rcases h with h | h | h | h | h
  · exact Or.inl h
  · obtain ⟨e⟩ := h
    apply Or.inr
    apply SylowPointwiseFixersInner.of_mulEquiv _ e
    intro P a ha
    have hm : IsSmallRemainingComponent Matrix.PSL3Two.PSL := Or.inr (Or.inl ⟨MulEquiv.refl _⟩)
    obtain ⟨F, hFP, hF⟩ := exists_four_of_shape P (hm.sylowTwoShape P)
    let := hF
    obtain ⟨z, hz, he⟩ := Matrix.PSL3Two.four_fixed_inner F a (fun x hx => ha x (hFP hx))
    exact ⟨z, hFP hz, he⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (SylowPointwiseFixersInner.of_mulEquiv Matrix.PSL3Three.sylow_fixed_inner e)
  · obtain ⟨e⟩ := h
    apply Or.inr
    apply SylowPointwiseFixersInner.of_mulEquiv _ e
    intro P a ha
    have hm : IsSmallRemainingComponent Sporadic.Mathieu.M11 :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩)))
    obtain ⟨F, hFP, hF⟩ := exists_four_of_shape P (hm.sylowTwoShape P)
    let := hF
    obtain ⟨z, rfl⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 (MulEquiv.refl _) a
    have hz : z ∈ centralizer (F : Set Sporadic.Mathieu.M11) := by
      intro x hx
      exact ((mul_inv_eq_iff_eq_mul.mp (ha x (hFP hx)))).symm
    rw [Sporadic.Mathieu.m11_four_centralizer F] at hz
    exact ⟨z, hFP hz, rfl⟩
  · obtain ⟨p, hp, hb, ⟨e⟩⟩ := h
    let : Fact p.Prime := ⟨hp.1⟩
    exact Or.inr (SylowPointwiseFixersInner.of_mulEquiv
      (Theory.PSL2.primeField_sylow_fixed_inner (hp.1.odd_of_ne_two (by omega)) (by omega)) e)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
