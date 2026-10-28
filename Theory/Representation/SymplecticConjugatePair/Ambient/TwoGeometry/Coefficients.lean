module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Swapping
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# Coefficient kernels and fixed spaces of elementary semilinear actors

A nonzero module makes the scalar automorphism of an invertible semilinear
operator unique. These automorphisms form a genuine homomorphism. Its kernel
has index at most two in every elementary abelian two-subgroup, because the
finite coefficient field has cyclic automorphism group.

The fixed space of a two-subgroup in the kernel is nonzero and closed under
all coefficient scalars. If a larger actor has that same fixed space, it acts
trivially on the coefficient field. This is the field-actor obstruction needed
in Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.

Semilinearity of the actual standard summand stabilizer is a separate input;
this module constructs and analyzes the coefficient map once that input is given.
-/

@[expose] public section

open Representation BinaryOffender
namespace SymplecticConjugatePair.Ambient.SemilinearCoefficients
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V]
  [Module F V] [Module (ZMod 2) V] [Nontrivial V]

lemma coefficient_unique (ρ : Representation (ZMod 2) G V) (g : G)
    {σ τ : F ≃+* F}
    (hσ : ∀ (c : F) (v : V), ρ g (c • v) = σ c • ρ g v)
    (hτ : ∀ (c : F) (v : V), ρ g (c • v) = τ c • ρ g v) : σ = τ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hgv : ρ g v ≠ 0 := fun h => hv ((ρ.apply_bijective g).1 (h.trans (map_zero _).symm))
  ext c
  exact smul_left_injective F hgv ((hσ c v).symm.trans (hτ c v))

noncomputable def coefficientHom (ρ : Representation (ZMod 2) G V)
    (hsemi : ∀ g : G, ∃ σ : F ≃+* F, ∀ (c : F) (v : V), ρ g (c • v) = σ c • ρ g v) :
    G →* (F ≃+* F) where
  toFun g := (hsemi g).choose
  map_one' := coefficient_unique ρ 1 (hsemi 1).choose_spec (by simp)
  map_mul' g h := coefficient_unique ρ (g*h) (hsemi (g*h)).choose_spec (by
    intro c v
    rw [map_mul]
    change ρ g (ρ h (c • v)) = (hsemi g).choose ((hsemi h).choose c) • ρ g (ρ h v)
    rw [(hsemi h).choose_spec, (hsemi g).choose_spec])

lemma coefficientHom_smul (ρ : Representation (ZMod 2) G V)
    (hsemi : ∀ g : G, ∃ σ : F ≃+* F, ∀ (c : F) (v : V), ρ g (c • v) = σ c • ρ g v)
    (g : G) (c : F) (v : V) :
    ρ g (c • v) = coefficientHom ρ hsemi g c • ρ g v := (hsemi g).choose_spec c v

variable (ρ : Representation (ZMod 2) G V) (π : G →* (F ≃+* F))
    (hsemi : ∀ g : G, ∀ (c : F) (v : V), ρ g (c • v) = π g c • ρ g v)

include hsemi in
lemma coefficient_eq_one_iff (g : G) :
    π g = 1 ↔ ∀ (c : F) (v : V), ρ g (c • v) = c • ρ g v := by
  constructor
  · intro he c v
    simpa only [he, RingAut.one_apply] using hsemi g c v
  · intro he
    exact coefficient_unique ρ g (hsemi g) he

omit [Nontrivial V] in
include hsemi in
lemma kernel_fixedSpace_smul {B : Subgroup G} (hB : B ≤ π.ker)
    {v : V} (hv : v ∈ fixedSpace ρ B) (c : F) : c • v ∈ fixedSpace ρ B := by
  intro b
  have hb : π b.val = 1 := hB b.property
  change ρ b.val (c • v) = c • v
  rw [hsemi, hb, RingAut.one_apply, show ρ b.val v = v from hv b]

omit [Nontrivial V] in
lemma coefficient_involutive {s : G} (hs : s^2 = 1) : Function.Involutive (π s) := by
  intro c
  have he : (π s)^2 = 1 := by rw [← map_pow, hs, map_one]
  exact congrArg (fun σ : F ≃+* F => σ c) he

variable [Finite F]

omit [Nontrivial V] [Module F V] [Module (ZMod 2) V] [AddCommGroup V] in
lemma kernel_relativeIndex_le_two {A : Subgroup G} (hA : IsElementaryAbelian 2 A) :
    (A ⊓ π.ker).relIndex A ≤ 2 := by
  let _ := hA
  let _ : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let _ : IsElementaryAbelian 2 (A.map π) := IsElementaryAbelian.map π
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_ker]
  have hd := IsElementaryAbelian.exponent_dvd_p 2 (A.map π)
  rw [IsCyclic.exponent_eq_card] at hd
  exact Nat.le_of_dvd (by decide) hd

variable [FiniteDimensional (ZMod 2) V]

omit [Finite F] in
include hsemi in
lemma le_kernel_of_fixedSpace_eq {A B : Subgroup G} (hB : IsPGroup 2 B)
    (hBker : B ≤ π.ker) (heq : fixedSpace ρ A = fixedSpace ρ B) : A ≤ π.ker := by
  obtain ⟨v, hv, hfix⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector (ρ.comp B.subtype) hB
  have hvB : v ∈ fixedSpace ρ B := hfix
  have hvA : v ∈ fixedSpace ρ A := heq ▸ hvB
  intro a ha
  change π a = 1
  ext c
  have hcvB := kernel_fixedSpace_smul ρ π hsemi hBker hvB c
  have hcvA : c • v ∈ fixedSpace ρ A := heq ▸ hcvB
  have he := hcvA ⟨a, ha⟩
  change ρ a (c • v) = c • v at he
  rw [hsemi, show ρ a v = v from hvA ⟨a, ha⟩] at he
  exact smul_left_injective F hv he
end SymplecticConjugatePair.Ambient.SemilinearCoefficients
