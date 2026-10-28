module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Weyl
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model

/-!
# Assembly and form transport for the binary PSU₃ torus configuration

The actual diagonal matrices and coordinate permutations discharge the
marked generation, swapping, exponent and normalization clauses.
The remaining index and fixed-subgroup cardinality assertions are kept
explicit in `configurationOfCounts`. An orthonormal basis gives a genuine
projective group equivalence carrying the complete configuration to any
input Hermitian form, with its original involution retained.

This is a conditional assembly, not the unconditional existence theorem.
Source: Aschbacher–Smith I.1.3(2), PDF p.418; GLS III, Theorem 6.1.4 and
Tables 6.1.2–3. The matrix basis change uses Huppert II.10.4(a).
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
variable {F : Type*} [Field F]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)

variable {E : Type*} [Field E] {K : HermitianForm 3 E} {n : ℕ}

/-- Carry all marked elements and both subgroup conditions through an actual
multiplicative equivalence of projective matrix groups. -/
def transport (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
    ProjectiveSpecialUnitaryMatrixGroup K) (D : TorusConfiguration J n) :
    TorusConfiguration K n where
  torus := D.torus.map e.toMonoidHom
  first := e D.first
  second := e D.second
  cycle := e D.cycle
  swap := e D.swap
  generate := by
    have hg := congrArg (fun H : Subgroup _ => H.map e.toMonoidHom) D.generate
    simpa only [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, Set.image_pair] using hg
  commute := D.commute.map e.toMonoidHom
  swap_first := by rw [← map_inv, ← map_mul, ← map_mul, D.swap_first]
  swap_second := by rw [← map_inv, ← map_mul, ← map_mul, D.swap_second]
  first_pow := by rw [← map_pow, D.first_pow, map_one]
  normalizes := by
    rw [mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [← map_mul, ← map_inv, mem_map_equiv, e.symm_apply_apply] using
      (mem_normalizer_iff.mp D.normalizes x)
  index_prime_to_three := by
    have hz := e.toMonoidHom.map_zpowers D.cycle
    simp only [MulEquiv.coe_toMonoidHom] at hz
    rw [← hz, ← Subgroup.map_sup, Subgroup.index_map_of_bijective e.bijective]
    exact D.index_prime_to_three
  fixed_card_le := by
    have he : (D.torus ⊓ centralizer ({D.cycle} : Set _)).map e.toMonoidHom =
        D.torus.map e.toMonoidHom ⊓ centralizer ({e D.cycle} : Set _) := by
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [mem_map_equiv, e.symm_apply_apply, mem_inf, mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, e.injective.eq_iff]
    rw [← he, ← Nat.card_congr
      ((D.torus ⊓ centralizer ({D.cycle} : Set _)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv]
    exact D.fixed_card_le


/-- The matrix construction discharges every configuration field except its
two finite counting assertions. These remain explicit source obligations. -/
def configurationOfCounts [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hindex : ¬ 3 ∣ (normOneTorus J hJ ⊔ zpowers (cycle J hJ)).index)
    (hfixed : Nat.card (normOneTorus J hJ ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3) :
    TorusConfiguration J n := by
  let g : EvenInner.normOne J :=
    Classical.choose (IsCyclic.exists_generator (α := EvenInner.normOne J))
  have hg : ∀ a : EvenInner.normOne J, ∃ k : ℤ, g ^ k = a :=
    Classical.choose_spec (IsCyclic.exists_generator (α := EvenInner.normOne J))
  refine {
    torus := normOneTorus J hJ
    first := first J hJ _ (normOne_norm J) g
    second := second J hJ _ (normOne_norm J) g
    cycle := cycle J hJ
    swap := swap J hJ
    generate := generate J hJ _ (normOne_norm J) g hg
    commute := first_commute_second J hJ _ (normOne_norm J) g
    swap_first := swap_first J hJ _ (normOne_norm J) g
    swap_second := swap_second J hJ _ (normOne_norm J) g
    first_pow := first_pow J hJ _ (normOne_norm J) g ?_
    normalizes := cycle_normalizes J hJ _ (normOne_norm J)
    index_prime_to_three := hindex
    fixed_card_le := hfixed }
  rw [← EvenInner.normOne_card J hcard hconj]
  exact pow_card_eq_one'

/-- Identity Gram model with the original stored field involution. -/
def identityModel : HermitianForm 3 F :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.identityForm J.conj J.conj_involutive

/-- The concrete counting assertions on the identity model give a complete
configuration on the original Hermitian form by genuine matrix basis change. -/
theorem nonempty_of_identity_counts [Finite F] {n : ℕ}
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hindex : ¬ 3 ∣ (normOneTorus (identityModel J) rfl ⊔
      zpowers (cycle (identityModel J) rfl)).index)
    (hfixed : Nat.card (normOneTorus (identityModel J) rfl ⊓
      centralizer ({cycle (identityModel J) rfl} : Set _) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityModel J))) ≤ 3) :
    Nonempty (TorusConfiguration J n) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 J (2 ^ n) hcard (card_fixed J hcard hconj)
  let e := (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.projectiveBasisEquiv J P hP).symm
  exact ⟨transport (identityModel J) e
    (configurationOfCounts (identityModel J) rfl hcard hconj hindex hfixed)⟩

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
