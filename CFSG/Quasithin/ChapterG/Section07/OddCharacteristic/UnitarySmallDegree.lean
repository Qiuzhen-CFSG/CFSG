module

public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.UnitarySieve
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.UnitaryG2Comparison
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.G2DerivedPermutationFiltration
public import Theory.Representation.Quotient

/-!
# The remaining small-degree unitary representation calculation

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.7.2(3), printed pp.347--348 (PDF pp.358--359).
The source asserts that a faithful irreducible binary PSU₃(3)-module of
degree at most eight has degree six. Constructing a degree-six module alone
does not prove this assertion.

The order of the actual Hermitian matrix group is divisible by 27. Since
27 does not divide the binary general linear group orders in degrees below
six, every faithful binary action has degree at least six.

The assembly uses a genuine group equivalence and a
finite filtration of a transitive permutation module with a two-group
stabilizer. Every irreducible module is a quotient of that permutation
module. A filtration with simple factors of degree one, six, or greater
than eight therefore excludes degrees seven and eight.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

private theorem six_le_of_cube_dvd_binary_GL {d : ℕ}
    (h : 3 ^ 3 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) : 6 ≤ d := by
  by_contra hd
  have hd : d ≤ 5 := by omega
  rw [Matrix.card_GL_field] at h
  interval_cases d <;> norm_num [Fin.prod_univ_succ] at h

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The source's actual PSU₃(3) model forces binary degree at least six,
even without irreducibility. -/
theorem psu33_finrank_ge_six (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSU G 3 3) :
    6 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hdiv : 3 ^ 3 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective (by decide) hcard hconj
  exact six_le_of_cube_dvd_binary_GL
    (hdiv.trans (Representation.card_dvd_card_GL_of_injective ρ hρ))

/-- Conditional G.7.2(3) assembly from an actual permutation-module
filtration. The filtration and the group equivalence must both be supplied;
neither a family label nor one degree-six example suffices. -/
theorem psu33_finrank_eq_six_of_permutation_filtration
    (ρ : Representation (ZMod 2) G V) [Representation.IsIrreducible ρ]
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSU G 3 3)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    {K Ω : Type*} [Group K] [Fintype Ω] (e : G ≃* K)
    (τ : K →* Equiv.Perm Ω) (o : Ω) (H : Subgroup K) (hH : IsPGroup 2 H)
    (hstab : ∀ g : K, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : K, τ g o = x)
    (hfiltration : Representation.FactorDegreeFiltration
      {d : ℕ | d = 1 ∨ d = 6 ∨ 8 < d} ((BinaryPermutation.representation Ω).comp τ)) :
    Module.finrank (ZMod 2) V = 6 := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff
      e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  have hdegree := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    τ o H hH hstab htrans hfiltration σ
  have hlower := psu33_finrank_ge_six ρ hρ hmodel
  change Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 6 ∨
    8 < Module.finrank (ZMod 2) V at hdegree
  omega

/-- The source's small-degree assertion for every faithful irreducible binary
PSU₃(3)-module. The genuine PSU₃(3)–G₂(2)′ comparison and the checked
189-point permutation filtration discharge the two concrete inputs to the
conditional assembly above. -/
theorem psu33_finrank_eq_six
    {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) [Representation.IsIrreducible ρ]
    (hρ : Function.Injective ρ) (hmodel : ClassicalGroup.IsPSU L 3 3)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 6 := by
  obtain ⟨e⟩ := psu33_nonempty_equiv_g2_derived hmodel
  obtain ⟨Ω, hΩ, τ, o, H, hH, hstab, htrans, hfiltration⟩ :=
    G2DerivedPermutationFiltration.exists_permutation_filtration
  let : Fintype Ω := hΩ
  exact psu33_finrank_eq_six_of_permutation_filtration
    ρ hρ hmodel hd e τ o H hH hstab htrans hfiltration

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
