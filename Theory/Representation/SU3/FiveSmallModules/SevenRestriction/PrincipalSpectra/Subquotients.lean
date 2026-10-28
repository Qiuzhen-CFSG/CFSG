module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.BranchInputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Spectral
public import Theory.Representation.SimpleHeadQuotient
public import Theory.LinearAlgebra.CharpolySubquotient
public import Theory.Representation.RepEquiv

/-!
# Seven-spectra of arbitrary small principal-series sections

A section is presented as an equivariant image of an invariant subspace of
the original induced module. Pulling back subspaces and composing quotient
maps keeps this presentation through a composition series; the first
isomorphism theorem identifies every simple head with a literal subquotient.

Induction on dimension multiplies characteristic polynomials. Below dimension
22 there is at most one factor of dimension 20 or 21. A 20-dimensional factor
and a trivial line give exactly the 21-dimensional spectrum, including for
nonsplit extensions. If all factors have polynomial `X - 1`, semisimplicity
of the cyclic order-seven operator in characteristic two makes it the identity,
contrary to its order. No semisimplicity of the whole group action is used.

This proves the conditional extension of the published small-factor input.
The finite simple-factor calculation remains with its independent producer.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open Polynomial Representation
namespace Representation.SU3.FiveSmallModules.SevenRestriction
namespace Subquotients

universe w
variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A section is presented by an actual surjective intertwiner from an ambient invariant subspace. -/
private def IsSection (ρ : Representation K G V) (τ : Representation K G W) : Prop :=
  ∃ S : Subrepresentation ρ, ∃ f : S.toRepresentation.IntertwiningMap τ,
    Function.Surjective f

private theorem section_quotient {ρ : Representation K G V} {τ : Representation K G W}
    (h : IsSection ρ τ) (N : Subrepresentation τ) : IsSection ρ N.quotientRepresentation := by
  obtain ⟨S, f, hf⟩ := h
  let q : τ.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  exact ⟨S, q.comp f, N.toSubmodule.mkQ_surjective.comp hf⟩

/-- Pull back the subspace and flatten the two nested invariant subspaces. -/
private theorem section_subrepresentation
    {ρ : Representation K G V} {τ : Representation K G W}
    (h : IsSection ρ τ) (N : Subrepresentation τ) : IsSection ρ N.toRepresentation := by
  obtain ⟨S, f, hf⟩ := h
  let U : Subrepresentation S.toRepresentation := {
    toSubmodule := N.toSubmodule.comap f.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change f (S.toRepresentation g v) ∈ N
      rw [IntertwiningMap.isIntertwining]
      exact N.apply_mem_toSubmodule g hv }
  let A : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map S.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨S.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩ }
  let e : U.toRepresentation.Equiv A.toRepresentation :=
    .mk (Submodule.equivMapOfInjective S.toSubmodule.subtype Subtype.val_injective
      U.toSubmodule) (by
        intro g
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rfl)
  let p : U.toRepresentation.IntertwiningMap N.toRepresentation := {
    toLinearMap := (f.toLinearMap.comp U.toSubmodule.subtype).codRestrict
      N.toSubmodule (fun u => u.property)
    isIntertwining' g := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      exact LinearMap.congr_fun (f.isIntertwining' g) u.val }
  have hp : Function.Surjective p := by
    intro n
    obtain ⟨s, hs⟩ := hf n.val
    refine ⟨⟨s, ?_⟩, Subtype.ext hs⟩
    change f s ∈ N
    rw [hs]
    exact n.property
  exact ⟨A, p.comp e.symm.toIntertwiningMap, hp.comp e.toLinearEquiv.symm.surjective⟩

/-- The first isomorphism theorem, retaining equivariance on the literal quotient. -/
private noncomputable def quotientKernelEquiv
    {ρ : Representation K G V} {τ : Representation K G W}
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) :
    f.ker.quotientRepresentation.Equiv τ :=
  .mk (f.toLinearMap.quotKerEquivOfSurjective hf) (by
    intro g
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => exact LinearMap.congr_fun (f.isIntertwining' g) v)

private theorem charpoly_equiv [FiniteDimensional K V] [FiniteDimensional K W]
    {ρ : Representation K G V} {τ : Representation K G W}
    (e : ρ.Equiv τ) (x : G) : (ρ x).charpoly = (τ x).charpoly := by
  rw [← e.conj_apply_self x, e.toLinearEquiv.charpoly_conj]

private def SimpleFactorSpectra [FiniteDimensional K V] (ρ : Representation K G V) (x : G) : Prop :=
  ∀ (S : Subrepresentation ρ) (T : Subrepresentation S.toRepresentation),
      T.quotientRepresentation.IsIrreducible →
      Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) ≤ 21 →
      (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 1 ∧
        (T.quotientRepresentation x).charpoly = X - C 1) ∨
      ((Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 ∨
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 21) ∧
        (T.quotientRepresentation x).charpoly =
          sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule)))

private theorem small_factor_of_section [FiniteDimensional K V] [FiniteDimensional K W]
    {ρ : Representation K G V} {τ : Representation K G W} (x : G)
    (h : SimpleFactorSpectra ρ x)
    (hs : IsSection ρ τ) (hirr : τ.IsIrreducible) (hd : Module.finrank K W ≤ 21) :
    (Module.finrank K W = 1 ∧ (τ x).charpoly = X - C 1) ∨
      ((Module.finrank K W = 20 ∨ Module.finrank K W = 21) ∧
        (τ x).charpoly = sevenSpectrum K (Module.finrank K W)) := by
  obtain ⟨S, f, hf⟩ := hs
  let e := quotientKernelEquiv f hf
  have he := e.toLinearEquiv.finrank_eq
  have hi := (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv hirr
  have hc := charpoly_equiv e x
  simpa only [he, hc] using h S f.ker hi (he ▸ hd)

private theorem mul_spectra {a b n : ℕ} {p q : K[X]}
    (hsum : b + a = n) (hd : n ≤ 21)
    (hp : p = (X - C 1) ^ a ∨ (20 ≤ a ∧ p = sevenSpectrum K a))
    (hq : (b = 1 ∧ q = X - C 1) ∨
      ((b = 20 ∨ b = 21) ∧ q = sevenSpectrum K b)) :
    p * q = (X - C 1) ^ n ∨ (20 ≤ n ∧ p * q = sevenSpectrum K n) := by
  rcases hq with ⟨hq, hqc⟩ | ⟨hq, hqc⟩
  · rcases hp with hp | ⟨hpd, hp⟩
    · left
      have he : a + 1 = n := by omega
      rw [hp, hqc, ← pow_succ, he]
    · right
      -- The only extension of a large factor by a line has degrees 20 and 21.
      have hn21 : n = 21 := by omega
      have ha20 : a = 20 := by omega
      refine ⟨by omega, ?_⟩
      rw [hp, hqc, hn21, ha20]
      change sevenPolynomial K ^ 3 * (X - C 1) ^ 2 * (X - C 1) =
        sevenPolynomial K ^ 3 * (X - C 1) ^ 3
      rw [pow_succ (X - C (1 : K)) 2, mul_assoc]
  · have hb20 : 20 ≤ b := by omega
    have hp := hp.resolve_right (by rintro ⟨hp, _⟩; omega)
    refine Or.inr ⟨by omega, ?_⟩
    rw [hp, hqc]
    unfold sevenSpectrum
    have he : a + (b - 18) = n - 18 := by omega
    rw [mul_left_comm, ← pow_add, he]

/-- Induction through simple heads; this does not split the group representation. -/
private theorem spectrum_of_small_factors [FiniteDimensional K V]
    (ρ : Representation K G V) (x : G) (h : SimpleFactorSpectra ρ x) :
    ∀ (n : ℕ) (W : Type w) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (τ : Representation K G W), Module.finrank K W = n → n ≤ 21 → IsSection ρ τ →
      (τ x).charpoly = (X - C 1) ^ n ∨
        (20 ≤ n ∧ (τ x).charpoly = sevenSpectrum K n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ _ τ hn hd hs
    by_cases hz : n = 0
    · let : Subsingleton W := Module.finrank_zero_iff.mp (hn.trans hz)
      left
      have he : τ x = 1 := Subsingleton.elim _ _
      simp only [he, LinearMap.charpoly_one, hn, map_one]
    have hp : 0 < Module.finrank K W := by omega
    let : Nontrivial W := Module.finrank_pos_iff.mp hp
    let : IsCoatomic (Subrepresentation τ) := SimpleHeadQuotient.subrepresentation_coatomic τ
    obtain ⟨N, hN, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation τ)).resolve_left
      bot_ne_top
    have hproper : N.toSubmodule ≠ ⊤ := fun he =>
      hN.1 (Subrepresentation.toSubmodule_injective he)
    have hlt : Module.finrank K N.toSubmodule < n :=
      (Submodule.finrank_lt hproper).trans_eq hn
    have hsum := N.toSubmodule.finrank_quotient_add_finrank
    have hq := small_factor_of_section x h (section_quotient hs N)
      (SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN) (by omega)
    have hr := ih (Module.finrank K N.toSubmodule) hlt N.toSubmodule
      N.toRepresentation rfl (by omega) (section_subrepresentation hs N)
    have hc : (τ x).charpoly = (N.toRepresentation x).charpoly *
        (N.quotientRepresentation x).charpoly :=
      LinearMap.charpoly_eq_charpoly_mul_charpoly N.toSubmodule (τ x)
        (N.apply_mem_toSubmodule x)
    rw [hc]
    exact mul_spectra (hsum.trans hn) hd hr hq

/-- Coprime cyclic semisimplicity excludes an all-trivial composition spectrum. -/
private theorem not_all_trivial [FiniteDimensional K W] [CharP K 2]
    (τ : Representation K G W) (x : G) (hx : orderOf (τ x) = 7) :
    (τ x).charpoly ≠ (X - C 1) ^ Module.finrank K W := by
  intro hc
  have h7 : (7 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 2 7).not.mpr (by decide)
  have hp : τ x ^ (7 : ℕ) = 1 := by
    simpa only [hx] using pow_orderOf_eq_one (τ x)
  have hf := fixed_dimension_of_charpoly τ x (1 : K[X]) h7 hp
    (by simp) (by simpa using hc)
  have hi : invariants (τ.comp (Subgroup.zpowers x).subtype) = ⊤ :=
    Submodule.eq_top_iff_finrank_eq.mpr hf
  have he : τ x = 1 := by
    ext v
    have hv : v ∈ invariants (τ.comp (Subgroup.zpowers x).subtype) := by
      rw [hi]
      trivial
    exact (mem_invariants _ v).mp hv ⟨x, Subgroup.mem_zpowers x⟩
  norm_num [he] at hx

end Subquotients

universe v

/-- Small simple-factor spectra determine the spectrum of every principal-series
section in dimensions twenty and twenty-one, including nonsplit extensions.
The two order hypotheses refer to the actual group element and its literal
quotient operator. -/
theorem principal_series_element_seven_spectra_of_small_factors
    (h : PrincipalSeriesSmallFactorSevenSpectra.{0, v}) :
    PrincipalSeriesElementSevenSpectra.{0, v} := by
  intro F _ _ J hF hconj K _ _ _ χ S T hd x hx hTx
  have hs : Subquotients.IsSection
      (ind (standardBorel J).subtype (scalarCharacter χ)) T.quotientRepresentation := by
    let f : S.toRepresentation.IntertwiningMap T.quotientRepresentation := {
      toLinearMap := T.toSubmodule.mkQ
      isIntertwining' _ := rfl }
    exact ⟨S, f, T.toSubmodule.mkQ_surjective⟩
  have hsmall : Subquotients.SimpleFactorSpectra
      (ind (standardBorel J).subtype (scalarCharacter χ)) x := by
    intro A B hirr hdim
    exact h F J hF hconj K χ A B hirr hdim x hx
  have hc := Subquotients.spectrum_of_small_factors _ x hsmall
    (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule))
    (S.toSubmodule ⧸ T.toSubmodule) T.quotientRepresentation rfl (by omega) hs
  exact (hc.resolve_left (Subquotients.not_all_trivial T.quotientRepresentation x hTx)).2

end Representation.SU3.FiveSmallModules.SevenRestriction
