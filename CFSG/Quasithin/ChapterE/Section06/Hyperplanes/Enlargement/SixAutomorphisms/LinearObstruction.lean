module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# An outer binary-linear action cannot fix a Sylow subgroup

The actual field equivalence and projective quotient comparison transport
pointwise Sylow rigidity from the natural binary linear group. Consequently
an induced automorphism subgroup containing an outer automorphism cannot
centralize any Sylow two-subgroup of the embedded L₄(2) or L₅(2).

The intrinsic result is `BinaryLinear.OuterCyclic.sylow_fixing_inner`.
The field and automorphism transports adapt the checked constructions in
`Chapter16.LiePreliminaries.HigherLinear` without importing that later chapter.
This discharges the negative Sylow assertion in E.6.23; construction of the
corank-two two-central subspace remains a separate obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265); compare the model pointwise-Sylow result in 16.1.6, p.1172.
The underlying matrix and field maps are from the attributed ATLAS comparison
module and `BinaryLinear.OuterCyclic.Model`.
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
variable {G : Type*} [Group G] [Finite G] {A Y : Subgroup G}

private theorem model_sylow_fixing_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL Y n 2) (P : Sylow 2 Y) (r : MulAut Y)
    (hr : ∀ x ∈ P, r x = x) : ∃ x : Y, r = MulAut.conj x := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e : Y ≃* LinearGroup n := e₀.trans ((Atlas.fieldEquivPSL n f.symm).trans
    (projectiveEquivLinear (by omega)))
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : ∀ x ∈ Q, MulAut.congr e r x = x := by
    rintro x ⟨y, hy, rfl⟩
    change e (r (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hr y hy]
  obtain ⟨g, hg, he⟩ := sylow_fixing_inner hn Q (MulAut.congr e r) hQ
  refine ⟨e.symm g, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact he

/-- A genuinely outer induced action fixes no Sylow subgroup of either binary model. -/
theorem LinearModelAction.no_fixed_sylow (hm : LinearModelAction A Y)
    (P : Sylow 2 Y) : ¬ (P : Subgroup Y).map Y.subtype ≤ centralizer (A : Set G) := by
  intro hP
  apply hm.outer
  rintro r ⟨a, ha, rfl⟩
  have hfix : ∀ y ∈ P, Y.normalizerMonoidHom a y = y := by
    intro y hy
    apply Subtype.ext
    change (a : G) * (y : G) * (a : G)⁻¹ = y
    exact mul_inv_eq_iff_eq_mul.mpr
      (hP (mem_map_of_mem Y.subtype hy) a ha)
  have hi : ∃ x : Y, Y.normalizerMonoidHom a = MulAut.conj x := by
    rcases hm.model with hm | hm
    · exact model_sylow_fixing_inner (Or.inl rfl) hm P _ hfix
    · exact model_sylow_fixing_inner (Or.inr rfl) hm P _ hfix
  obtain ⟨x, hx⟩ := hi
  exact ⟨x, hx.symm⟩

/-- Only construction of the two-central subspace remains once the model is identified. -/
theorem twoCentralGeometry_of_subspace {V A₁ : Subgroup G}
    (hm : LinearModelAction A Y)
    (hs : ∃ B : Subgroup G, A₁ ≤ B ∧ B ≤ V ∧ subgroupCorank V B = 2 ∧
      Nat.card (actionImage B Y) = 2 ∧
        ∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype ≤ centralizer (B : Set G)) :
    TwoCentralGeometry V A₁ A Y :=
  ⟨hm.no_fixed_sylow, hs⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
