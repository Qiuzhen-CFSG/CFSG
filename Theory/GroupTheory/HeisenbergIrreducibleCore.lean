module
public import Theory.GroupTheory.HeisenbergResidualComparison
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Irreducible Heisenberg images and the three-core

A normal self-centralizing Heisenberg subgroup R of order 27 is the full
three-core if the ambient action on R/Φ(R) is irreducible. Orbit counting
gives a nonidentity fixed point for the three-core. Its normality makes
the fixed subgroup invariant, so irreducibility makes the action trivial;
the literal Frattini-action kernel is R.

Consequently a proper such R in the full two-residual leaves an SL₂(3)
quotient: a cubic quotient would make the two-residual a normal three-group.
No splitting of the remaining extension is assumed or asserted.

Source application: Aschbacher–Smith 14.7.15(3), 14.7.27, printed
pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Subgroup

/-- Irreducibility on the actual Frattini quotient identifies the full three-core. -/
theorem heisenberg_pCore_eq_of_irreducible
    {D : Type*} [Group D] [Finite D]
    (R : Subgroup D) [R.Normal] (e : R ≃* HeisenbergPrime 3)
    (hc : centralizer (R : Set D) ≤ R)
    (hirr : ∀ J : Subgroup (R ⧸ frattini R),
      (∀ a : D, ∀ x ∈ J, quotientAut (frattini R) (MulAut.conjNormal a) x ∈ J) →
        J = ⊥ ∨ J = ⊤) : pCore 3 D = R := by
  let : IsExtraspecial 3 R := (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hR : IsPGroup 3 R := IsExtraspecial.isPGroup 3 R
  let W := R ⧸ frattini R
  let : Nontrivial W := by
    dsimp only [W]
    rw [IsExtraspecial.frattini_eq_center (p := 3)]
    exact IsExtraspecial.quotient_nontrivial 3 R
  let f : D →* MulAut W := (quotientAut (frattini R)).comp MulAut.conjNormal
  have hk : f.ker = R := by
    dsimp only [f]
    rw [←MonoidHom.comap_ker,IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := 3)]
    change (MulAut.innerSubgroup R).comap (MulAut.conjNormal : D →* MulAut R) = R
    rw [MulAut.conjNormal_comap_innerSubgroup,sup_eq_left.mpr hc]
  let : MulDistribMulAction D W := MulDistribMulAction.compHom W f
  let P := pCore 3 D
  have hdiv : 3 ∣ Nat.card W := (hR.to_quotient (frattini R)).card_eq_or_dvd.resolve_left
    (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨w,hw,hwne⟩ := (pCore_isPGroup (p := 3) (G := D)).exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := W) hdiv (show (1 : W) ∈ MulAction.fixedPoints P W by simp [MulAction.mem_fixedPoints])
  have hfixed : FixedPoints.subgroup P W ≠ ⊥ := by
    intro he
    have hh : w ∈ FixedPoints.subgroup P W := hw
    rw [he,mem_bot] at hh
    exact hwne hh.symm
  have hinv := fixedPoints_isInvariant_of_normalizing_actor (V := W) (⊤ : Subgroup D) P
    (by rw [normalizer_eq_top])
  have htop : FixedPoints.subgroup P W = ⊤ :=
    (hirr _ (fun a x hx => (hinv.invariant ⟨a,mem_top a⟩ x).mp hx)).resolve_left hfixed
  have hRcore : R ≤ pCore 3 D := le_sSup ⟨inferInstance,hR⟩
  apply le_antisymm _ hRcore
  intro a ha
  rw [←hk,MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro x
  have hx : x ∈ FixedPoints.subgroup P W := by rw [htop]; trivial
  exact hx ⟨a,ha⟩

/-- Once the local image is the full three-core, strict containment in the
two-residual leaves the literal SL₂(3) quotient and excludes the cubic branch. -/
theorem heisenberg_twoResidual_sl23_of_pCore_eq
    {D : Type*} [Group D] [Finite D]
    (R : Subgroup D) [R.Normal] (e : R ≃* HeisenbergPrime 3)
    (hc : centralizer (R : Set D) ≤ R)
    (hcore : pCore 3 D = R) (hR : R ≤ pResidual 2 D)
    (hne : R ≠ pResidual 2 D) :
    Nonempty (((pResidual 2 D) ⧸ R.subgroupOf (pResidual 2 D)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  rcases (heisenberg_twoResidual_comparison R e hc hR).resolve_left hne with h3 | hSL
  · exfalso
    let K := pResidual 2 D
    let A := R.subgroupOf K
    have hR3 : IsPGroup 3 R :=
      (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
    have hA3 : IsPGroup 3 A := hR3.comap_subtype
    have hQ3 : IsPGroup 3 (K ⧸ A) := IsPGroup.of_card (p := 3) (n := 1) (by simpa using h3)
    have hK3 : IsPGroup 3 K := by
      have hp := (hQ3.to_subgroup ⊤).comap_of_ker_isPGroup (QuotientGroup.mk' A)
        (by rw [QuotientGroup.ker_mk']; exact hA3)
      rw [comap_top] at hp
      exact hp.of_surjective (⊤ : Subgroup K).subtype (by intro x; exact ⟨⟨x,mem_top x⟩,rfl⟩)
    have hKcore : K ≤ pCore 3 D := le_sSup ⟨inferInstance,hK3⟩
    exact hne (le_antisymm hR (hcore ▸ hKcore))
  · exact hSL

end Subgroup
