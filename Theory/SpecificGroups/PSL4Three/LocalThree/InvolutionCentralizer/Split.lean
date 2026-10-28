module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.GroupTheory.Coset.Card

/-!
# The ordinary centralizer of a split involution lift in SL₄(3)

A trace-zero involution splits the natural module into its negative and
positive eigenspaces. Their dimensions sum to four, and their difference is
zero in F₃, so both dimensions are two. Restriction gives a faithful action
of the ordinary lift centralizer on their product. Thus its order divides
|GL₂(3)|² = 2304.

The eigenspace and trace argument adapts
`ClassicalUnitary/UnitaryFourThree/TwoLocal/InvolutionTransport/LinearEigenbasis.lean`
to F₃. This is an ordinary centralizer calculation; passage to the full
projective centralizer is handled in the parent module.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Module Submodule Subgroup
noncomputable section
namespace Matrix.PSL4Three.LocalThree.InvolutionCentralizer
private abbrev V := Fin 4 → ZMod 3
private def involutionLin (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Module.End (ZMod 3) (Fin 4 → ZMod 3) :=
  Matrix.toLin' M

private def negSpace (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
  (involutionLin M).eigenspace (-1)

private def posSpace (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
  (involutionLin M).eigenspace 1

private theorem involution_isCompl
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hsq : M * M = 1) :
    IsCompl (negSpace M) (posSpace M) := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  let f := involutionLin M
  have hf : f * f = 1 := by
    apply LinearMap.ext
    intro x
    change M *ᵥ (M *ᵥ x) = x
    calc
      M *ᵥ (M *ᵥ x) = (M * M) *ᵥ x := Matrix.mulVec_mulVec x M M
      _ = x := by rw [hsq]; simp
  have hfx (x : Fin 4 → ZMod 3) : f (f x) = x := by
    simpa [Module.End.mul_apply] using congrArg (fun g : Module.End (ZMod 3) (Fin 4 → ZMod 3) => g x) hf
  have hsum : negSpace M ⊔ posSpace M = ⊤ := by
    apply top_unique
    intro x hx
    let u : Fin 4 → ZMod 3 := (2 : ZMod 3)⁻¹ • (x - f x)
    let v : Fin 4 → ZMod 3 := (2 : ZMod 3)⁻¹ • (x + f x)
    have hu : u ∈ negSpace M := by
      change u ∈ f.eigenspace (-1)
      rw [Module.End.mem_eigenspace_iff]
      dsimp [u, f]
      rw [map_smul, map_sub, hfx]
      simp [sub_eq_add_neg, add_comm]
    have hv : v ∈ posSpace M := by
      change v ∈ f.eigenspace 1
      rw [Module.End.mem_eigenspace_iff]
      dsimp [v, f]
      rw [map_smul, map_add, hfx]
      simp [add_comm]
    have huv : u + v = x := by
      dsimp [u, v]
      rw [← smul_add]
      funext i
      abel_nf
      simp [smul_eq_mul, h2]
    rw [← huv]
    exact add_mem_sup hu hv
  have hdis : Disjoint (negSpace M) (posSpace M) := by
    rw [disjoint_iff]
    apply le_antisymm
    · rintro x ⟨hxneg, hxpos⟩
      change x ∈ f.eigenspace (-1) at hxneg
      change x ∈ f.eigenspace 1 at hxpos
      rw [Module.End.mem_eigenspace_iff] at hxneg hxpos
      have he : (-1 : ZMod 3) • x = (1 : ZMod 3) • x := hxneg.symm.trans hxpos
      have he0 : -x = x := by simpa using he
      have he' : x + x = 0 := (eq_neg_iff_add_eq_zero.mp he0.symm)
      have he'' : (2 : ZMod 3) • x = 0 := by simpa [two_smul] using he'
      have : x = 0 := by
        exact (smul_eq_zero.mp he'').resolve_left h2
      rw [show x = 0 from this]
      exact Submodule.zero_mem _
    · exact bot_le
  exact ⟨hdis, by rw [codisjoint_iff]; exact hsum⟩

private theorem trace_involution
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hsq : M * M = 1) :
    M.trace = -(finrank (ZMod 3) (negSpace M) : ZMod 3) + finrank (ZMod 3) (posSpace M) := by
  let e := (negSpace M).prodEquivOfIsCompl (posSpace M) (involution_isCompl M hsq)
  let g : Module.End (ZMod 3) (negSpace M × posSpace M) :=
    LinearMap.prodMap ((-1 : ZMod 3) • (1 : Module.End (ZMod 3) (negSpace M))) 1
  have he (x : negSpace M × posSpace M) : involutionLin M (e x) = e (g x) := by
    have hn := (Module.End.mem_eigenspace_iff.mp x.1.property)
    have hp := (Module.End.mem_eigenspace_iff.mp x.2.property)
    change involutionLin M ((x.1 : Fin 4 → ZMod 3) + x.2) =
      (-1 : ZMod 3) • (x.1 : Fin 4 → ZMod 3) + x.2
    rw [map_add, hn, hp, one_smul]
  have hf : involutionLin M = e.conj g := by
    apply LinearMap.ext
    intro x
    simpa using he (e.symm x)
  calc
    M.trace = LinearMap.trace (ZMod 3) _ (involutionLin M) := by simp [involutionLin]
    _ = LinearMap.trace (ZMod 3) _ g := by rw [hf, LinearMap.trace_conj']
    _ = -(finrank (ZMod 3) (negSpace M) : ZMod 3) + finrank (ZMod 3) (posSpace M) := by
      simp [g, LinearMap.trace_prodMap']

private theorem dimensions
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (hsq : M * M = 1) (htrace : M.trace = 0) :
    finrank (ZMod 3) (negSpace M) = 2 ∧ finrank (ZMod 3) (posSpace M) = 2 := by
  have hc := involution_isCompl M hsq
  have hsum : finrank (ZMod 3) (negSpace M) + finrank (ZMod 3) (posSpace M) = 4 := by
    simpa using Submodule.finrank_add_eq_of_isCompl hc
  have ht : -(finrank (ZMod 3) (negSpace M) : ZMod 3) + finrank (ZMod 3) (posSpace M) = 0 :=
    (trace_involution M hsq).symm.trans htrace
  have hp : finrank (ZMod 3) (posSpace M) = 4 - finrank (ZMod 3) (negSpace M) := by omega
  rw [hp] at ht
  have hn : finrank (ZMod 3) (negSpace M) ≤ 4 := by omega
  -- Among dimensions zero through four, only two satisfies the trace equation in F₃.
  interval_cases hn' : finrank (ZMod 3) (negSpace M)
  all_goals first
    | exact ⟨rfl, by omega⟩
    | exfalso; revert ht; decide


private theorem card_aut_two {F W : Type*} [Field F] [Fintype F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] (hd : finrank F W = 2) :
    Nat.card (W ≃ₗ[F] W) = (Fintype.card F ^ 2 - 1) *
      (Fintype.card F ^ 2 - Fintype.card F) := by
  let b := Module.finBasisOfFinrankEq F W hd
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F W)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp [Fin.prod_univ_two]

private abbrev C (g : SL) := centralizer ({g} : Set SL)

private def act (g : SL) : V ≃ₗ[ZMod 3] V := SpecialLinearGroup.toLin' g

private theorem act_commute (g : SL) (x : C g) (v : V) :
    act g (act x.val v) = act x.val (act g v) := by
  have h := x.property g (by simp)
  have he := congrArg (fun t : SL => act t v) h
  simpa only [act, map_mul, LinearEquiv.mul_apply] using he

private def onEigen (g : SL) (c : ZMod 3) (x : C g) :
    (involutionLin (g : Mat)).eigenspace c →ₗ[ZMod 3]
      (involutionLin (g : Mat)).eigenspace c where
  toFun v := ⟨act x.val v, by
    rw [Module.End.mem_eigenspace_iff]
    change act g (act x.val v.val) = c • act x.val v.val
    rw [act_commute, show act g v.val = c • v.val from
      Module.End.mem_eigenspace_iff.mp v.property, map_smul]⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)

private def eigenHom (g : SL) (c : ZMod 3) :
    C g →* ((involutionLin (g : Mat)).eigenspace c ≃ₗ[ZMod 3]
      (involutionLin (g : Mat)).eigenspace c) where
  toFun x := LinearEquiv.ofInjectiveEndo (onEigen g c x) (by
    intro v w h
    exact Subtype.ext ((act x.val).injective (congrArg Subtype.val h)))
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change act 1 v.val = v.val
    simp [act]
  map_mul' x y := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change act (x.val * y.val) v.val = act x.val (act y.val v.val)
    simp only [act, map_mul, LinearEquiv.mul_apply]

/-- Restriction to the two eigenspaces bounds the ordinary centralizer order. -/
public theorem split_card_dvd (g : SL) (hsq : (g : Mat) * (g : Mat) = 1)
    (htr : Matrix.trace (g : Mat) = 0) : Nat.card (centralizer ({g} : Set SL)) ∣ 2304 := by
  let f := (eigenHom g (-1)).prod (eigenHom g 1)
  have hinj : Function.Injective f := by
    intro x y h
    have hn := congrArg Prod.fst h
    have hp := congrArg Prod.snd h
    apply Subtype.ext
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    let e := (negSpace (g : Mat)).prodEquivOfIsCompl _ (involution_isCompl _ hsq)
    obtain ⟨⟨vn, vp⟩, rfl⟩ := e.surjective v
    change act x.val (vn.val + vp.val) = act y.val (vn.val + vp.val)
    rw [map_add, map_add]
    have hn' := congrArg (fun t => (t vn).val) hn
    have hp' := congrArg (fun t => (t vp).val) hp
    exact congrArg₂ (· + ·) hn' hp'
  have hd := Subgroup.card_dvd_of_injective f hinj
  obtain ⟨hn, hp⟩ := dimensions (g : Mat) hsq htr
  have hcn : Nat.card (negSpace (g : Mat) ≃ₗ[ZMod 3] negSpace (g : Mat)) = 48 := by
    rw [card_aut_two hn]; rfl
  have hcp : Nat.card (posSpace (g : Mat) ≃ₗ[ZMod 3] posSpace (g : Mat)) = 48 := by
    rw [card_aut_two hp]; rfl
  simp only [negSpace] at hcn
  simp only [posSpace] at hcp
  simpa only [Nat.card_prod, hcn, hcp] using hd
end Matrix.PSL4Three.LocalThree.InvolutionCentralizer
