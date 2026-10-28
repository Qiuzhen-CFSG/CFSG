module

public import Theory.Representation.CompleteReducibility
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

/-!
# Fixed-point-free binary modules for the literal SL₂(2) residual

Let `C = SL₂(2)'`, as a subgroup of the determinant-one matrix group. Every
finite binary `C`-module with zero invariant space is equivariantly a finite
sum of the tautological matrix plane. A nonzero such module of order at most
four is a single natural plane and has order exactly four.

We identify `C` with the three actual matrices `1, r, r²`, where
`r = !![0, 1; 1, 1]`. Maschke's theorem supplies simple summands. On each
summand, the cubic norm is zero, so `r²v = v + rv`; a nonzero vector gives
the injective equivariant map `(a,b) ↦ av + b(rv)`. Simplicity makes this
map surjective. Combining these maps with the group-algebra decomposition
produces the stated linear equivalence, with no nonzero assumption on the
whole module and no extending symmetric-three action.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (4.6.12)(1)--(2), printed p.910. This is the binary
representation-theoretic input; the geometric action descent and vanishing
of the actual section's fixed space belong to the source assembly.
-/

noncomputable section

namespace BinarySL2Residual
open Matrix
open scoped commutatorElement MonoidAlgebra
/-- The binary scalar field. -/
public abbrev F := ZMod 2
/-- The literal two-by-two determinant-one matrix group. -/
public abbrev H := Matrix.SpecialLinearGroup (Fin 2) F
/-- The actual derived subgroup, not the full special linear group. -/
public abbrev C := commutator H
private abbrev Plane := Fin 2 → F

private def r : H := ⟨!![0, 1; 1, 1], by decide⟩
private def s : H := ⟨!![0, 1; 1, 0], by decide⟩
private def t : H := ⟨!![1, 1; 0, 1], by decide⟩

private def K : Subgroup H where
  carrier := {g | g = 1 ∨ g = r ∨ g = r * r}
  one_mem' := Or.inl rfl
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private theorem commutator_eq_K : commutator H = K := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    have h : ∀ a b : H, ⁅a, b⁆ ∈ K := by
      change ∀ a b : H, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = r ∨ ⁅a, b⁆ = r * r
      decide +kernel
    exact fun a _ b _ => h a b
  · have hr : r ∈ commutator H := by
      have h : ⁅t, s⁆ = r := by decide +kernel
      rw [← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top t) (Subgroup.mem_top s)
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hr
    · exact Subgroup.mul_mem _ hr hr

private def c : C := ⟨r, by
  change r ∈ commutator H
  rw [commutator_eq_K]
  exact Or.inr (Or.inl rfl)⟩

private theorem words (g : C) : g = 1 ∨ g = c ∨ g = c * c := by
  have h := g.property
  change (g : H) ∈ commutator H at h
  rw [commutator_eq_K] at h
  rcases h with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))
private theorem cube : c ^ 3 = 1 := by
  apply Subtype.ext
  exact (by decide +kernel : r ^ 3 = 1)

private theorem card_C : Nat.card C = 3 := by
  change Nat.card (commutator H) = 3
  rw [commutator_eq_K]
  change Nat.card {g : H // g = 1 ∨ g = r ∨ g = r * r} = 3
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def natural : Representation F C Plane where
  toFun g := Matrix.toLin' g.val.val
  map_one' := Matrix.toLin'_one
  map_mul' g h := Matrix.toLin'_mul g.val.val h.val.val

private def a (g : C) : MonoidAlgebra F C := MonoidAlgebra.of F C g
private lemma a_one : a 1 = 1 := map_one (MonoidAlgebra.of F C)
private lemma a_mul (g h : C) : a (g * h) = a g * a h := map_mul (MonoidAlgebra.of F C) g h

section Simple
variable {M : Type*} [AddCommGroup M] [Module F M]
  [Module F[C] M] [IsScalarTower F F[C] M]

omit [Module F[C] M] [IsScalarTower F F[C] M] in
private lemma double (v : M) : v + v = 0 := by
  simpa only [show (1 : F) + 1 = 0 by decide, zero_smul, one_smul] using
    (add_smul (1 : F) 1 v).symm

omit [Module F M] [IsScalarTower F F[C] M] in
private lemma cube_smul (v : M) : a c • (a c • (a c • v)) = v := by
  rw [smul_smul, smul_smul, ← a_mul, ← a_mul]
  have h : c * c * c = 1 := by simpa [pow_succ, mul_assoc] using cube
  rw [h, a_one, one_smul]

omit [IsScalarTower F F[C] M] in
private lemma square_smul (hfix : ∀ v : M, a c • v = v → v = 0) (v : M) :
    a c • (a c • v) = v + a c • v := by
  have hn : v + a c • v + a c • (a c • v) = 0 := by
    apply hfix
    simp only [smul_add, cube_smul]
    abel
  have he := eq_neg_of_add_eq_zero_right hn
  have neg (x : M) : -x = x := neg_eq_iff_add_eq_zero.mpr (double x)
  simpa only [neg] using he

private def planeMap (v : M) : Plane →ₗ[F] M where
  toFun x := x 0 • v + x 1 • (a c • v)
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' k x := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]

private lemma planeMap_c (hfix : ∀ v : M, a c • v = v → v = 0) (v : M) (x : Plane) :
    planeMap v (natural c x) = a c • planeMap v x := by
  have hn : natural c x = ![x 1, x 0 + x 1] := by
    change (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) *ᵥ x = _
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hn]
  change x 1 • v + (x 0 + x 1) • (a c • v) = a c • (x 0 • v + x 1 • (a c • v))
  simp only [smul_add, smul_comm (a c), square_smul hfix, add_smul]
  abel

private lemma planeMap_equivariant (hfix : ∀ v : M, a c • v = v → v = 0)
    (v : M) (g : C) (x : Plane) :
    planeMap v (natural g x) = a g • planeMap v x := by
  rcases words g with rfl | rfl | rfl
  · simp [a, map_one, Module.End.one_apply]
  · exact planeMap_c hfix v x
  · rw [map_mul, Module.End.mul_apply, planeMap_c hfix, planeMap_c hfix,
      a_mul, mul_smul]

omit [IsScalarTower F F[C] M] in
private lemma planeMap_injective (hfix : ∀ v : M, a c • v = v → v = 0)
    (v : M) (hv : v ≠ 0) : Function.Injective (planeMap v) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change x 0 • v + x 1 • (a c • v) = 0 at hx
  have hc : a c • v ≠ 0 := by
    intro he
    have := cube_smul v
    rw [he, smul_zero, smul_zero] at this
    exact hv this.symm
  have hs : v + a c • v ≠ 0 := by
    intro he
    apply hv
    apply hfix
    have hh := eq_neg_of_add_eq_zero_right he
    exact hh.trans (neg_eq_iff_add_eq_zero.mpr (double v))
  have hz : x 0 = 0 ∧ x 1 = 0 := by
    have cases (b : F) : b = 0 ∨ b = 1 := by revert b; decide
    rcases cases (x 0) with h0 | h0 <;> rcases cases (x 1) with h1 | h1 <;>
      simp_all only [zero_smul, one_smul, zero_add, add_zero, and_self]
  ext i
  fin_cases i
  · exact hz.1
  · exact hz.2

private lemma simple_coordinates [IsSimpleModule F[C] M]
    (hfix : ∀ v : M, a c • v = v → v = 0) :
    ∃ e : M ≃ₗ[F] Plane, ∀ g v, e (a g • v) = natural g (e v) := by
  let : Nontrivial M := IsSimpleModule.nontrivial F[C] M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  let f : natural.asModule →ₗ[F[C]] M :=
    MonoidAlgebra.equivariantOfLinearOfComm
      ((planeMap v).comp natural.asModuleEquiv.toLinearMap) (fun g x => by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one]
        exact planeMap_equivariant hfix v g _)
  have hf : f ≠ 0 := by
    intro he
    have hh := LinearMap.congr_fun he (natural.asModuleEquiv.symm ![1, 0])
    change (1 : F) • v + (0 : F) • (a c • v) = 0 at hh
    exact hv (by simpa using hh)
  have hsur : Function.Surjective (planeMap v) := by
    intro w
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_ne_zero hf w
    exact ⟨natural.asModuleEquiv x, hx⟩
  let e := LinearEquiv.ofBijective (planeMap v) ⟨planeMap_injective hfix v hv, hsur⟩
  refine ⟨e.symm, ?_⟩
  intro g w
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  change a g • w = planeMap v (natural g (e.symm w))
  rw [planeMap_equivariant hfix]
  exact congrArg (fun z => a g • z) (e.apply_symm_apply w).symm
end Simple

/-- Every finite fixed-point-free binary module for `SL₂(2)'` has actual
coordinates as a finite sum of its tautological planes. The zero module is
allowed, in which case the number of summands is zero. -/
public theorem exists_natural_decomposition {W : Type*} [AddCommGroup W] [Module F W] [Finite W]
    (ρ : Representation F C W) (hfix : Representation.invariants ρ = ⊥) :
    ∃ (n : ℕ) (e : W ≃ₗ[F] (Fin n → Fin 2 → F)),
      ∀ (g : C) (w : W) (j : Fin n), e (ρ g w) j = g.val.val.mulVec (e w j) := by
  classical
  let : Finite ρ.asModule := Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  let : IsSemisimpleModule F[C] ρ.asModule :=
    ρ.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (Or.inr (by
      rw [ZMod.ringChar_zmod_n, card_C]
      decide))
  have hmfix (w : ρ.asModule) (hw : a c • w = w) : w = 0 := by
    have hg (g : C) : a g • w = w := by
      rcases words g with rfl | rfl | rfl
      · rw [a_one, one_smul]
      · exact hw
      · rw [a_mul, mul_smul, hw, hw]
    have hi : ρ.asModuleEquiv w ∈ Representation.invariants ρ := by
      intro g
      have hh := congrArg ρ.asModuleEquiv (hg g)
      simpa only [a, Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_of] using hh
    rw [hfix] at hi
    exact ρ.asModuleEquiv.injective (hi.trans ρ.asModuleEquiv.map_zero.symm)
  obtain ⟨n, S, d, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp F[C] ρ.asModule
  let := hs
  have hS (j : Fin n) (w : S j) (hw : a c • w = w) : w = 0 := by
    apply Subtype.ext
    exact hmfix w (congrArg Subtype.val hw)
  choose f hf using fun j => simple_coordinates (hS j)
  let D := d.trans (DFinsupp.linearEquivFunOnFintype (R := F[C]))
  let e : W ≃ₗ[F] (Fin n → Plane) := ρ.asModuleEquiv.symm.trans
    ((D.restrictScalars F).trans (LinearEquiv.piCongrRight f))
  refine ⟨n, e, ?_⟩
  intro g w j
  change f j (D (ρ.asModuleEquiv.symm (ρ g w)) j) = natural g (f j (D (ρ.asModuleEquiv.symm w) j))
  rw [Representation.asModuleEquiv_symm_map_rho, D.map_smul]
  exact hf j g _

/-- A nonzero fixed-point-free binary residual module of order at most four
has order four and is equivariantly the actual matrix plane. -/
public theorem natural_of_card_le_four {W : Type*} [AddCommGroup W] [Module F W] [Finite W]
    [Nontrivial W] (ρ : Representation F C W) (hfix : Representation.invariants ρ = ⊥)
    (hcard : Nat.card W ≤ 4) :
    Nat.card W = 4 ∧ ∃ e : W ≃ₗ[F] (Fin 2 → F),
      ∀ (g : C) (w : W), e (ρ g w) = g.val.val.mulVec (e w) := by
  obtain ⟨n, e, he⟩ := exists_natural_decomposition ρ hfix
  have hc : Nat.card W = 4 ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fun]
    simp [F]
  have hn0 : n ≠ 0 := by
    intro hn
    have hh := Finite.one_lt_card (α := W)
    rw [hc, hn, pow_zero] at hh
    omega
  have hn : n = 1 := by
    have hp : 4 ^ n ≤ 4 ^ 1 := by simpa only [pow_one, ← hc] using hcard
    have hle : n ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 4)).mp hp
    omega
  subst n
  refine ⟨by simpa using hc, e.trans (LinearEquiv.piUnique F (fun _ : Fin 1 => Plane)), ?_⟩
  intro g w
  exact he g w 0

end BinarySL2Residual
