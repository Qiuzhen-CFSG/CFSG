module

public import Theory.Representation.BinaryNaturalDual.ModelOrbits.SourceComparison
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.MarkedGeometry

/-!
# H.9.1(1–2) for the source group and its marked module

Let M ≃ Aut(PSLₙ(2)), n = 4 or 5, and let V = V₁ ⊕ V₂. The input `eL`
and its equivariance on `e₁` say precisely that V₁ is a natural module for
the actual layer E(M). This marking need not agree with the supplied group
isomorphism `eM`: the proof constructs their compatible replacement. The only
input about V₂ is that an element outside E(M) carries V₁ onto V₂. In the
source that element lies in the specified Sylow T; parts (1–2) only use its
membership outside the layer.

The group and linear comparisons, both marked summands, the full coordinate
action, and the Sylow fixed-line input are constructed by the imported proofs.
Pulling back evaluation proves the unique invariant nondegenerate form.
The three nonempty, pairwise disjoint orbit classes are the punctured marked
summands, singular diagonal vectors, and pairing-one vectors. The latter are
exactly the nonsingular vectors over F₂. The singular diagonal class is exactly
the nonzero vectors fixed by some Sylow two-subgroup. Inner transitivity on
pairing-one vectors is retained for the corrected adapted-pair argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9 setup and
H.9.1(1–2), printed pp.389–390, PDF pp.400–401. These parts are unchanged by
the separately audited fixed-Sylow correction to H.9.1(4).
-/

public section

open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryLinear.OuterCyclic
open Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual.ModelOrbits.MarkedGeometry

variable {n : ℕ} (hn : n = 4 ∨ n = 5)
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
variable (eM : M ≃* MulAut PSL(n, ZMod 2))
variable (eL : componentLayer M ≃* LinearGroup n)
variable (ρ : Representation (ZMod 2) M V)
variable {V₁ V₂ : Submodule (ZMod 2) V} (hV : IsCompl V₁ V₂)
variable (e₁ : V₁ ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
variable (hnatural : ∀ (l : componentLayer M) (x : BinaryLinear.OuterCyclic.Space n),
  ρ l (e₁.symm x : V) = (e₁.symm (eL l x) : V))
variable (houter : ∃ t : M, t ∉ componentLayer M ∧ V₁.map (ρ t) = V₂)

include eM hV hnatural houter in
/-- Construct the actual group and whole-module models from the source hypotheses,
retaining the layer action and both marked summands. -/
theorem exists_source_model :
    ∃ (e : M ≃* MulAut (LinearGroup n))
      (e₂ : V₂ ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))
      (eV : V ≃ₗ[ZMod 2] CoordinateSpace n),
      (∀ l : componentLayer M, e l = MulAut.conj (eL l)) ∧
      (∀ m : M, e m ∈ MulAut.innerSubgroup (LinearGroup n) ↔ m ∈ componentLayer M) ∧
      (∀ u : V₁, eV u = (e₁ u, 0)) ∧
      (∀ w : V₂, eV w = (0, e₂ w)) ∧
      (∀ m v, eV (ρ m v) =
        (AutomorphismModel.coordinateAction hn).representation (e m) (eV v)) :=
  SourceComparison.exists_marked_equiv hn (AutomorphismModel.coordinateAction hn)
    eM eL ρ hV e₁ hnatural houter

include hn eM hV hnatural houter in
/-- H.9.1(1): the source module has a unique nondegenerate M-invariant form
in which the natural summand is totally singular. -/
theorem source_existsUnique_quadratic :
    ∃! q : QuadraticForm (ZMod 2) V, IsInvariantForm ρ V₁ q := by
  obtain ⟨e, e₂, eV, _, _, he₁, _, ha⟩ :=
    exists_source_model hn eM eL ρ hV e₁ hnatural houter
  let A := AutomorphismModel.coordinateAction hn
  have h₁ := mem_natural_iff_of_marking eV e₁ he₁
  exact ⟨form eV, form_invariant A ρ e eV ha h₁ hn,
    fun Q hQ => form_unique A ρ e eV ha h₁ Q hQ⟩

include hn eM hV hnatural houter in
/-- H.9.1(1–2), including nonemptiness and disjointness of the three orbit classes,
the existential Sylow clause, and transitivity by the actual layer on pairing-one vectors.
There is no action-existence, model-comparison, orbit, or fixed-line premise. -/
theorem source_form_and_orbits :
    ∃ q : QuadraticForm (ZMod 2) V,
      IsInvariantForm ρ V₁ q ∧
      (∀ Q : QuadraticForm (ZMod 2) V, IsInvariantForm ρ V₁ Q → Q = q) ∧
      (∀ v : V, Pure V₁ V₂ v → q v = 0) ∧
      (∀ v : V, q v = 1 → v ∉ V₁ ∧ v ∉ V₂) ∧
      (∀ v w : V, v ≠ 0 → w ≠ 0 →
        ((∃ m : M, ρ m v = w) ↔
          (Pure V₁ V₂ v ∧ Pure V₁ V₂ w) ∨
          (SingularDiagonal V₁ V₂ q v ∧ SingularDiagonal V₁ V₂ q w) ∨
          (q v = 1 ∧ q w = 1))) ∧
      ((∃ v : V, Pure V₁ V₂ v) ∧
        (∃ v : V, SingularDiagonal V₁ V₂ q v) ∧ (∃ v : V, q v = 1)) ∧
      (∀ v : V,
        (Pure V₁ V₂ v → ¬ SingularDiagonal V₁ V₂ q v) ∧
        (Pure V₁ V₂ v → q v ≠ 1) ∧
        (SingularDiagonal V₁ V₂ q v → q v ≠ 1)) ∧
      (∀ v : V, v ≠ 0 →
        (SingularDiagonal V₁ V₂ q v ↔ ∃ P : Sylow 2 M, ∀ m ∈ P, ρ m v = v)) ∧
      (∀ v w : V, q v = 1 → q w = 1 →
        ∃ l ∈ componentLayer M, ρ l v = w) := by
  obtain ⟨e, e₂, eV, _, hL, he₁, he₂, ha⟩ :=
    exists_source_model hn eM eL ρ hV e₁ hnatural houter
  let A := AutomorphismModel.coordinateAction hn
  have h₁ := mem_natural_iff_of_marking eV e₁ he₁
  have h₂ := mem_dual_iff_of_marking eV e₂ he₂
  refine ⟨form eV, form_invariant A ρ e eV ha h₁ hn,
    fun Q hQ => form_unique A ρ e eV ha h₁ Q hQ,
    fun v hv => pure_singular eV h₁ h₂ hv,
    fun v hv => nonsingular_diagonal eV h₁ h₂ hv,
    fun v w hv hw => orbit_iff A ρ e eV ha h₁ h₂ hn hv hw,
    MarkedGeometry.orbit_classes_nonempty eV h₁ h₂ (by omega : 2 ≤ n),
    MarkedGeometry.orbit_classes_disjoint eV h₁ h₂,
    fun v hv => MarkedGeometry.singularDiagonal_iff_exists_sylow_fixed A ρ e eV ha h₁ h₂ hn hv,
    fun v w hv hw => exists_layer_eq_of_pairing_one A ρ e eV ha hL hv hw⟩

end CFSG.Quasithin.ChapterH.NaturalDual
