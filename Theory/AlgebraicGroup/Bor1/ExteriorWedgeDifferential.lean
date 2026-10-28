module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialMinor
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The exterior-power matrix minor with a fixed family of source columns. -/
@[expose]
public noncomputable def rationalRepresentationExteriorWedgeMinor
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    {n : ℕ} (s : Set.powersetCard (Fin (Module.finrank k V)) n)
    (c : Fin n ↪o Fin (Module.finrank k V)) : G.PolynomialFunction :=
  Matrix.det fun i j : Fin n =>
    rationalRepresentationMatrixCoefficient ρ e f
      (Set.powersetCard.ofFinEmbEquiv.symm s i) (c j)

/-- A linear matrix coefficient of a rational representation acting on a
basis top wedge, expanded in the exterior basis. -/
@[expose]
public noncomputable def rationalRepresentationExteriorWedgeCoefficient
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    {n : ℕ} (c : Fin n ↪o Fin (Module.finrank k V))
    (L : Module.Dual k (⋀[k]^n V)) : G.PolynomialFunction :=
  ∑ s, algebraMap k G.PolynomialFunction (L (e.exteriorPower n s)) *
    rationalRepresentationExteriorWedgeMinor ρ e f s c

/-- The infinitesimal exterior-action vector on a fixed basis wedge,
reconstructed from the derivatives of all exterior minors. -/
@[expose]
public noncomputable def rationalRepresentationExteriorWedgeDifferential
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    {n : ℕ} (c : Fin n ↪o Fin (Module.finrank k V)) :
    IdentityPointDerivation G →ₗ[k] (⋀[k]^n V) where
  toFun D := ∑ s, D (rationalRepresentationExteriorWedgeMinor ρ e f s c) •
    e.exteriorPower n s
  map_add' := by
    intro D E
    simp only [Derivation.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro z D
    simp only [Derivation.smul_apply, RingHom.id_apply, Finset.smul_sum,
      smul_smul, smul_eq_mul]

omit [FiniteDimensional k V] in
/-- Every covector evaluates the infinitesimal exterior-action vector as the
derivative of its exterior linear matrix coefficient. -/
public theorem rationalRepresentationExteriorWedgeDifferential_coefficient
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    {n : ℕ} (c : Fin n ↪o Fin (Module.finrank k V))
    (D : IdentityPointDerivation G) (L : Module.Dual k (⋀[k]^n V)) :
    L (rationalRepresentationExteriorWedgeDifferential ρ e f c D) =
      D (rationalRepresentationExteriorWedgeCoefficient ρ e f c L) := by
  rw [rationalRepresentationExteriorWedgeDifferential,
    rationalRepresentationExteriorWedgeCoefficient]
  change L (∑ s, D (rationalRepresentationExteriorWedgeMinor ρ e f s c) •
    e.exteriorPower n s) = _
  simp only [map_sum, map_smul]
  simp_rw [D.leibniz]
  have hsmul (q : G.PolynomialFunction) (a : k) : q • a = q 1 * a := rfl
  simp_rw [hsmul]
  simp only [Derivation.map_algebraMap, polynomialFunction_algebraMap_apply,
    mul_zero, add_zero]
  ring_nf

/-- The exterior coefficient evaluates to the covector applied to the actual
exterior action on the chosen basis wedge. -/
public theorem rationalRepresentationExteriorWedgeCoefficient_apply
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    {n : ℕ} (c : Fin n ↪o Fin (Module.finrank k V))
    (L : Module.Dual k (⋀[k]^n V)) (g : Variety.Point G) :
    rationalRepresentationExteriorWedgeCoefficient ρ e f c L g =
      L (exteriorPower.map n (ρ.action g : Module.End k V)
        (exteriorPower.ιMulti k n (fun i => e (c i)))) := by
  let x : ⋀[k]^n V :=
    exteriorPower.map n (ρ.action g : Module.End k V)
      (exteriorPower.ιMulti k n (fun i => e (c i)))
  have hminor (s : Set.powersetCard (Fin (Module.finrank k V)) n) :
      rationalRepresentationExteriorWedgeMinor ρ e f s c g =
        (e.exteriorPower n).repr x s := by
    rw [rationalRepresentationExteriorWedgeMinor]
    let ev := polynomialFunctionPointAlgHom G g
    let Q : Matrix (Fin n) (Fin n) G.PolynomialFunction := fun i j =>
      rationalRepresentationMatrixCoefficient ρ e f
        (Set.powersetCard.ofFinEmbEquiv.symm s i) (c j)
    change ev Q.det = _
    rw [AlgHom.map_det]
    change Matrix.det (fun i j : Fin n =>
      rationalRepresentationMatrixCoefficient ρ e f
        (Set.powersetCard.ofFinEmbEquiv.symm s i) (c j) g) = _
    simp_rw [rationalRepresentationMatrixCoefficient_apply ρ e f hf]
    rw [exteriorPower.basis_repr_apply]
    rw [show x = exteriorPower.ιMulti k n
        (fun i => ((ρ.action g : Module.End k V) (e (c i)))) by
      dsimp [x]
      rw [exteriorPower.map_apply_ιMulti]
      congr 1]
    rw [exteriorPower.ιMultiDual_apply_ιMulti]
    rw [← Matrix.det_transpose]
    congr 1
  rw [rationalRepresentationExteriorWedgeCoefficient]
  let ev := polynomialFunctionPointAlgHom G g
  change ev (∑ s, algebraMap k G.PolynomialFunction
      (L (e.exteriorPower n s)) *
        rationalRepresentationExteriorWedgeMinor ρ e f s c) = _
  rw [map_sum]
  simp_rw [map_mul]
  simp_rw [ev.commutes]
  change (∑ s, L (e.exteriorPower n s) *
      rationalRepresentationExteriorWedgeMinor ρ e f s c g) = _
  simp_rw [hminor]
  change (∑ s, L (e.exteriorPower n s) * (e.exteriorPower n).repr x s) = L x
  calc
    (∑ s, L (e.exteriorPower n s) * (e.exteriorPower n).repr x s) =
        L (∑ s, (e.exteriorPower n).repr x s • e.exteriorPower n s) := by
          simp only [map_sum, map_smul, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    _ = L x := by rw [(e.exteriorPower n).sum_repr]

/-- Replacing one coordinate covector in the exterior pairing produces the
corresponding single-row replacement minor. -/
public theorem rationalRepresentationExteriorWedgeCoefficient_replacement
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    {n : ℕ} (c : Fin n ↪o Fin (Module.finrank k V))
    (i₀ : Fin n) (a : Fin (Module.finrank k V)) :
    rationalRepresentationExteriorWedgeCoefficient ρ e f c
        (exteriorPower.pairingDual k V n
          (exteriorPower.ιMulti k n
            (fun j => e.coord (Function.update (fun x => c x) i₀ a j)))) =
      Matrix.det (fun i j : Fin n =>
        rationalRepresentationMatrixCoefficient ρ e f
          (Function.update (fun x => c x) i₀ a i) (c j)) := by
  apply Variety.PolynomialFunction.ext
  intro g
  rw [rationalRepresentationExteriorWedgeCoefficient_apply ρ e f hf]
  rw [exteriorPower.map_apply_ιMulti]
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  let Q : Matrix (Fin n) (Fin n) G.PolynomialFunction := fun i j =>
    rationalRepresentationMatrixCoefficient ρ e f
      (Function.update (fun x => c x) i₀ a i) (c j)
  let ev := polynomialFunctionPointAlgHom G g
  change Matrix.det (fun i j : Fin n =>
      e.coord (Function.update (fun x => c x) i₀ a j)
        ((ρ.action g : Module.End k V) (e (c i)))) = ev Q.det
  rw [AlgHom.map_det]
  let R : Matrix (Fin n) (Fin n) k := fun i j => ev (Q i j)
  change Matrix.det (fun i j : Fin n =>
      e.coord (Function.update (fun x => c x) i₀ a j)
        ((ρ.action g : Module.End k V) (e (c i)))) = R.det
  calc
    Matrix.det (fun i j : Fin n =>
        e.coord (Function.update (fun x => c x) i₀ a j)
          ((ρ.action g : Module.End k V) (e (c i)))) = R.transpose.det := by
      congr 1
      ext i j
      dsimp [R, Q, ev]
      change e.coord (Function.update (fun x => c x) i₀ a j)
          ((ρ.action g : Module.End k V) (e (c i))) =
        rationalRepresentationMatrixCoefficient ρ e f
          (Function.update (fun x => c x) i₀ a j) (c i) g
      exact (rationalRepresentationMatrixCoefficient_apply ρ e f hf
        (Function.update (fun x => c x) i₀ a j) (c i) g).symm
    _ = R.det := Matrix.det_transpose R

/-- A replacement exterior covector reads the corresponding original
representation differential coordinate. -/
public theorem rationalRepresentationExteriorWedgeDifferential_replacement
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G) {n : ℕ}
    (c : Fin n ↪o Fin (Module.finrank k V)) (i₀ : Fin n)
    (a : Fin (Module.finrank k V)) (ha : a ∉ Set.range c) :
    (exteriorPower.pairingDual k V n
        (exteriorPower.ιMulti k n
          (fun j => e.coord (Function.update (fun x => c x) i₀ a j))))
        (rationalRepresentationExteriorWedgeDifferential ρ e f c D) =
      e.coord a (rationalRepresentationDifferential ρ e f D (e (c i₀))) := by
  rw [rationalRepresentationExteriorWedgeDifferential_coefficient]
  rw [rationalRepresentationExteriorWedgeCoefficient_replacement ρ e f hf]
  exact rationalRepresentationDifferential_singleRowMinor ρ e f hf D
    c.toEmbedding i₀ a ha

/-- If the infinitesimal exterior vector remains on its original line, every
outside-row, inside-column coordinate of the original differential vanishes. -/
public theorem rationalRepresentationDifferential_outside_coord_eq_zero_of_exteriorWedge_line
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G) {n : ℕ}
    (c : Fin n ↪o Fin (Module.finrank k V))
    (hline : rationalRepresentationExteriorWedgeDifferential ρ e f c D ∈
      k ∙ exteriorPower.ιMulti k n (fun i => e (c i)))
    (i₀ : Fin n) (a : Fin (Module.finrank k V))
    (ha : a ∉ Set.range c) :
    e.coord a (rationalRepresentationDifferential ρ e f D (e (c i₀))) = 0 := by
  let L : Module.Dual k (⋀[k]^n V) :=
    exteriorPower.pairingDual k V n
      (exteriorPower.ιMulti k n
        (fun j => e.coord (Function.update (fun x => c x) i₀ a j)))
  have hp : L (exteriorPower.ιMulti k n (fun i => e (c i))) = 0 := by
    dsimp [L]
    rw [exteriorPower.pairingDual_ιMulti_ιMulti]
    apply Matrix.det_eq_zero_of_column_eq_zero i₀
    intro i
    simp only [Matrix.of_apply]
    rw [show Function.update (fun x => c x) i₀ a i₀ = a by simp]
    have hac : a ≠ c i := by
      intro h
      exact ha ⟨i, h.symm⟩
    rw [Module.Basis.coord_apply, Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne hac
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hline
  have hL : L (rationalRepresentationExteriorWedgeDifferential ρ e f c D) = 0 := by
    rw [← hz, map_smul, hp, smul_zero]
  rw [show L (rationalRepresentationExteriorWedgeDifferential ρ e f c D) =
      e.coord a (rationalRepresentationDifferential ρ e f D (e (c i₀))) by
    exact rationalRepresentationExteriorWedgeDifferential_replacement
      ρ e f hf D c i₀ a ha] at hL
  exact hL

/-- Infinitesimal stability of a basis top-wedge line forces the original
representation differential to preserve the spanned subspace. -/
public theorem rationalRepresentationDifferential_preserves_initialSpan_of_exteriorWedge_line
    (ρ : RationalRepresentation G V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k V))
    (hf : ∀ g, glPointEquivOf k V e (f.onPoints g) = ρ.action g)
    (D : IdentityPointDerivation G) {n : ℕ}
    (c : Fin n ↪o Fin (Module.finrank k V))
    (hline : rationalRepresentationExteriorWedgeDifferential ρ e f c D ∈
      k ∙ exteriorPower.ιMulti k n (fun i => e (c i))) :
    ∀ v ∈ Submodule.span k (Set.range fun i => e (c i)),
      rationalRepresentationDifferential ρ e f D v ∈
        Submodule.span k (Set.range fun i => e (c i)) := by
  intro v hv
  refine Submodule.span_induction (p := fun v _ =>
    rationalRepresentationDifferential ρ e f D v ∈
      Submodule.span k (Set.range fun i => e (c i))) ?_ ?_ ?_ ?_ hv
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [← e.sum_repr
      (rationalRepresentationDifferential ρ e f D (e (c i)))]
    apply Submodule.sum_mem
    intro a haFin
    by_cases ha : a ∈ Set.range c
    · obtain ⟨j, rfl⟩ := ha
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · have hzero :=
        rationalRepresentationDifferential_outside_coord_eq_zero_of_exteriorWedge_line
          ρ e f hf D c hline i a ha
      change e.repr
        (rationalRepresentationDifferential ρ e f D (e (c i))) a = 0 at hzero
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hxmem hymem
    rw [map_add]
    exact Submodule.add_mem _ hxmem hymem
  · intro z x hx hxmem
    rw [map_smul]
    exact Submodule.smul_mem _ z hxmem

end Theory.AlgebraicGroup.Bor1
