module

public import Theory.AlgebraicGroup.RootSystems.GeckScalarExtensionCompatibility
public import Theory.AlgebraicGroup.RootSystems.GeckTitsRootWeight
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-!
# Rational multiplicity one for irreducible integral Geck root spaces

For a finite irreducible reduced crystallographic root system, two integral Geck root operators
transported by Tits words are rationally proportional when the corresponding reflection words
reach the same root.  The proof first maps the integral matrices into Geck's Lie algebra over an
algebraic closure of `ℚ`.  Scalar compatibility of the Tits lifts puts both nonzero matrices in
the same root space, and Mathlib's Killing-root theorem makes that root space one-dimensional.
A nonzero rational matrix coordinate then forces the algebraic proportionality scalar to lie in
`ℚ`, giving the claimed descent.

The scalar-extension model and Tits-action calculations are isolated in lower modules.  This
module imports only those interfaces, ultimately depending on `IntegralTitsCoherence` and the
minimal Mathlib Geck/Lie prerequisites; no reducible component, route-coherence, all-root
operator, bracket-transport, or integral primitivity argument is used.
-/

namespace RootPairing.IntegralGeckConstruction

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1000000

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private noncomputable def geckCartanBasis :
    Module.Basis b.support R
      (RootPairing.GeckConstruction.cartanSubalgebra' b) :=
  Module.Basis.mk
    (v := RootPairing.GeckConstruction.h' (P := P) (b := b)) (by
      apply LinearIndependent.of_comp
        ((RootPairing.GeckConstruction.lieAlgebra b).subtype.comp
          (RootPairing.GeckConstruction.cartanSubalgebra' b).subtype)
      exact RootPairing.GeckConstruction.linearIndependent_h b)
    (by rw [RootPairing.GeckConstruction.span_range_h'_eq_top])

private lemma geckCartanBasis_apply (l : b.support) :
    geckCartanBasis (P := P) (R := R) (b := b) l =
      RootPairing.GeckConstruction.h' l := by
  rw [geckCartanBasis]
  apply Module.Basis.mk_apply

private noncomputable def geckWeightLinear (k : ι) :
    RootPairing.GeckConstruction.cartanSubalgebra' b →ₗ[R] R :=
  (geckCartanBasis (P := P) (R := R) (b := b)).constr R
    (fun l => P.pairing k l)

private lemma geckWeightLinear_h' (k : ι) (l : b.support) :
    geckWeightLinear (P := P) (R := R) (b := b) k
        (RootPairing.GeckConstruction.h' l) = P.pairing k l := by
  rw [← geckCartanBasis_apply (P := P) (R := R) (b := b) l]
  apply Module.Basis.constr_basis

private lemma geckWeightLinear_ne_zero (k : ι) :
    geckWeightLinear (P := P) (R := R) (b := b) k ≠ 0 := by
  obtain ⟨j, hj, hj0⟩ := b.exists_mem_support_pos_pairingIn_ne_zero k
  have hrev : P.pairingIn ℤ k j ≠ 0 := by
    rw [ne_eq, P.pairingIn_eq_zero_iff]
    exact hj0
  have hpair : P.pairing k j ≠ 0 := by
    rw [← P.algebraMap_pairingIn ℤ]
    exact (FaithfulSMul.algebraMap_eq_zero_iff ℤ R).not.mpr hrev
  intro hzero
  apply hpair
  have h := LinearMap.congr_fun hzero
    (RootPairing.GeckConstruction.h' (b := b) ⟨j, hj⟩)
  simpa only [geckWeightLinear_h', LinearMap.zero_apply] using h

private lemma mem_geckWeightSpace_of_hasRootWeight (k : ι)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hXmem : X ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hXweight : HasRootWeight (P := P) (b := b) k X) :
    (⟨X, hXmem⟩ : RootPairing.GeckConstruction.lieAlgebra b) ∈
      LieModule.genWeightSpace (RootPairing.GeckConstruction.lieAlgebra b)
        (geckWeightLinear (P := P) (R := R) (b := b) k) := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let H := RootPairing.GeckConstruction.cartanSubalgebra' b
  let X' : L := ⟨X, hXmem⟩
  rw [LieModule.mem_genWeightSpace]
  intro x
  have hx : x ∈ Submodule.span R (Set.range
      (RootPairing.GeckConstruction.h' (P := P) (b := b))) := by
    rw [RootPairing.GeckConstruction.span_range_h'_eq_top]
    exact Submodule.mem_top
  have heigen : ∀ y : H, y ∈ Submodule.span R (Set.range
      (RootPairing.GeckConstruction.h' (P := P) (b := b))) →
      ⁅(y : L), X'⁆ =
        geckWeightLinear (P := P) (R := R) (b := b) k y • X' := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨l, rfl⟩
        rw [geckWeightLinear_h']
        exact Subtype.ext (hXweight l)
    | zero => simp
    | add y z _ _ hy hz =>
        rw [show ((↑(y + z) : L)) = (y : L) + (z : L) by
          exact map_add H.subtype y z]
        rw [add_lie, map_add, hy, hz, add_smul]
    | smul c y _ hy =>
        rw [show ((↑(c • y) : L)) = c • (y : L) by
          exact map_smul H.subtype c y]
        rw [smul_lie, map_smul, hy, smul_smul]
        simp only [smul_eq_mul]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  exact sub_eq_zero.mpr (heigen x hx)

private lemma undo_titsConjugate (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsWordInv word * titsConjugate word A * titsWord word = A := by
  rw [titsConjugate_apply]
  calc
    titsWordInv word * (titsWord word * A * titsWordInv word) * titsWord word =
        (titsWordInv word * titsWord word) * A *
          (titsWordInv word * titsWord word) := by noncomm_ring
    _ = A := by rw [titsWord_inv_mul, Matrix.one_mul, Matrix.mul_one]

private lemma titsConjugate_ne_zero (word : List b.support) (i : b.support) :
    titsConjugate word (eMatrix i) ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun A => titsWordInv word * A * titsWord word) hzero
  rw [undo_titsConjugate, Matrix.mul_zero, Matrix.zero_mul] at h
  have hvec := eMatrix_mulVec_v_neg (P := P) i
  rw [h, Matrix.zero_mulVec] at hvec
  have hentry := congrFun hvec (Sum.inl i)
  simpa [u, Pi.single_apply] using hentry

private lemma map_titsConjugate_ne_zero (word : List b.support) (i : b.support) :
    (titsConjugate word (eMatrix i)).map (algebraMap ℤ R) ≠ 0 := by
  intro hzero
  apply titsConjugate_ne_zero (P := P) word i
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
  simpa using hzero

private lemma exists_scalar_map_titsConjugate_eq
    (w z : List b.support) (i j : b.support)
    (hroot : reflectionWord w (i : ι) = reflectionWord z (j : ι)) :
    ∃ c : R,
      (titsConjugate w (eMatrix i)).map (algebraMap ℤ R) =
        c • (titsConjugate z (eMatrix j)).map (algebraMap ℤ R) := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let H := RootPairing.GeckConstruction.cartanSubalgebra' b
  let k : ι := reflectionWord w i
  let A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    (titsConjugate w (eMatrix i)).map (algebraMap ℤ R)
  let B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    (titsConjugate z (eMatrix j)).map (algebraMap ℤ R)
  have hAmem : A ∈ L := by
    dsimp only [A]
    apply map_titsConjugate_mem_lieAlgebra (P := P) (R := R) (b := b) w
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P) i
  have hBmem : B ∈ L := by
    dsimp only [B]
    apply map_titsConjugate_mem_lieAlgebra (P := P) (R := R) (b := b) z
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P) j
  have hA0 : A ≠ 0 := map_titsConjugate_ne_zero (P := P) (R := R) w i
  have hB0 : B ≠ 0 := map_titsConjugate_ne_zero (P := P) (R := R) z j
  have hAspace : (⟨A, hAmem⟩ : L) ∈
      LieModule.genWeightSpace L
        (geckWeightLinear (P := P) (R := R) (b := b) k) :=
    mem_geckWeightSpace_of_hasRootWeight (P := P) (R := R) (b := b) k hAmem
      (by simpa only [A, k] using
        map_titsConjugate_hasRootWeight (P := P) (R := R) (b := b) w i)
  have hBspace : (⟨B, hBmem⟩ : L) ∈
      LieModule.genWeightSpace L
        (geckWeightLinear (P := P) (R := R) (b := b) k) :=
    mem_geckWeightSpace_of_hasRootWeight (P := P) (R := R) (b := b) k hBmem
      (by simpa only [B, k, hroot] using
        map_titsConjugate_hasRootWeight (P := P) (R := R) (b := b) z j)
  have hspace0 : LieModule.genWeightSpace L
      (geckWeightLinear (P := P) (R := R) (b := b) k) ≠ ⊥ := by
    intro hbot
    rw [LieSubmodule.eq_bot_iff] at hbot
    apply hA0
    have hzero := hbot ⟨A, hAmem⟩ hAspace
    exact congrArg (fun x : L =>
      ((x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))) hzero
  let α : LieModule.Weight R H L :=
    ⟨geckWeightLinear (P := P) (R := R) (b := b) k, hspace0⟩
  have hAroot : (⟨A, hAmem⟩ : L) ∈ LieAlgebra.rootSpace H α := hAspace
  have hBroot : (⟨B, hBmem⟩ : L) ∈ LieAlgebra.rootSpace H α := hBspace
  have hα : α.IsNonZero := by
    intro hzero
    apply geckWeightLinear_ne_zero (P := P) (R := R) (b := b) k
    apply LinearMap.ext
    intro x
    exact congrFun hzero x
  have hfin : Module.finrank R (LieAlgebra.rootSpace H α) = 1 :=
    LieAlgebra.IsKilling.finrank_rootSpace_eq_one α hα
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hfin
  obtain ⟨a, ha⟩ := hv ⟨⟨A, hAmem⟩, hAroot⟩
  obtain ⟨d, hd⟩ := hv ⟨⟨B, hBmem⟩, hBroot⟩
  have hd0 : d ≠ 0 := by
    intro hdzero
    apply hB0
    have := congrArg (fun x : LieAlgebra.rootSpace H α => ((x : L) :
      Matrix (b.support ⊕ ι) (b.support ⊕ ι) R)) hd
    simpa [hdzero, B] using this.symm
  refine ⟨a / d, ?_⟩
  have hscaled := congrArg (fun x : LieAlgebra.rootSpace H α => ((x : L) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R))
      (show (a / d) • (d • v) = a • v by
        rw [smul_smul, div_mul_cancel₀ a hd0])
  simpa [ha, hd, A, B] using hscaled.symm

private lemma map_rat_map_eq_map
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    (A.map (algebraMap ℤ ℚ)).map (algebraMap ℚ R) =
      A.map (algebraMap ℤ R) := by
  ext x y
  simpa only [Matrix.map_apply] using
    (IsScalarTower.algebraMap_apply ℤ ℚ R (A x y)).symm

private lemma exists_rat_smul_of_map_eq_smul
    {A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℚ}
    (hB : B ≠ 0) (c : R)
    (h : A.map (algebraMap ℚ R) = c • B.map (algebraMap ℚ R)) :
    ∃ q : ℚ, A = q • B := by
  obtain ⟨x₀, y₀, hBxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hB
    ext x y
    exact hnone x y
  let q : ℚ := A x₀ y₀ / B x₀ y₀
  have hBmap : algebraMap ℚ R (B x₀ y₀) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ R)).2 hBxy
  have hcoord := congrFun (congrFun h x₀) y₀
  have hc : c = algebraMap ℚ R q := by
    calc
      c = algebraMap ℚ R (A x₀ y₀) / algebraMap ℚ R (B x₀ y₀) := by
        apply (eq_div_iff hBmap).2
        simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using hcoord.symm
      _ = algebraMap ℚ R (A x₀ y₀ / B x₀ y₀) :=
        (map_div₀ (algebraMap ℚ R) _ _).symm
      _ = algebraMap ℚ R q := by rfl
  refine ⟨q, ?_⟩
  ext x y
  apply (FaithfulSMul.algebraMap_injective ℚ R)
  have hxy := congrFun (congrFun h x) y
  simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← hc] using hxy

/-- Equal reflected roots give rationally proportional integral Geck root vectors.

The scalar is first obtained after mapping the integral matrices into the algebraically closed
coefficient field of the root pairing, where Geck's Lie algebra has one-dimensional root spaces.
The last step descends that scalar to `ℚ` using a nonzero rational matrix entry. -/
private theorem exists_rat_smul_titsConjugate_of_reflectionWord_eq_of_isAlgClosed
    (w z : List b.support) (i j : b.support)
    (hroot : reflectionWord w (i : ι) = reflectionWord z (j : ι)) :
    ∃ q : ℚ,
      (titsConjugate w (eMatrix i)).map (algebraMap ℤ ℚ) =
        q • (titsConjugate z (eMatrix j)).map (algebraMap ℤ ℚ) := by
  let A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
    titsConjugate w (eMatrix i)
  let B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
    titsConjugate z (eMatrix j)
  obtain ⟨c, hc⟩ := exists_scalar_map_titsConjugate_eq
    (P := P) (R := R) (b := b) w z i j hroot
  have hB : B.map (algebraMap ℤ ℚ) ≠ 0 := by
    intro hzero
    apply titsConjugate_ne_zero (P := P) z j
    apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℚ)
    simpa [B] using hzero
  apply exists_rat_smul_of_map_eq_smul (P := P) (R := R) (b := b) hB c
  simpa only [A, B, map_rat_map_eq_map] using hc

end
end RootPairing.IntegralGeckConstruction

namespace RootPairing.IntegralGeckConstruction

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- Equal reflected roots give rationally proportional integral Geck root vectors.

The proof extends the integral coordinate realization to an algebraic closure of `ℚ`, where
Geck's semisimplicity theorem makes the common nonzero root space one-dimensional.  The explicit
integral coordinate model identifies the extended matrices and Tits conjugations with the
original ones.  Finally, a nonzero rational matrix coordinate shows that the proportionality
scalar descends from the algebraic closure to `ℚ`. -/
public theorem exists_rat_smul_titsConjugate_of_reflectionWord_eq
    (w z : List b.support) (i j : b.support)
    (hroot : reflectionWord w (i : ι) = reflectionWord z (j : ι)) :
    ∃ q : ℚ,
      (titsConjugate w (eMatrix i)).map (algebraMap ℤ ℚ) =
        q • (titsConjugate z (eMatrix j)).map (algebraMap ℤ ℚ) := by
  have hroot' :
      reflectionWord (P := scalarExtension (P := P) (b := b))
          (b := scalarExtensionBase (P := P) (b := b)) w (i : ι) =
        reflectionWord (P := scalarExtension (P := P) (b := b))
          (b := scalarExtensionBase (P := P) (b := b)) z (j : ι) := by
    simpa only [scalarExtension_reflectionWord] using hroot
  obtain ⟨q, hq⟩ :=
    exists_rat_smul_titsConjugate_of_reflectionWord_eq_of_isAlgClosed
      (P := scalarExtension (P := P) (b := b)) (R := RatAlgClosure)
      (b := scalarExtensionBase (P := P) (b := b)) w z i j hroot'
  refine ⟨q, ?_⟩
  rw [scalarExtension_eMatrix (P := P) (b := b) i,
    scalarExtension_eMatrix (P := P) (b := b) j,
    scalarExtension_titsConjugate (P := P) (b := b) w,
    scalarExtension_titsConjugate (P := P) (b := b) z] at hq
  exact hq

end
end RootPairing.IntegralGeckConstruction
