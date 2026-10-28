module

public import Theory.Character.ModularBlock.IsotypicLattice
public import Theory.Character.ModularBlock.NagaoComplement

/-!
# Projector Trace

Multiplication by the denominator-cleared complex projector of an
irreducible character reads off its degree times the trace of the other
factor. The proof expands the group-algebra action in its basis and compares
coefficients with the character formula. The companion trace expansion with
a fixed left group element and the centralizer embedding/action comparison
provide the generic algebra needed by the later characterwise projection
argument. The finite-group hypotheses of the historical public API remain
explicit, including the action-comparison theorem.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseProjection.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.CharacterwiseProjection

open ModularBlock PrincipalBlockConstruction

universe u v

attribute [local instance] Fintype.ofFinite

variable {G : Type u} [Group G] [finG : Finite G]

theorem trace_left_groupAlgebra_mul
    {H : Type v} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ H V) (x : H)
    (a : MonoidAlgebra ℂ H) :
    LinearMap.trace ℂ V
        (rho x * rho.asAlgebraHom a) =
      ∑ h : H, a.coeff h * rho.character (x * h) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, mul_add, map_add, ha, hb]
      change
        (∑ h : H, a.coeff h * rho.character (x * h)) +
            ∑ h : H, b.coeff h * rho.character (x * h) =
          ∑ h : H,
            (a.coeff h + b.coeff h) * rho.character (x * h)
      simp only [add_mul, Finset.sum_add_distrib]
  | single h r =>
      have hmap :
          rho.asAlgebraHom (MonoidAlgebra.single h r) = r • rho h := by
        rw [show (MonoidAlgebra.single h r : MonoidAlgebra ℂ H) =
            r • MonoidAlgebra.single h (1 : ℂ) by simp]
        rw [map_smul, Representation.asAlgebraHom_single_one]
      rw [hmap, Algebra.mul_smul_comm, map_smul]
      change r * LinearMap.trace ℂ V (rho x * rho h) =
        ∑ y : H, (MonoidAlgebra.single h r).coeff y *
          LinearMap.trace ℂ V (rho (x * y))
      rw [show rho x * rho h = rho (x * h) by rw [← map_mul]]
      rw [Finset.sum_eq_single h]
      · rw [show (MonoidAlgebra.single h r).coeff h = r by
          change (Finsupp.single h r) h = r
          simp]
      · intro y _hy hyh
        rw [show (MonoidAlgebra.single h r).coeff y = 0 by
          change (Finsupp.single h r) y = 0
          exact Finsupp.single_eq_of_ne hyh]
        exact zero_mul _
      · simp

/-! Multiplication by the denominator-cleared primitive projector reads off
the trace of the left factor in the chosen irreducible representation. -/

theorem mul_complexCharacterProjectorNumerator_coeff_one
    (d : PrincipalCongruenceBlockData G) (i : d.I)
    {n : ℕ} (rho : Representation ℂ G (Fin n → ℂ))
    (hrho : d.chi i = characterClassFunction rho)
    (a : MonoidAlgebra ℂ G) :
    (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
      d.chi i (ConjClasses.mk (1 : G)) *
        LinearMap.trace ℂ (Fin n → ℂ) (rho.asAlgebraHom a) := by
  classical
  have hcoeff :
      (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
        d.chi i (ConjClasses.mk (1 : G)) *
          ∑ g : G, a.coeff g * d.chi i (ConjClasses.mk g) := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
        rw [add_mul, MonoidAlgebra.coeff_add]
        change
          (a * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 +
              (b * IsotypicLattice.complexCharacterProjectorNumerator d i).coeff 1 =
            _
        rw [ha, hb]
        simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul,
          Finset.sum_add_distrib]
        ring
    | single g r =>
        rw [MonoidAlgebra.coeff_single_mul_apply]
        rw [IsotypicLattice.complexCharacterProjectorNumerator_apply]
        simp only [mul_one, inv_inv]
        rw [Finset.sum_eq_single g]
        · change r *
              (d.chi i (ConjClasses.mk (1 : G)) *
                d.chi i (ConjClasses.mk g)) =
            d.chi i (ConjClasses.mk (1 : G)) *
              ((MonoidAlgebra.single g r).coeff g *
                d.chi i (ConjClasses.mk g))
          rw [show (MonoidAlgebra.single g r).coeff g = r by
            change (Finsupp.single g r) g = r
            simp]
          ring
        · intro y _hy hyg
          rw [show (MonoidAlgebra.single g r).coeff y = 0 by
            change (Finsupp.single g r) y = 0
            exact Finsupp.single_eq_of_ne hyg]
          simp
        · simp
  rw [hcoeff, IsotypicLattice.groupAlgebra_trace]
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [show d.chi i (ConjClasses.mk g) = rho.character g by
    rw [hrho]
    rfl]

/-! The ambient representation sees an embedded centralizer algebra through
its restricted representation. -/

omit finG in
theorem asAlgebraHom_centralizerSubtypeMap
    [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (z : G)
    (b : MonoidAlgebra ℂ (Subgroup.centralizer ({z} : Set G))) :
    rho.asAlgebraHom (ModularBlock.NagaoComplement.centralizerSubtypeMap z b) =
      Representation.asAlgebraHom
        (rho.comp (Subgroup.centralizer ({z} : Set G)).subtype) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => rw [map_add, map_add, hb, hc, map_add]
  | single h r =>
      have hsubtype :
          ModularBlock.NagaoComplement.centralizerSubtypeMap z
              (MonoidAlgebra.single h r) =
            (MonoidAlgebra.single (h : G) r : MonoidAlgebra ℂ G) := by
        simp [ModularBlock.NagaoComplement.centralizerSubtypeMap,
          MonoidAlgebra.mapDomainRingHom_apply]
      rw [hsubtype]
      rw [show (MonoidAlgebra.single (h : G) r : MonoidAlgebra ℂ G) =
          r • MonoidAlgebra.single (h : G) 1 by simp]
      rw [show (MonoidAlgebra.single h r :
          MonoidAlgebra ℂ (Subgroup.centralizer ({z} : Set G))) =
          r • MonoidAlgebra.single h 1 by simp]
      rw [map_smul, map_smul,
        Representation.asAlgebraHom_single_one,
        Representation.asAlgebraHom_single_one]
      rfl


end ModularBlock.CharacterwiseProjection

