module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Trace
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Elementary two-subgroups and their largest centralizers in PSL₄(3)

Lifts of distinct elements of an elementary two-subgroup are orthogonal for
the matrix trace pairing: their quotient is a nonidentity projective involution,
whose lifts have trace zero. Self-pairing has trace four, which is one in F₃.
The lifts are therefore linearly independent in the sixteen-dimensional matrix
algebra. At equality they span the algebra. Every projective centralizer lift
has square commuting with this basis, hence with every matrix; its square is
central in SL₄(3). The projective centralizer consequently has exponent two.

The trace-duality organization adapts the repository's
`ClassicalUnitary/UnitaryFourThree/ElementaryLocal/TraceBound.lean` to the
actual SL central quotient; all trace premises are discharged here.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4) on printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Subgroup
noncomputable section
namespace Matrix.PSL4Three.LocalThree

private def liftRep (A : Subgroup P) (a : A) : SL :=
  Classical.choose (project_surjective (a : P))

private theorem project_liftRep (A : Subgroup P) (a : A) : project (liftRep A a) = a :=
  Classical.choose_spec (project_surjective (a : P))

private theorem trace_pair_zero {A : Subgroup P} [IsElementaryAbelian 2 A]
    (a b : A) (hab : a ≠ b) :
    Matrix.trace (((liftRep A b)⁻¹).val * (liftRep A a).val) = 0 := by
  have hne : project ((liftRep A b)⁻¹ * liftRep A a) ≠ 1 := by
    intro he
    apply hab
    apply Subtype.ext
    rw [map_mul, map_inv, project_liftRep, project_liftRep] at he
    exact (inv_mul_eq_one.mp he).symm
  have hsq : (project ((liftRep A b)⁻¹ * liftRep A a)) ^ 2 = 1 := by
    rw [map_mul, map_inv, project_liftRep, project_liftRep]
    exact congrArg (fun z : A => (z : P))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (b⁻¹ * a))
  exact trace_eq_zero_of_projective_involution _ hne hsq

private theorem trace_pair_one (A : Subgroup P) (a : A) :
    Matrix.trace (((liftRep A a)⁻¹).val * (liftRep A a).val) = 1 := by
  change Matrix.trace (((liftRep A a)⁻¹ * liftRep A a : SL) : Mat) = 1
  rw [inv_mul_cancel]
  rw [SpecialLinearGroup.coe_one, Matrix.trace_one]
  decide

private theorem liftRep_linearIndependent (A : Subgroup P) [IsElementaryAbelian 2 A] :
    LinearIndependent (ZMod 3) (fun a : A => (liftRep A a : Mat)) := by
  let := Fintype.ofFinite A
  let v : A → Mat := fun a => (liftRep A a : Mat)
  change LinearIndependent (ZMod 3) v
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  let L : Mat →ₗ[ZMod 3] ZMod 3 :=
    (Matrix.traceLinearMap (Fin 4) (ZMod 3) (ZMod 3)).comp
      (LinearMap.mulLeft (ZMod 3) ((liftRep A a)⁻¹).val)
  have hz : ∑ i, c i * Matrix.trace (((liftRep A a)⁻¹).val * v i) = 0 := by
    have hzero : L (∑ i, c i • v i) = 0 := by rw [hc]; simp [L]
    simpa [L, Finset.smul_sum, Matrix.mul_sum, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul] using hzero
  have hsingle : (∑ i, c i * Matrix.trace (((liftRep A a)⁻¹).val * v i)) =
      c a * Matrix.trace (((liftRep A a)⁻¹).val * v a) := by
    rw [Finset.sum_eq_single a]
    · intro b _ hba
      rw [trace_pair_zero b a hba]
      simp
    · intro haa
      exact False.elim (haa (Finset.mem_univ a))
  rw [hsingle, trace_pair_one A a] at hz
  simpa using hz

/-- Every elementary two-subgroup has at most sixteen elements. -/
public theorem elementary_card_le_sixteen (A : Subgroup P) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 16 := by
  let := hA
  let := Fintype.ofFinite A
  have hcard := (liftRep_linearIndependent A).fintype_card_le_finrank
  change Fintype.card A ≤ Module.finrank (ZMod 3) (Fin 4 → Fin 4 → ZMod 3) at hcard
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hcard
  rw [Nat.card_eq_fintype_card]
  norm_num at hcard ⊢
  exact hcard

/-- At equality every element of the actual projective centralizer squares to one. -/
public theorem centralizer_square_of_card_eq_sixteen (A : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16)
    (c : P) (hc : c ∈ centralizer (A : Set P)) : c ^ 2 = 1 := by
  let := hA
  let := Fintype.ofFinite A
  let v : A → Mat := fun a => (liftRep A a : Mat)
  have hspan : Submodule.span (ZMod 3) (Set.range v) = ⊤ := by
    apply (liftRep_linearIndependent A).span_eq_top_of_card_eq_finrank
    rw [Nat.card_eq_fintype_card] at hcard
    change Fintype.card A = Module.finrank (ZMod 3) (Fin 4 → Fin 4 → ZMod 3)
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    norm_num at hcard ⊢
    exact hcard
  obtain ⟨x, rfl⟩ := project_surjective c
  let W : Submodule (ZMod 3) Mat := {
    carrier := {z | ((x ^ 2 : SL) : Mat) * z = z * ((x ^ 2 : SL) : Mat)}
    zero_mem' := by simp
    add_mem' := by
      intro z w hz hw
      change ((x ^ 2 : SL) : Mat) * (z + w) = (z + w) * ((x ^ 2 : SL) : Mat)
      rw [Matrix.mul_add, Matrix.add_mul, hz, hw]
    smul_mem' := by
      intro r z hz
      change ((x ^ 2 : SL) : Mat) * (r • z) = (r • z) * ((x ^ 2 : SL) : Mat)
      rw [Matrix.mul_smul, Matrix.smul_mul, hz] }
  have hWgen : Set.range v ⊆ W := by
    rintro z ⟨a, rfl⟩
    have hcomm : Commute (project x) (project (liftRep A a)) := by
      rw [project_liftRep]
      exact (mem_centralizer_iff.mp hc a a.property).symm
    exact congrArg (fun g : SL => (g : Mat))
      (square_commute_of_project_commute x (liftRep A a) hcomm).eq
  have hWtop : W = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hWgen
  rw [← map_pow, project_eq_one_iff]
  apply mem_center_iff.mpr
  intro z
  apply Subtype.ext
  exact (show ((x ^ 2 : SL) : Mat) * (z : Mat) = (z : Mat) * ((x ^ 2 : SL) : Mat) from
    (show (z : Mat) ∈ W by rw [hWtop]; trivial)).symm

/-- The centralizer of an elementary subgroup of order sixteen has no factor of three. -/
public theorem centralizer_not_three_dvd_of_card_eq_sixteen (A : Subgroup P)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ¬ 3 ∣ Nat.card (centralizer (A : Set P)) := by
  intro hdiv
  obtain ⟨c, horder⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  have hsq := centralizer_square_of_card_eq_sixteen A hA hcard c.1 c.2
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [Subgroup.orderOf_coe, horder] at hdvd
  norm_num at hdvd
end Matrix.PSL4Three.LocalThree
