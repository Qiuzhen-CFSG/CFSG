module

public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm.Certificates

/-!
# Cubic normal form on the minus extraspecial group

Every nonidentity automorphism of the quaternion–dihedral central product
whose cube is the identity is conjugate to the standard quaternion cycle.
The equivalence acts on the actual 32-element group, including its center.

An automorphism is determined by four generator images. The presentation
relations and cubic equation put these images in an exhaustive checked table.
Each row supplies inverse coordinate maps and multiplication by generators;
canonical words extend the latter to full multiplicativity. Its checked
action equation then gives the required conjugacy on every group element.

Source: Aschbacher, *Sporadic Groups* (1994), the final local construction in
47.5, p.263, and the quaternion–dihedral coordinates on p.265. This discharges
`HasCubicNormalForm` in the actual-core construction; it assumes no quotient
normal form or unproved automorphism classification.
-/

@[expose] public section
namespace MinusExtraspecial.CubicAction.NormalForm

theorem encode_mul (x y : Model) : encode (x * y) = mul (encode x) (encode y) := by
  have h := congrArg encode (decode_mul (encode x) (encode y))
  simpa only [encode_decode, decode_encode] using h.symm

/-- The certificate supplies an actual multiplicative equivalence of the model. -/
def rowEquiv (t : Row) (ht : rowCheck t) : Model ≃* Model where
  toFun x := decode (table t.e (encode x))
  invFun x := decode (table t.d (encode x))
  left_inv x := by
    simp only [rowCheck, Bool.and_eq_true, and_assoc] at ht
    have h := beq_iff_eq.mp (List.all_eq_true.mp ht.2.1 (encode x) (mem_all _))
    dsimp only
    rw [encode_decode, h, decode_encode]
  right_inv x := by
    simp only [rowCheck, Bool.and_eq_true, and_assoc] at ht
    have h := beq_iff_eq.mp (List.all_eq_true.mp ht.2.2.1 (encode x) (mem_all _))
    dsimp only
    rw [encode_decode, h, decode_encode]
  map_mul' := by
    simp only [rowCheck, Bool.and_eq_true, and_assoc] at ht
    apply multiplicative_of_generators (fun x => decode (table t.e (encode x)))
    intro x i
    have h := List.all_eq_true.mp (List.all_eq_true.mp ht.1 (encode x) (mem_all _))
      (encode (generators i)) (gens_mem i)
    have hd := congrArg decode (beq_iff_eq.mp h)
    simpa only [encode_mul, decode_mul] using hd

theorem rowEquiv_action (t : Row) (ht : rowCheck t) (x : B) :
    rowEquiv t ht (decode (word t.a x)) = cycle (rowEquiv t ht (decode x)) := by
  have ht' := ht
  simp only [rowCheck, Bool.and_eq_true, and_assoc] at ht'
  have h := List.all_eq_true.mp ht'.2.2.2 x (mem_all x)
  have hd := congrArg decode (beq_iff_eq.mp h)
  change decode (table t.e (encode (decode (word t.a x)))) =
    cycle (decode (table t.e (encode (decode x))))
  simpa only [encode_decode, decode_sigma] using hd

end MinusExtraspecial.CubicAction.NormalForm
namespace MinusExtraspecial.CubicAction
open NormalForm

/-- Every nonidentity cubic automorphism is conjugate to the literal quaternion cycle. -/
theorem hasCubicNormalForm : HasCubicNormalForm := by
  intro a ha3 hane
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have hc := coverage_all (images a).u h1 (images a).v h2 h3
    (images a).r h4 h5 h6 (images a).s h7 h8 h9 h10
    (cubic_aut a ha3) (nontrivial_aut a hane)
  obtain ⟨t, ht, hit⟩ := List.any_eq_true.mp hc
  have hit' : t.a = images a := of_decide_eq_true hit
  have hv := List.all_eq_true.mp rows_valid t ht
  refine ⟨rowEquiv t hv, ?_⟩
  intro q
  have h := rowEquiv_action t hv (encode q)
  rw [hit', decode_word, decode_encode] at h
  exact h

end MinusExtraspecial.CubicAction
