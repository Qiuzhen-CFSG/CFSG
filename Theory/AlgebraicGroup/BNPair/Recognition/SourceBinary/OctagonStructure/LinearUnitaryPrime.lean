module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiConstituentKernels
public import Theory.NumberTheory.BinaryPrimitiveDivisor.Separation
public import Theory.Representation.NormalInvariants

/-!
# Separating prime in an octagon linear/unitary pair

When the linear field exponent is larger than twice the unitary exponent, a
prime dividing `2^a - 1` and avoiding `2^(2b) - 1` occurs in the linear
Cartan.  The prime-order actor then centralizes every Weyl conjugate of the
unitary root.  The construction is stated for the actual marked quotient and
keeps the octagon rotation hypothesis in the interface; the fixed-point
argument itself only uses the root-action and unitary Cartan data.

This is the Cartan input for the fixed-section exclusions in Fong--Seitz I
(6F), pp.46--47.  No hexagon movement or six-step root incidence is used.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem prime_actor_trivial_of_irreducible
    {H A : Type*} [Group H] [IsMulCommutative H] [Finite H]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (ρ : H →* MulAut A)
    (ρlin : Representation (ZMod 2) H (Additive A))
    (heq : ∀ h a, ρlin h (Additive.ofMul a) = Additive.ofMul (ρ h a))
    [ρlin.IsIrreducible]
    {t : H} {r : ℕ} (hr : r.Prime) (ht : orderOf t = r)
    (hcard : ¬ r ∣ Nat.card A - 1) : ρ t = 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact r.Prime := ⟨hr⟩
  let T := zpowers t
  let : MulDistribMulAction T A := MulDistribMulAction.compHom A (ρ.comp T.subtype)
  let Y : SubMulAction T A :=
    { carrier := {a | a ≠ 1}
      smul_mem' := by
        intro g a ha he
        exact ha ((MulAction.injective g) (he.trans (smul_one g).symm)) }
  have hc : Nat.card Y = Nat.card A - 1 := by
    let := Fintype.ofFinite A
    change Nat.card {a : A // a ≠ 1} = _
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp only [Fintype.card_unique,Nat.card_eq_fintype_card]
  have hT : IsPGroup r T := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht,pow_one])
  obtain ⟨a,ha⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card Y (by rwa [hc])
  have hfix : Representation.invariants (ρlin.comp T.subtype) ≠ ⊥ := by
    intro hz
    have hm : Additive.ofMul (a : A) ∈ Representation.invariants (ρlin.comp T.subtype) := by
      intro z
      rw [MonoidHom.comp_apply,heq]
      exact congrArg (fun x : Y => Additive.ofMul (x : A))
        (MulAction.mem_fixedPoints.mp ha z)
    rw [hz,Submodule.mem_bot] at hm
    exact a.property (congrArg Additive.toMul hm)
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρlin T hfix (mem_zpowers t)
  ext a
  have he := congrArg (fun f : Module.End (ZMod 2) (Additive A) => f (Additive.ofMul a)) hk
  rw [heq] at he
  exact congrArg Additive.toMul he

private theorem octagon_prime_cartan_centralizes_unitary_roots
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^n))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    {r : ℕ} (hr : r.Prime) (ho : orderOf t = r)
    (hsep : ¬ r ∣ 2^(2*n)-1) (w : Weyl Q) :
    t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
  let := split.abelian
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  obtain ⟨hirr,_⟩ := unitary_rootAt_cartan_frattini_irreducible Q split J₀ hn hcard hf rfl
    j (μj.trans e) hKj w
  let τ := rootAtCartanFrattiniRepresentation Q split j w
  let : τ.IsIrreducible := hirr
  have hz : rootAtCartanFrattiniAction Q split j w ⟨t,ht⟩ = 1 := by
    apply prime_actor_trivial_of_irreducible
      (rootAtCartanFrattiniAction Q split j w) τ (by intros; rfl) hr
      (by rw [← Subgroup.orderOf_coe]; exact ho)
    rwa [unitary_rootAt_frattini_card Q split J₀ hn hcard hf rfl j (μj.trans e) hKj w]
  have hk : (⟨t,ht⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ∈ τ.ker := by
    change τ ⟨t,ht⟩ = 1
    ext a
    change Additive.ofMul (rootAtCartanFrattiniAction Q split j w ⟨t,ht⟩ a.toMul) = a
    rw [hz]
    rfl
  rw [HexagonStructure.rootAtCartanFrattiniRepresentation_kernel] at hk
  intro a ha
  have he := congrArg (fun f : MulAut (rootAt Q split j w) => (f ⟨a,ha⟩ : X ⧸ Q.D)) hk
  change t*a*t⁻¹=a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A prime-order element of the large linear Cartan centralizes every
conjugate of the opposite unitary root. -/
theorem octagon_separating_prime_unitary_fixed
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F]
    (_hm : rotationOrder Q = 8)
    (i j : Fin 2) (_hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (J : HermitianForm 3 F)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {b a : ℕ} (hb : 2 ≤ b) (hE : Nat.card E = 2^a)
    (hF : Nat.card F = (2^b)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^b))
    (hlarge : 2*b < a)
    (si : RootReflection Q split i) :
    ∃ r : ℕ, ∃ t : X ⧸ Q.D,
      r.Prime ∧ r ∣ 2^a - 1 ∧ ¬ r ∣ 2^(2*b) - 1 ∧
      t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i ∧
      orderOf t = r ∧
      ∀ w, t ∈ centralizer (rootAt Q split j w : Set (X ⧸ Q.D)) := by
  have hpos : 0 < 2*b := by omega
  obtain ⟨r, hr, hri, hrj⟩ := Theory.NumberTheory.exists_binary_separating_prime
    hpos hlarge
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) r
    (by
      rw [rankOne_cartan_card Q split i hKi μi si, hE]
      exact hri)
  let t : X ⧸ Q.D := z
  have ht : orderOf t = r := by
    simpa only [t, Subgroup.orderOf_coe] using hz
  have hfix (w : Weyl Q) :=
    octagon_prime_cartan_centralizes_unitary_roots Q split
      J hb hF hconj j hKj μj z.property.1 hr ht hrj w
  refine ⟨r, t, hr, hri, hrj, ?_, ht, hfix⟩
  exact z.property

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
