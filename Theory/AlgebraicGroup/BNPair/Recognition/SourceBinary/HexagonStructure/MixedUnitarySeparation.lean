module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryWeights
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.CentralizerSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiConstituentKernels
public import Theory.Representation.NormalInvariants
public import Theory.NumberTheory.BinaryPrimitiveDivisor.Separation

/-!
# Separating primes in a mixed linear–unitary hexagon

If the binary exponent a of the linear field exceeds twice the unitary
exponent n, a prime dividing 2^a - 1 but not 2^(2n) - 1 supplies a
nontrivial Cartan element centralizing every unitary root. The simple
reflections normalize its cyclic group, and its fixed points on every
linear root vanish. The resulting centralizer section has Frattini order
at most 2^(4n), contradicting the unitary lower bound 2^(6n).

This closes the strict parameter branch of Fong–Seitz I (6D), printed
p.43. The equality case a = 2n requires a separate argument.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
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

/-- A separating prime in the Cartan fixes each whole unitary root. -/
theorem prime_cartan_centralizes_unitary_roots
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
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
  rw [rootAtCartanFrattiniRepresentation_kernel] at hk
  intro a ha
  have he := congrArg (fun f : MulAut (rootAt Q split j w) => (f ⟨a,ha⟩ : X ⧸ Q.D)) hk
  change t*a*t⁻¹=a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

include split in
private theorem cyclic_normalized_of_simple_lifts
    (i j : Fin 2) (hij : i ≠ j) (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple i)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple j)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    (hat : (a : X ⧸ Q.D)*t*(a : X ⧸ Q.D)⁻¹ = t⁻¹)
    (hbt : Commute (b : X ⧸ Q.D) t) :
    Q.tits.N ≤ normalizer (zpowers t : Set (X ⧸ Q.D)) := by
  classical
  let := split.abelian
  let A := normalizer (zpowers t : Set (X ⧸ Q.D))
  have hH : Q.tits.B ⊓ Q.tits.N ≤ A :=
    ((Subgroup.le_centralizer (Q.tits.B ⊓ Q.tits.N)).trans
      (centralizer_le (zpowers_le.mpr ht))).trans (_root_.centralizer_le_normalizer (zpowers t))
  have haA : (a : X ⧸ Q.D) ∈ A := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((a : X ⧸ Q.D)*t*(a : X ⧸ Q.D)⁻¹) = zpowers t
    rw [hat,zpowers_inv]
  have hbA : (b : X ⧸ Q.D) ∈ A := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((b : X ⧸ Q.D)*t*(b : X ⧸ Q.D)⁻¹) = zpowers t
    rw [hbt.eq,mul_inv_cancel_right]
  let s (k : Fin 2) := if k = i then a else b
  have hs (k : Fin 2) : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (s k) = Q.simple k := by
    by_cases hk : k = i
    · simpa [s,hk] using ha
    · have hkj : k = j := by omega
      simpa [s,hkj,hij.symm] using hb
  have hsA (k : Fin 2) : (s k : X ⧸ Q.D) ∈ A := by
    dsimp only [s]
    split_ifs <;> assumption
  intro g hg
  let q := QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
  let gN : Q.tits.N := ⟨g,hg⟩
  obtain ⟨k,hk,hqk⟩ := UnitarySource.exists_weyl_lift_in Q s hs A hsA (q gN)
  have hdiff : gN*k⁻¹ ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (gN*k⁻¹) = 1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have hz := A.mul_mem (hH hdiff) hk
  change (g*(k : X ⧸ Q.D)⁻¹)*(k : X ⧸ Q.D) ∈ A at hz
  simpa only [inv_mul_cancel_right] using hz

private theorem linear_cyclic_fixedFree_conjugates
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E)) (si : RootReflection Q split i)
    {t : X ⧸ Q.D} (htH : t ∈ Q.tits.B ⊓ Q.tits.N)
    (htR : t ∈ rankOne Q split i) (htne : t ≠ 1)
    (hTN : Q.tits.N ≤ normalizer (zpowers t : Set (X ⧸ Q.D))) (w : Weyl Q) :
    rootAt Q split i w ⊓ centralizer (zpowers t : Set (X ⧸ Q.D)) = ⊥ := by
  have hf : simpleRoot Q split i ⊓ centralizer (zpowers t : Set (X ⧸ Q.D)) = ⊥ := by
    apply bot_unique
    apply le_trans (inf_le_inf_left _ (centralizer_le ?_))
      (le_of_eq (rankOne_cartan_root_fixedFree Q split i hKi μi si htH htR htne))
    exact Set.singleton_subset_iff.mpr (mem_zpowers t)
  let n := representative w
  have hh := congrArg (fun A => rightConjugate A (n : X ⧸ Q.D)) hf
  rw [rightConjugate_inf,rightConjugate_eq_self _
    (normalizer_le_normalizer_centralizer (zpowers t) (hTN n.property))] at hh
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) = ⊥ := by
    ext x
    change (n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹ = 1 ↔ x = 1
    exact (MulAut.conj (n : X ⧸ Q.D)).map_eq_one_iff
  exact hh.trans hb

/-- The linear exponent cannot exceed twice the unitary exponent. -/
theorem mixed_unitary_no_larger_linear_field
    {E F : Type*} [Field E] [Finite E] [CharP E 2] [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    {a : ℕ} (hE : Nat.card E = 2^a) (ha : 2*n < a) : False := by
  obtain ⟨r,hr,hrE,hrF⟩ := Theory.NumberTheory.exists_binary_separating_prime
    (by omega : 0 < 2*n) ha
  let : Fact r.Prime := ⟨hr⟩
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split i)) r
    (by rwa [rankOne_cartan_card Q split i hKi μi si,hE])
  let t : X ⧸ Q.D := z
  have ht : orderOf t = r := by
    simpa only [t,Subgroup.orderOf_coe] using hz
  have htne : t ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ht
    exact hr.ne_one ht.symm
  have hfix (w : Weyl Q) := prime_cartan_centralizes_unitary_roots Q split J hn hcard hconj
    j hKj μj z.property.1 hr ht hrF w
  have hR : rankOne Q split j ≤ centralizer ({t} : Set (X ⧸ Q.D)) := by
    apply sup_le
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr (by
        have hc := hfix 1
        rw [rootAt_one] at hc
        exact mem_centralizer_iff.mp hc u hu)
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hfix (Q.simple j)) u hu)
  have hsj : Commute (sj.val : X ⧸ Q.D) t :=
    mem_centralizer_singleton_iff.mp (hR sj.mem_rankOne)
  have hsi : (si.val : X ⧸ Q.D)*t*(si.val : X ⧸ Q.D)⁻¹ = t⁻¹ := by
    obtain ⟨u,hu⟩ := exists_alignedTorus_of_mem Q split i hKi μi si z.property.1 z.property.2
    change alignedTorus Q split i hKi μi si u = t at hu
    rw [←hu,reflection_alignedTorus]
    exact (alignedTorusHom Q split i hKi μi si).map_inv u
  let T := zpowers t
  have hTN : Q.tits.N ≤ normalizer (T : Set (X ⧸ Q.D)) :=
    cyclic_normalized_of_simple_lifts Q split i j hij si.val sj.val si.class_eq sj.class_eq
      z.property.1 hsi hsj
  have hfree (w : Weyl Q) : rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥ :=
    linear_cyclic_fixedFree_conjugates Q split i hKi μi si z.property.1 z.property.2 htne hTN w
  have hfixT (w : Weyl Q) : rootAt Q split j w ≤ centralizer (T : Set (X ⧸ Q.D)) :=
    le_centralizer_iff.mp (zpowers_le.mpr (hfix w))
  have hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · simpa only [rootAt_one] using hfixT 1
    · exact hfixT (Q.simple j)
  let d := centralizerSection Q split j hKj T hTR
  have hlo := unitary_section_card_bound Q split j J hn hcard hconj σ hσ d
    (centralizerSection_action_ne_one Q split hhex i j hij sj hKj T hTR (hfixT _))
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(6*n) ≤ d.effectiveDenominator.index at hlo
  rw [he] at hlo
  have hup := centralizerSection_frattini_bound Q split hhex i j hij T
    (zpowers_le.mpr z.property.1) hfree hfixT
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨e⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2^n) hcard hf
  have hc := unitary_rootAt_frattini_card Q split J₀ hn hcard hf rfl j (μj.trans e) hKj 1
  rw [rootAt_one] at hc
  rw [hc,←pow_mul] at hup
  have hbound : 2^(6*n) ≤ 2^(4*n) := by
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hlo.trans hup
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hbound
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
