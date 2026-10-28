module
public import Stellmacher.Recognition.OddCoreClosure
public import Glauberman.Signalizer.TwoCompletion

/-!
# Completing the actual involution odd-core closure

In a finite N2 group, let A be an actual elementary abelian two-subgroup of
order at least eight. The existing subgroup `involutionOddCoreClosure A`
has odd order, is solvable and normalized by A, and its intersection with
each nonidentity element centralizer is exactly that centralizer's ambient
odd core. No simplicity or extra Z hypothesis is used.

The private signalizer family assigns the existing ambient odd core to each
nonidentity actor. Its action is actual conjugation through the inclusion
A into G; the action and its inherited structures are selected from that
same homomorphism throughout. Core order and N2 involution-centralizer
solvability provide the value hypotheses. Commutation inside A and normality
of each core give invariance, while the proved ambient odd-core balance
theorem gives the balance condition. The family supremum is the exact
preexisting closure by reindexing nonidentity actors. The unconditional
binary signalizer theorem then supplies completeness, and conjugation fixed
points identify its fixed-value equalities with actual centralizers.

This is the odd-core application of Kurzweil–Stellmacher, *The Theory of
Finite Groups*, Theorem 11.2.9, printed p.325, to the N2 balance theorem.
It completes the closure used in GLS2 Section 21.8 and the later global
odd-core recognition argument, without asserting any further connectivity
or fusion conclusion.
-/

namespace Stellmacher.Recognition
open Theory.GroupTheory
open scoped IsMulCommutative

private abbrev actualConjugationAction {G : Type*} [Group G] (A : Subgroup G) :
    MulDistribMulAction A G := MulDistribMulAction.compHom G (MulAut.conj.comp A.subtype)

local instance conjugationDistribAction {G : Type*} [Group G] (A : Subgroup G) :
    MulDistribMulAction A G := actualConjugationAction A

local instance conjugationMulAction {G : Type*} [Group G] (A : Subgroup G) :
    MulAction A G := (actualConjugationAction A).toMulAction

local instance conjugationSMul {G : Type*} [Group G] (A : Subgroup G) :
    SMul A G := (actualConjugationAction A).toSMul

private theorem involution_order {G : Type*} [Group G] (A : Subgroup G)
    [IsElementaryAbelian 2 A] (a : {a : A // a ≠ 1}) : orderOf (a.val : G) = 2 := by
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime_iff.mpr ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) a.val, a.property⟩

private theorem oddCore_odd {G : Type*} [Group G] [Finite G] (a : G) :
    Odd (Nat.card (involutionOddCore a)) := by
  apply Nat.coprime_two_left.mp
  change Nat.Coprime 2 (Nat.card ((pPrimeCore 2 (Subgroup.centralizer ({a} : Set G))).map _))
  rw [Subgroup.card_map_of_injective Subtype.coe_injective]
  exact pPrimeCore_coprime_card

private theorem oddCore_solvable {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (a : G) (ha : orderOf a = 2) :
    Group.IsSolvable (involutionOddCore a) := by
  let C := Subgroup.centralizer ({a} : Set G)
  have hC : Group.IsSolvable C := by
    by_contra hn
    obtain ⟨U, hU, hnot⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer ha hn
    exact hnot (hN U hU)
  let _ := hC
  let f : involutionOddCore a →* C :=
    (involutionOddCore a).subtype.codRestrict C (fun x =>
      Subgroup.map_subtype_le (pPrimeCore 2 C) x.property)
  apply Group.isSolvable_of_isSolvable_injective (f := f)
  intro x y h
  have hxy : (x : G) = (y : G) := congrArg (fun z : C => (z : G)) h
  exact Subtype.ext hxy

private def oddCoreFamily {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (A : Subgroup G) [IsElementaryAbelian 2 A] :
    TwoSignalizerFamily A G := by
  refine {
  subgroup a := involutionOddCore (a.val : G)
  odd a := oddCore_odd _
  solvable a := oddCore_solvable hN _ (involution_order A a)
  invariant a := by
    constructor
    intro b x
    have hb : (b : G) ∈ Subgroup.centralizer ({(a.val : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mul_comm b a.val))
    have hn := centralizer_le_normalizer_involutionOddCore _ hb
    exact Subgroup.mem_normalizer_iff.mp hn x
  le_fixed a := by
    intro x hx z
    have hxC := Subgroup.map_subtype_le
      (pPrimeCore 2 (Subgroup.centralizer ({(a.val : G)} : Set G))) hx
    have hxcomm := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hfixed : a.val • x = x := by
      change (a.val : G) * x * (a.val : G)⁻¹ = x
      rw [← hxcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact smul_eq_self_of_mem_zpowers z.property hfixed
  balance a b := by
    intro x hx
    have hbfix := hx.2 ⟨b.val, Subgroup.mem_zpowers b.val⟩
    have hbfix' : (b.val : G) * x * (b.val : G)⁻¹ = x := hbfix
    have hxC : x ∈ Subgroup.centralizer ({(b.val : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hbfix').symm
    exact involution_oddCore_balance hN (involution_order A a) (involution_order A b)
      (congrArg Subtype.val (mul_comm a.val b.val)) ⟨hx.1, hxC⟩ }

private theorem oddCoreFamily_closure {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (A : Subgroup G) [IsElementaryAbelian 2 A] :
    (oddCoreFamily hN A).closure = involutionOddCoreClosure A := by
  simp only [TwoSignalizerFamily.closure, oddCoreFamily, involutionOddCoreClosure, iSup_subtype]

private theorem conjugation_fixed_eq_centralizer {G : Type*} [Group G]
    (A : Subgroup G) (a : A) :
    FixedPoints.subgroup (Subgroup.zpowers a) G = Subgroup.centralizer ({(a : G)} : Set G) := by
  ext x
  constructor
  · intro hx
    have hf : (a : G) * x * (a : G)⁻¹ = x := hx ⟨a, Subgroup.mem_zpowers a⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf).symm
  · intro hx z
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hx
    apply smul_eq_self_of_mem_zpowers z.property
    change (a : G) * x * (a : G)⁻¹ = x
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

private theorem ambient_complete_of_family_complete {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hc : (oddCoreFamily hN A).IsComplete) :
    Odd (Nat.card (involutionOddCoreClosure A)) ∧
      Group.IsSolvable (involutionOddCoreClosure A) ∧
      A ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
      ∀ a : A, a ≠ 1 → involutionOddCoreClosure A ⊓
        Subgroup.centralizer ({(a : G)} : Set G) = involutionOddCore (a : G) := by
  have heq := oddCoreFamily_closure hN A
  refine ⟨heq ▸ hc.1, heq ▸ hc.2.1, ?_, ?_⟩
  · exact A.le_normalizer.trans (normalizer_le_normalizer_involutionOddCoreClosure A)
  · intro a ha
    have h := hc.fixed_eq ⟨a, ha⟩
    rwa [heq, conjugation_fixed_eq_centralizer] at h

/-- The actual involution odd-core closure in an N2 group is odd and solvable,
normalized by A, and recovers each local odd core by centralizer intersection. -/
public theorem involutionOddCoreClosure_complete {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) :
    Odd (Nat.card (involutionOddCoreClosure A)) ∧
      Group.IsSolvable (involutionOddCoreClosure A) ∧
      A ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
      ∀ a : A, a ≠ 1 → involutionOddCoreClosure A ⊓
        Subgroup.centralizer ({(a : G)} : Set G) = involutionOddCore (a : G) := by
  exact ambient_complete_of_family_complete hN A
    (Glauberman.solvable_two_signalizer_complete (oddCoreFamily hN A) hA)

end Stellmacher.Recognition
