module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions

/-!
# Coordinates for Janko's second centralizer

The parity-twisted binary permutation module has the basis
`1111, 1000, 0011, 0110`. Together with the indicated permutations in S4,
this gives exactly the four matrices in Janko's Case II. We check the
sixteen conjugation identities in the concrete semidirect product.
Conjugation here is `s⁻¹ * x * s`, as in the source.

An actual equivalence from this product to an involution centralizer
therefore supplies marked Case II coordinates. The marking follows from
the center having order two; it is not an additional hypothesis on that
equivalence. The same argument shows that the given equivalence to the
Steiner M22 centralizer preserves the distinguished involution.

The comparison of the twisted product with the concrete M22 centralizer
is a separate obligation. This module does not assert that comparison,
ambient fusion, or ambient order recognition.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 2, p.3,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u

namespace CaseII

-- Componentwise equality avoids the dependent recursor in the derived instance.
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm

local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

/-- The source basis elements `z₁,z₂,z₃,z₄`, indexed here by `0,1,2,3`. -/
@[expose] public def z : Fin 4 → TwistedModel := fun i => SemidirectProduct.inl
  (![Multiplicative.ofAdd ![1, 1, 1, 1], Multiplicative.ofAdd ![1, 0, 0, 0],
     Multiplicative.ofAdd ![0, 0, 1, 1], Multiplicative.ofAdd ![0, 1, 1, 0]] i)

/-- The source actor `a = (01)(23)`. -/
@[expose] public def a : TwistedModel :=
  SemidirectProduct.inr (Equiv.swap 0 1 * Equiv.swap 2 3)

/-- The source actor `b = (03)(12)`. -/
@[expose] public def b : TwistedModel :=
  SemidirectProduct.inr (Equiv.swap 0 3 * Equiv.swap 1 2)

/-- The source actor `c = (123)`. -/
@[expose] public def c : TwistedModel :=
  SemidirectProduct.inr (Equiv.swap 1 2 * Equiv.swap 2 3)

/-- The source actor `d = (23)`. -/
@[expose] public def d : TwistedModel := SemidirectProduct.inr (Equiv.swap 2 3)

/-- The first Case II matrix, with rows giving the images of the basis. -/
public theorem conjugation_a :
    ∀ i, a⁻¹ * z i * a = ![z 0, z 0 * z 1 * z 2, z 2, z 0 * z 3] i := by
  decide +kernel

/-- The second Case II matrix. -/
public theorem conjugation_b :
    ∀ i, b⁻¹ * z i * b = ![z 0, z 0 * z 1 * z 3, z 0 * z 2, z 3] i := by
  decide +kernel

/-- The third Case II matrix, in the source's right-conjugation convention. -/
public theorem conjugation_c :
    ∀ i, c⁻¹ * z i * c = ![z 0, z 1, z 3, z 2 * z 3] i := by
  decide +kernel

/-- The fourth Case II matrix. -/
public theorem conjugation_d :
    ∀ i, d⁻¹ * z i * d = ![z 0, z 0 * z 1, z 2, z 2 * z 3] i := by
  decide +kernel

/-- Each basis element is an involution. -/
public theorem z_order : ∀ i, orderOf (z i) = 2 := by
  intro i
  apply orderOf_eq_prime
  · have h : ∀ i, z i ^ 2 = 1 := by decide +kernel
    exact h i
  · have h : ∀ i, z i ≠ 1 := by decide +kernel
    exact h i

/-- The first basis element is central in the whole semidirect product. -/
public theorem z_zero_mem_center : z 0 ∈ center TwistedModel := by
  decide +kernel

/-- The actor conjugation relations on p.2, with the exact Case II coordinates. -/
public theorem actor_relations :
    c⁻¹ * a * c = b ∧ c⁻¹ * b * c = a * b ∧
    d⁻¹ * a * d = a ∧ d⁻¹ * b * d = a * b ∧ d⁻¹ * c * d = c⁻¹ := by
  decide +kernel

/-- The four source actors have orders `2,2,3,2`. -/
public theorem actor_orders :
    orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 3 ∧ orderOf d = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply orderOf_eq_prime <;> decide +kernel

/-- Every binary vector has source-basis coordinates. -/
public theorem binary_expansion : ∀ v : BinaryFour, ∃ r : Fin 4 → Fin 2,
    (SemidirectProduct.inl v : TwistedModel) =
      z 0 ^ (r 0).val * z 1 ^ (r 1).val * z 2 ^ (r 2).val * z 3 ^ (r 3).val := by
  decide +kernel

/-- Every actor is a word in the indicated Klein four-group, three-cycle
and involution. Together with `binary_expansion`, this exhausts the product. -/
public theorem actor_expansion : ∀ s : SymmetricFour,
    ∃ i j : Fin 2, ∃ k : Fin 3, ∃ l : Fin 2,
      (SemidirectProduct.inr s : TwistedModel) = a ^ i.val * b ^ j.val * c ^ k.val * d ^ l.val := by
  decide +kernel

end CaseII

variable {G : Type u} [Group G]

/-- A nonidentity central element is the specified involution, since the
centralizer's intrinsic center has order two. -/
public theorem central_element_eq_involution [Finite G] (D : LocalData G)
    (x : D.centralizer) (hx : x ∈ center D.centralizer) (hne : x ≠ 1) :
    x = D.centralInvolution := by
  let xZ : center D.centralizer := ⟨x, hx⟩
  let zZ : center D.centralizer := ⟨D.centralInvolution, D.centralInvolution_mem_center⟩
  have hxZ : xZ ≠ 1 := fun h => hne (congrArg Subtype.val h)
  have hzZ : zZ ≠ 1 := by
    intro h
    exact D.z_ne_one
      (congrArg (fun t : center D.centralizer => ((t : D.centralizer) : G)) h)
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center D.centralizer)).mp D.center_card
  exact congrArg Subtype.val ((hw xZ hxZ).trans (hw zZ hzZ).symm)

/-- Marking a Case II equivalence requires no extra compatibility assumption. -/
public theorem caseIIEquiv_involution [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : k (CaseII.z 0) = D.centralInvolution := by
  apply central_element_eq_involution D
  · exact ((centerCongr k) ⟨CaseII.z 0, CaseII.z_zero_mem_center⟩).property
  · intro h
    have h' : CaseII.z 0 = 1 := k.injective (h.trans k.map_one.symm)
    simpa [h'] using CaseII.z_order 0

/-- The selected Mathieu involution as an element of its own centralizer. -/
@[expose] public def modelCentralInvolution : CentralizerModels.m22Centralizer :=
  ⟨CentralizerModels.m22Involution, mem_centralizer_singleton_iff.mpr rfl⟩

/-- Any supplied local-model equivalence preserves the distinguished involution. -/
public theorem centralizerEquiv_involution [Finite G] (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.m22Centralizer) :
    e D.centralInvolution = modelCentralInvolution := by
  have hc : modelCentralInvolution ∈ center CentralizerModels.m22Centralizer := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have he := central_element_eq_involution D (e.symm modelCentralInvolution)
    (((centerCongr e.symm) ⟨modelCentralInvolution, hc⟩).property)
  have hn : e.symm modelCentralInvolution ≠ 1 := by
    intro h
    have ho : orderOf (e.symm modelCentralInvolution) = 2 := by
      rw [e.symm.orderOf_eq]
      simpa only [modelCentralInvolution, Subgroup.orderOf_mk] using
        CentralizerModels.m22Involution_order
    rw [h, orderOf_one] at ho
    contradiction
  exact (congrArg e (he hn)).symm.trans (e.apply_symm_apply _)

namespace CaseII

/-- The coordinate inclusion into the actual ambient group. -/
@[expose] public def into (D : LocalData G) (k : TwistedModel ≃* D.centralizer) :
    TwistedModel →* G := D.centralizer.subtype.comp k.toMonoidHom

/-- The ambient coordinate map is faithful. -/
public theorem into_injective (D : LocalData G) (k : TwistedModel ≃* D.centralizer) :
    Function.Injective (into D k) := Subtype.val_injective.comp k.injective

/-- The first source coordinate is the original, unaltered ambient involution. -/
public theorem into_z_zero [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) : into D k (z 0) = D.z :=
  congrArg Subtype.val (caseIIEquiv_involution D k)

/-- Janko's `E` is the image of the actual binary normal factor. -/
@[expose] public def E (D : LocalData G) (k : TwistedModel ≃* D.centralizer) : Subgroup G :=
  ((into D k).comp (SemidirectProduct.inl : BinaryFour →* TwistedModel)).range

/-- Janko's second elementary subgroup, with its actual ambient generators. -/
@[expose] public def F (D : LocalData G) (k : TwistedModel ≃* D.centralizer) : Subgroup G :=
  closure {into D k (z 0), into D k (z 2), into D k a, into D k d}

/-- The source subgroup `Q = ⟨c⟩`. -/
@[expose] public def Q (D : LocalData G) (k : TwistedModel ≃* D.centralizer) : Subgroup G :=
  zpowers (into D k c)

end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification
