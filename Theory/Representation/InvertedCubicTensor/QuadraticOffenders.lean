module
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.NormalThree
public import Theory.Representation.PerfectInvolutionExtension
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# Quadratic offenders on a cubic multiplicity space

A fixed-free normal cubic and an inverter identify the binary module with two
copies of the inverter-fixed space. For commuting actors, fixed codimension
is therefore doubled. A faithful perfect component makes the ambient dimension
greater than four; halving a quadratic bound gives a genuine FF offender.
These are the multiplicity-space steps used in the external case of
Aschbacher--Smith, *The Classification of Quasithin Groups*, 13.8.20.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace InvertedCubicTensor
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Elementary actors centralizing the normal cubic also centralize every
component-centralizing actor under the common-centralizer bound. -/
theorem elementary_centralizes_component_centralizer
    (K X A : Subgroup D) [K.Normal] [X.Normal]
    (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hA : IsElementaryAbelian 2 A) (hAX : A ≤ centralizer (X : Set D)) :
    A ≤ centralizer (centralizer (K : Set D) : Set D) := by
  let : IsCyclic X := isCyclic_of_prime_card hx
  let : IsElementaryAbelian 2 A := hA
  intro a ha b hb
  let c := a * b * a⁻¹ * b⁻¹
  have hcK : c ∈ centralizer (K : Set D) :=
    (centralizer (K : Set D)).mul_mem
      ((inferInstance : (centralizer (K : Set D)).Normal).conj_mem b hb a)
      ((centralizer (K : Set D)).inv_mem hb)
  have hcX : c ∈ X := hc ⟨hcK,
    commutator_le_centralizer_of_isCyclic_normal X (commutator_mem_commutator (mem_top a) (mem_top b))⟩
  have hac : a * c = c * a := (hAX ha c hcX).symm
  have ha2 : a * a = 1 := by
    simpa only [pow_two] using (show a ^ 2 = 1 from elemPow_eq_one_of_isElementaryAbelian a ha)
  have hconj : a * c * a⁻¹ = c⁻¹ := by
    dsimp [c]
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    simp only [mul_inv_rev, inv_inv]
    rw [hai]
    simp only [←mul_assoc, ha2, one_mul]
  have hci : c = c⁻¹ := by
    calc c = a * c * a⁻¹ := by rw [hac, mul_inv_cancel_right]
         _ = c⁻¹ := hconj
  have hc2 : c^2 = 1 := by rw [pow_two]; exact (congrArg (fun x => x*c) hci).trans (inv_mul_cancel c)
  have hc3 : c^3 = 1 := congrArg Subtype.val
    (show (⟨c,hcX⟩ : X)^3 = 1 by rw [←hx]; exact pow_card_eq_one')
  have hc1 : c = 1 := by simpa only [pow_succ,hc2,one_mul] using hc3
  have he := congrArg (fun z : D => z*b*a) hc1
  change b*a=a*b
  simpa only [c,mul_assoc,inv_mul_cancel,mul_one,one_mul] using he.symm

variable (σ : Representation (ZMod 2) S₃ V) (κ : Representation (ZMod 2) D V)
  (hc : ∀ g h v, κ g (σ h v) = σ h (κ g v))
  (hfree : ∀ v, σ cubic v = v → v = 0)

include hc hfree

/-- A nontrivial faithful perfect component forces at least three multiplicity
coordinates, hence more than four dimensions in the cubic tensor. -/
theorem four_lt_finrank_of_perfect [Group.IsPerfect D] [Nontrivial D]
    (hf : Function.Injective κ) : 4 < Module.finrank (ZMod 2) V := by
  have hi := multiplicity_injective σ κ hc hfree hf
  have hd := (pairEquiv σ hfree).finrank_eq
  rw [Module.finrank_prod] at hd
  change Module.finrank (ZMod 2) (multiplicitySpace σ) +
    Module.finrank (ZMod 2) (multiplicitySpace σ) = Module.finrank (ZMod 2) V at hd
  by_contra! hh
  have hm : Module.finrank (ZMod 2) (multiplicitySpace σ) ≤ 2 := by omega
  obtain ⟨g,hg⟩ := exists_ne (1 : D)
  apply hg
  apply hi
  apply LinearMap.ext
  intro v
  simpa only [map_one,Module.End.one_apply] using
    Representation.PerfectInvolutionExtension.small_action_trivial (multiplicity σ κ hc) hm g v

/-- Fixed codimension is doubled by the actual cubic pair coordinates. -/
theorem fixedCodim_multiplicity (A : Subgroup D) :
    2 * fixedCodim (multiplicity σ κ hc) A = fixedCodim κ A := by
  have he := fixedCodim_map_equivariant
    ((multiplicity σ κ hc).prod (multiplicity σ κ hc)) κ (MonoidHom.id D)
    (pairEquiv σ hfree) (fun g v => pairEquiv_equivariant σ κ hc hfree g v) A
  rw [Subgroup.map_id,fixedCodim_prod] at he
  omega

/-- Halving the source quadratic bound produces an actual FF offender. -/
theorem offender_multiplicity (A : Subgroup D)
    (hA : IsElementaryTwo A) (hb : fixedCodim κ A ≤ 2 * rank A) :
    IsOffender (multiplicity σ κ hc) A := by
  refine ⟨hA,?_⟩
  have hd := fixedCodim_multiplicity σ κ hc hfree A
  omega
end InvertedCubicTensor
