module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.Defs
public import Theory.GroupTheory.QuaternionCentralProductModelData
public import Theory.GroupTheory.Recognition.UnitaryFourThree.FromQuaternionCore

/-!
# The genuine Asc94 type construction in the first branch of13.5.16

In the M=L case of13.5.15(9), the source quaternion core is O₂(H), and
H is the actual involution centralizer. The alternative S₆ quotient is
incompatible with the A₆-block quotient of L. From the original quaternion
model and the actual S₃ × S₃ quotient, construct both normal SL₂(3) factors
in O²(H), identify its two-core with U_H and obtain the centralizer order.
One returning core intersection of order four then gives the full universal
intersection condition by conjugation in O²(H).

This discharges the implicit invocation of the definition of type U₄(3)
in the first paragraph of13.5.16. The preceding nine-clause source theorem
13.5.15 and construction of its selected y and V₂ intersection remain
separate obligations of the original Chapter13 setup. The S₆ branch's
transfer exclusion is not asserted here.

Source: Aschbacher–Smith,13.5.15–16, printed pp.919–922;
Aschbacher, Sporadic Groups (1994),45.1 and type definition, pp.242,244.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
namespace TypeU4
open Theory.GroupTheory.Recognition
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {M : Subgroup G} {g : G}

omit [Finite G] in
/-- In the original M=L branch, the S₆ option is impossible because the
literal quotient of L is A₆, as supplied by its source block structure. -/
theorem core_eq_closure (b : Conclusions D M 6 g) (hM : M = D.L) :
    D.QH = D.UH := by
  rcases (b.nine rfl).2 with h | h
  · exact h.2
  · obtain ⟨eS⟩ := h.1
    obtain ⟨eA⟩ := (b.four.2 rfl).2.2.quotient_iso
    have hS : Nat.card (M ⧸ pCore 2 M) = 720 := by
      rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_perm, Fintype.card_fin]
      decide
    have hA : Nat.card (D.L ⧸ pCore 2 D.L) = 360 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hM, hA] at hS
    contradiction

/-- A nonidentity element of the actual source line is its involution generator. -/
theorem point_generator (h : D.Hypothesis) (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    orderOf z = 2 ∧ D.V₁ = zpowers z := by
  have hdiv := D.V₁.orderOf_dvd_natCard hz
  rw [h.point_card] at hdiv
  have ho : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with he | he
    · exact (hz1 (orderOf_eq_one_iff.mp he)).elim
    · exact he
  refine ⟨ho, ?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm
  rw [h.point_card, Nat.card_zpowers, ho]

/-- The earlier H=G₁ conclusion identifies the literal centralizer used by Asc94. -/
theorem centralizer_eq (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    UnitaryFourThree.centralizer z = D.H := by
  rw [b.six.1]
  change centralizer ({z} : Set G) = centralizer (D.V₁ : Set G)
  rw [(point_generator h z hz hz1).2, zpowers_eq_closure, centralizer_closure]

/-- Every Asc94 local field, including its original SL₂(3) factors, follows
from the first source branch and its original returning-core intersection. -/
theorem isType (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M = D.L)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (y : G) (hy : y⁻¹ * z * y ∈ D.UH) (hyV₁ : y⁻¹ * z * y ∉ D.V₁)
    (hpair : Nat.card (D.UH ⊓ UnitaryFourThree.conjugate D.UH y : Subgroup G) = 4) :
    UnitaryFourThree.IsType z := by
  have hpoint := point_generator h z hz hz1
  have hC := centralizer_eq h b z hz hz1
  have hQ := core_eq_closure b hM
  let eQ : pCore 2 D.H ≃* D.UH :=
    ((pCore 2 D.H).equivMapOfInjective D.H.subtype D.H.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)
  let d := (QuaternionCentralProduct.dataOfEquiv b.five.2.some).map eQ.symm
  have hdc : Nonempty (QuaternionCentralProductData (pCore 2 (UnitaryFourThree.centralizer z))) := by
    rw [hC]
    exact ⟨d⟩
  obtain ⟨dc⟩ := hdc
  have hc : generalizedFitting (UnitaryFourThree.centralizer z) =
      pCore 2 (UnitaryFourThree.centralizer z) := by rw [hC]; exact h.characteristic_H
  have he : Nonempty (((UnitaryFourThree.centralizer z) ⧸
      pCore 2 (UnitaryFourThree.centralizer z)) ≃* OmegaPlusFour) := by
    rw [hC]
    exact (b.nine rfl).1
  have hcore : (UnitaryFourThree.centralizer z).pCoreIn 2 = D.UH := by
    rw [hC]
    exact hQ
  apply UnitaryFourThree.isType_of_quaternion_core_and_one_intersection
    hpoint.1 dc hc he.some y
  · rwa [hcore]
  · rwa [← hpoint.2]
  · simpa only [hcore] using hpair

/-- The source's returning plane gives the needed fusion witness directly:
its conjugator normalizes V₂ but does not centralize the distinguished point. -/
theorem isType_of_returning_plane (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (hM : M = D.L) (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (V₂ : Subgroup G) (hline : D.V₁ ≤ V₂) (hseed : V₂ ≤ D.Vplus)
    (hfour : Nat.card V₂ = 4) (y : G)
    (hy : y ∈ normalizer (V₂ : Set G)) (hyH : y ∉ D.H)
    (hpair : D.UH ⊓ UnitaryFourThree.conjugate D.UH y = V₂) :
    UnitaryFourThree.IsType z := by
  have hmove : y⁻¹ * z * y ∉ D.V₁ := by
    intro hmem
    have hneq : y⁻¹ * z * y ≠ 1 := by
      intro he
      have hh := congrArg (fun x : G => y * x * y⁻¹) he
      have : z = 1 := by simpa only [mul_assoc, mul_inv_cancel_left,
        inv_mul_cancel_right, mul_one, mul_inv_cancel] using hh
      exact hz1 this
    have heq : y⁻¹ * z * y = z := by
      obtain ⟨w, hw, hwuniq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
      have ha := hwuniq ⟨y⁻¹ * z * y, hmem⟩
        (fun he => hneq (congrArg Subtype.val he))
      have hb := hwuniq ⟨z, hz⟩ (fun he => hz1 (congrArg Subtype.val he))
      exact congrArg Subtype.val (ha.trans hb.symm)
    apply hyH
    rw [← centralizer_eq h b z hz hz1]
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun x : G => y * x) heq
    simpa only [mul_assoc, mul_inv_cancel_left] using hh.symm
  apply isType h b hM z hz hz1 y
  · apply (le_conjugateSpanBy D.Vplus D.H)
    apply hseed
    have hh := mem_normalizer_iff.mp ((normalizer (V₂ : Set G)).inv_mem hy) z
    simpa only [inv_inv] using hh.mp (hline hz)
  · exact hmove
  · rw [hpair, hfour]

end TypeU4
end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
