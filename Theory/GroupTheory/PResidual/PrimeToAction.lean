module

public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas

/-!
# Coprime splitting from the actual conjugation image

If a homomorphism kills O^{p′}, its image has order prime to p, since
O^{p′} has index prime to p. An abelian subgroup acted on through a coprime
image is the direct product of its commutator and its fixed subgroup.

We apply coprime action to the image in the actual automorphism group,
then identify its fixed and moving subgroups elementwise with the embedded
centralizer and commutator. The original acting group need not have
coprime order. This is the common action argument used in Aschbacher–Smith,
E.6.8, printed pp.247–248, following Definition E.6.4.
-/

public section

open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Killing the prime-to-p residual forces the actual homomorphism image
to have order prime to p. -/
theorem coprime_card_range_of_primeToResidual_le_ker {H : Type*} [Group H] (p : ℕ) [Fact p.Prime]
    (f : G →* H) (hf : primeToResidual p G ≤ f.ker) :
    Nat.Coprime p (Nat.card f.range) := by
  rw [← index_ker]
  exact (primeToResidual_index_coprime p).coprime_dvd_right (index_dvd_of_le hf)

/-- Coprimality of the induced conjugation image suffices for the direct
decomposition of an abelian subgroup, even when the actor has even order. -/
theorem commutator_centralizer_decomposition_of_coprime_image (V B : Subgroup G) [IsMulCommutative V]
    (hB : B ≤ normalizer (V : Set G))
    (hc : Nat.Coprime
      (Nat.card (V.normalizerMonoidHom.comp (inclusion hB)).range) (Nat.card V)) :
    ⁅V, B⁆ ⊔ (V ⊓ centralizer (B : Set G)) = V ∧
      ⁅V, B⁆ ⊓ (V ⊓ centralizer (B : Set G)) = ⊥ := by
  let f := V.normalizerMonoidHom.comp (inclusion hB)
  have hfixed : (fixedPointSubgroup f.range V).map V.subtype =
      V ⊓ centralizer (B : Set G) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.property, ?_⟩
      intro b hb
      have he := congrArg Subtype.val (hv (f.rangeRestrict ⟨b, hb⟩))
      change b * (v : G) * b⁻¹ = v at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · rintro ⟨hv, hc⟩
      refine ⟨⟨x, hv⟩, ?_, rfl⟩
      rintro ⟨a, b, rfl⟩
      apply Subtype.ext
      change (b : G) * x * (b : G)⁻¹ = x
      rw [hc b b.property, mul_inv_cancel_right]
  have hmoving : (commutatorAction f.range V).map V.subtype = ⁅V, B⁆ := by
    apply le_antisymm
    · rw [map_le_iff_le_comap, commutatorAction_eq_closure, closure_le]
      rintro _ ⟨⟨a, b, rfl⟩, v, rfl⟩
      change (v : G)⁻¹ * ((b : G) * (v : G) * (b : G)⁻¹) ∈ ⁅V, B⁆
      simpa only [commutatorElement_def, inv_inv, mul_assoc] using
        commutator_mem_commutator (V.inv_mem v.property) b.property
    · apply commutator_le.mpr
      intro v hv b hb
      refine ⟨(⟨v, hv⟩ : V) * (f ⟨b, hb⟩ (⟨v, hv⟩ : V)⁻¹), ?_, ?_⟩
      · rw [commutatorAction_eq_closure]
        exact subset_closure ⟨f.rangeRestrict ⟨b, hb⟩, (⟨v, hv⟩ : V)⁻¹, by rw [inv_inv]; rfl⟩
      · change v * (b * v⁻¹ * b⁻¹) = v * b * v⁻¹ * b⁻¹
        simp only [mul_assoc]
  have hd := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := f.range) (Group.isSolvable_of_comm (fun a b => mul_comm a b)) hc inferInstance
  constructor
  · have he := congrArg (Subgroup.map V.subtype) hd.sup_eq_top
    simpa only [Subgroup.map_sup, hfixed, hmoving, ← MonoidHom.range_eq_map, range_subtype, sup_comm] using he
  · rw [← hmoving, ← hfixed, ← map_inf _ _ _ V.subtype_injective,
      inf_comm, hd.inf_eq_bot, Subgroup.map_bot]

end Subgroup
