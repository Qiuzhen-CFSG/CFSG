module

public import Theory.Mathieu.M11.Properties.OrderCertificate

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise
open M11OrderCertificate M11OrderRigidity
private theorem m11Generated_le_M11 :
    wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec ≤ M11 := by
  intro g hg
  rcases hg with ⟨w, rfl⟩
  induction w with
  | nil => exact M11.one_mem
  | cons i w ih =>
      apply M11.mul_mem
      · fin_cases i
        · change m11L0G0 ∈ M11
          rw [← m11GeneratorA_eq_m11L0G0]
          exact m11GeneratorA_mem
        · change m11L0G1 ∈ M11
          rw [← m11GeneratorB_eq_m11L0G1]
          exact m11GeneratorB_mem
        · change m11L0G0⁻¹ ∈ M11
          rw [← m11GeneratorA_eq_m11L0G0]
          exact M11.inv_mem m11GeneratorA_mem
        · change m11L0G1⁻¹ ∈ M11
          rw [← m11GeneratorB_eq_m11L0G1]
          exact M11.inv_mem m11GeneratorB_mem
      · exact ih

private def m11GeneratedEmbedding :
    wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec ↪ M11 where
  toFun g := ⟨g, m11Generated_le_M11 g.property⟩
  inj' := by
    intro g h hgh
    apply Subtype.ext
    exact congrArg (fun q : M11 => (q : Equiv.Perm (Fin 11))) hgh

private theorem m11_card_ge : 7920 ≤ Nat.card M11 := by
  rw [← m11Generated_order]
  exact Nat.card_le_card_of_injective
    m11GeneratedEmbedding m11GeneratedEmbedding.injective

/-- The full automorphism group of the Witt design S(4,5,11) has order 7920. -/
public theorem m11_order : Nat.card M11 = 7920 :=
  Nat.le_antisymm m11_card_le m11_card_ge

/-- The ordered tuple of Atlas points 1, 2, 3, and 4 used by the M11
four-point rigidity certificate. -/
public def m11FourPointBase : Fin 4 ↪ Fin 11 where
  toFun i := ⟨i.1 + 1, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    change i.1 + 1 = j.1 + 1 at hval
    omega

/-- The orbit map of the standard ordered four-tuple is bijective.  This is
the bounded public interface to the reflected order certificate and the
four-point rigidity argument above. -/
public theorem m11_fourPointOrbitMap_bijective :
    Function.Bijective (fun g : M11 => g • m11FourPointBase) := by
  have hImage (g : M11) :
      m11FourPointImage g = g • m11FourPointBase := by
    ext i
    fin_cases i <;> rfl
  apply (Nat.bijective_iff_injective_and_card _).2
  constructor
  · intro g h hgh
    apply m11FourPointImage_injective
    rw [hImage g, hImage h]
    exact hgh
  · calc
      Nat.card M11 = 7920 := m11_order
      _ = Fintype.card (Fin 4 ↪ Fin 11) := m11_fourPointImages_card.symm
      _ = Nat.card (Fin 4 ↪ Fin 11) := Nat.card_eq_fintype_card.symm

/-- The natural degree-eleven action of M11 is transitive. -/
public noncomputable instance : MulAction.IsPretransitive M11 (Fin 11) where
  exists_smul_eq := by
    let reps : Fin 11 → Equiv.Perm (Fin 11) := fun y =>
      m11L0Rep (m11L0PointInv y)
    have hMem : ∀ y : Fin 11, reps y ∈ M11 := by
      intro y
      change m11L0Rep (m11L0PointInv y) ∈ M11
      rw [m11L0Rep_eq_word]
      exact m11Generated_le_M11
        (evalWord_mem_wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec
          (m11L0RepWord (m11L0PointInv y)))
    have hOrbit : ∀ y : Fin 11, reps y • (1 : Fin 11) = y := by
      intro y
      change m11L0Rep (m11L0PointInv y) 1 = y
      rw [m11L0RepPoint]
      fin_cases y <;> rfl
    intro x y
    refine ⟨⟨reps y * (reps x)⁻¹,
      M11.mul_mem (hMem y) (M11.inv_mem (hMem x))⟩, ?_⟩
    calc
      (reps y * (reps x)⁻¹) • x =
          (reps y * (reps x)⁻¹) • (reps x • (1 : Fin 11)) := by rw [hOrbit x]
      _ = reps y • (1 : Fin 11) := by simp [mul_smul]
      _ = y := hOrbit y
/-- The first ATLAS standard generator, regarded as an element of M11. -/
@[expose]
public noncomputable def m11GeneratorAInM11 : M11 := ⟨m11GeneratorA, m11GeneratorA_mem⟩

/-- The second ATLAS standard generator, regarded as an element of M11. -/
@[expose]
public noncomputable def m11GeneratorBInM11 : M11 := ⟨m11GeneratorB, m11GeneratorB_mem⟩

private noncomputable def m11GeneratorClosure : Subgroup M11 :=
  Subgroup.closure ({m11GeneratorAInM11, m11GeneratorBInM11} : Set M11)

private noncomputable def m11ClosureGen : Fin 4 → m11GeneratorClosure
  | 0 => ⟨m11GeneratorAInM11, Subgroup.subset_closure (by simp)⟩
  | 1 => ⟨m11GeneratorBInM11, Subgroup.subset_closure (by simp)⟩
  | 2 => ⟨(m11GeneratorAInM11)⁻¹,
      m11GeneratorClosure.inv_mem (Subgroup.subset_closure (by simp))⟩
  | 3 => ⟨(m11GeneratorBInM11)⁻¹,
      m11GeneratorClosure.inv_mem (Subgroup.subset_closure (by simp))⟩
  | _ => ⟨m11GeneratorAInM11, Subgroup.subset_closure (by simp)⟩

private theorem m11ClosureGen_coe (i : Fin 4) :
    (((m11ClosureGen i : m11GeneratorClosure) : M11) : Equiv.Perm (Fin 11)) =
      m11L0Gen i := by
  fin_cases i
  · exact m11GeneratorA_eq_m11L0G0
  · exact m11GeneratorB_eq_m11L0G1
  · exact congrArg Inv.inv m11GeneratorA_eq_m11L0G0
  · exact congrArg Inv.inv m11GeneratorB_eq_m11L0G1

private theorem m11EvalWordClosureGen_coe (w : List (Fin 4)) :
    (((evalWord m11ClosureGen w : m11GeneratorClosure) : M11) :
      Equiv.Perm (Fin 11)) = evalWord m11L0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change (((m11ClosureGen i : m11GeneratorClosure) : M11) :
          Equiv.Perm (Fin 11)) *
          (((evalWord m11ClosureGen w : m11GeneratorClosure) : M11) :
            Equiv.Perm (Fin 11)) =
        m11L0Gen i * evalWord m11L0Gen w
      rw [m11ClosureGen_coe, ih]

private noncomputable def m11GeneratedClosureEmbedding :
    wordSubgroup m11L0Gen m11L0Inv m11L0Inv_spec ↪ m11GeneratorClosure where
  toFun g := evalWord m11ClosureGen (Classical.choose g.property)
  inj' := by
    intro g h hgh
    apply Subtype.ext
    have hval := congrArg (fun x : m11GeneratorClosure =>
      (((x : M11) : Equiv.Perm (Fin 11)))) hgh
    rw [m11EvalWordClosureGen_coe, m11EvalWordClosureGen_coe,
      Classical.choose_spec g.property, Classical.choose_spec h.property] at hval
    exact hval

/-- The two ATLAS standard generators generate the full Witt-design automorphism group M11. -/
public theorem m11_generators_closure_eq_top :
    Subgroup.closure ({m11GeneratorAInM11, m11GeneratorBInM11} : Set M11) = ⊤ := by
  apply Subgroup.eq_top_of_le_card
  rw [m11_order, ← m11Generated_order]
  exact Nat.card_le_card_of_injective m11GeneratedClosureEmbedding
    m11GeneratedClosureEmbedding.injective


public theorem m11_order_factorization :
    Nat.card M11 = 2 ^ 4 * 3 ^ 2 * 5 * 11 := by
  rw [m11_order]
  norm_num

/-- The prime divisors of the order of `M11` are exactly `2`, `3`, `5`, and `11`. -/
public theorem m11_prime_dvd_order_iff (p : ℕ) [Fact (Nat.Prime p)] :
    p ∣ Nat.card M11 ↔ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11 := by
  rw [m11_order, show 7920 = 2 * 2 * 2 * 2 * 3 * 3 * 5 * 11 by norm_num]
  have hp : Nat.Prime p := Fact.out
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 11)]
  aesop

/-- The prime spectrum of `M11`. -/
public theorem m11_prime_spectrum :
    Nat.primeFactors (Nat.card M11) = {2, 3, 5, 11} := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdiv, _⟩
    let : Fact (Nat.Prime p) := ⟨hp⟩
    exact (m11_prime_dvd_order_iff p).mp hdiv
  · intro h
    rw [m11_order]
    rcases h with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide +kernel, by norm_num, by norm_num⟩

end Sporadic.Mathieu
