module

public import Theory.AlgebraicGroup.BNPair.Defs

/-! Representatives of quotient classes in a Tits system. -/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- Multiplying all representatives of a class in `N / (B ∩ N)` by `B` on the
right gives the same set as multiplying any one representative by `B`. -/
public lemma representativeSet_mul_B (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) (n : N)
    (hn : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = w) :
    representativeSet B N w * (B : Set X) =
      ({(n : X)} : Set X) * (B : Set X) := by
  ext x
  constructor
  · rintro ⟨a, ⟨m, hmw, rfl⟩, b, hb, rfl⟩
    have hq : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) m =
        QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n := hmw.trans hn.symm
    rw [QuotientGroup.mk'_eq_mk'] at hq
    obtain ⟨z, hz, hmz⟩ := hq
    have hzB : (z : X) ∈ B := by
      change (z : X) ∈ B ⊓ N at hz
      exact hz.1
    have hmzX : (m : X) * (z : X) = (n : X) :=
      congrArg (fun q : N => (q : X)) hmz
    refine ⟨(n : X), Set.mem_singleton _, (z : X)⁻¹ * b,
      B.mul_mem (B.inv_mem hzB) hb, ?_⟩
    rw [← hmzX]
    simp only [mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact ⟨(n : X), ⟨n, hn, rfl⟩, b, hb, rfl⟩

/-- Multiplying `B` by all representatives of a class in `N / (B ∩ N)` gives
the same set as multiplying `B` by any one representative. -/
public lemma B_mul_representativeSet (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) (n : N)
    (hn : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = w) :
    (B : Set X) * representativeSet B N w =
      (B : Set X) * ({(n : X)} : Set X) := by
  ext x
  constructor
  · rintro ⟨b, hb, a, ⟨m, hmw, rfl⟩, rfl⟩
    have hq : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n =
        QuotientGroup.mk' ((B ⊓ N).subgroupOf N) m := hn.trans hmw.symm
    rw [QuotientGroup.mk'_eq_mk'] at hq
    obtain ⟨z, hz, hnz⟩ := hq
    have hzConj := (inferInstance : ((B ⊓ N).subgroupOf N).Normal).conj_mem z hz n
    have hzConjB : ((n * z * n⁻¹ : N) : X) ∈ B := by
      change ((n * z * n⁻¹ : N) : X) ∈ B ⊓ N at hzConj
      exact hzConj.1
    have hnzX : (n : X) * (z : X) = (m : X) :=
      congrArg (fun q : N => (q : X)) hnz
    refine ⟨b * ((n * z * n⁻¹ : N) : X), B.mul_mem hb hzConjB,
      (n : X), Set.mem_singleton _, ?_⟩
    rw [← hnzX]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]
  · intro hx
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact ⟨b, hb, (n : X), ⟨n, hn, rfl⟩, rfl⟩

/-- The double coset represented by a quotient class agrees with the double
coset of any supplied representative of that class. -/
public lemma B_mul_representativeSet_mul_B (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) (n : N)
    (hn : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) n = w) :
    (B : Set X) * representativeSet B N w * (B : Set X) =
      (B : Set X) * ({(n : X)} : Set X) * (B : Set X) := by
  rw [mul_assoc, representativeSet_mul_B B N w n hn, ← mul_assoc]

end Theory.AlgebraicGroup.TitsSystem
