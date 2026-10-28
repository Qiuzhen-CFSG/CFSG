module
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Quotient markings for subgroups covering a prime core

If A ≤ L and L = A Oₚ(L), the inclusion induces an isomorphism
A/Oₚ(A) ≃ L/Oₚ(L). The restricted quotient map is surjective with
p-group kernel; lifting p-cores identifies its kernel with Oₚ(A).
The equivalence retains the inclusion on every representative.

This is the quotient-marking step for the literal covering intersection
component in Aschbacher–Smith, 4.2.12, printed p.610 (1 March 2004).
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A cover modulo the ambient prime core identifies the intrinsic
prime-core quotients by the literal inclusion. -/
theorem exists_pCoreQuotientEquiv_of_cover {A L : Subgroup G}
    (hAL : A ≤ L)
    (hcover : (L : Set G) ⊆ (A : Set G) * (L.pCoreIn p : Set G)) :
    ∃ e : (A ⧸ pCore p A) ≃* (L ⧸ pCore p L),
      ∀ a : A, e (QuotientGroup.mk' (pCore p A) a) =
        QuotientGroup.mk' (pCore p L) (inclusion hAL a) := by
  let q := QuotientGroup.mk' (pCore p L)
  let f := q.comp (inclusion hAL)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := hq y
    obtain ⟨a, ha, n, hn, he⟩ := hcover l.property
    obtain ⟨n, hn, rfl⟩ := hn
    refine ⟨⟨a, ha⟩, ?_⟩
    have hel : inclusion hAL ⟨a, ha⟩ * n = l := Subtype.ext he
    change q (inclusion hAL ⟨a, ha⟩) = q l
    rw [← hel, map_mul]
    have hnq : q n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    rw [hnq, mul_one]
  have hk : IsPGroup p f.ker := by
    change IsPGroup p (q.comp (inclusion hAL)).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hAL)
  have hqk : IsPGroup p q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcoreL := q.comap_pCore_of_ker_isPGroup hq hqk
  have hker : f.ker = pCore p A := by
    change (q.comp (inclusion hAL)).ker = pCore p A
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', ← hcoreL, comap_comap]
    exact f.comap_pCore_of_ker_isPGroup hf hk
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e, fun a => rfl⟩
end Subgroup
