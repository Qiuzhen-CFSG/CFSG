module
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeToCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeToCoreMap

/-!
# Residuals and the cubic section above a two-core

Normal-subgroup core restriction identifies O^{p′}(A)/O_q(O^{p′}(A))
with the actual image O^{p′}(A/O_q(A)). In particular the cubic cores
have equal order. Restricting the original projection to O₂,₃(A), then
to its prime-to-three residual, constructs a two-core quotient isomorphic
to O₃(A/O₂(A)). These are isomorphisms of the intrinsic quotients.

Source application: Aschbacher--Smith 15.2.23(d), printed p.1117.
-/

public section
open Subgroup
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

/-- The intrinsic q-core quotient of O^{p′} is the residual in A/O_q(A). -/
noncomputable def primeToResidualCoreQuotientImage (p q : ℕ) [Fact p.Prime] :
    (primeToResidual p A ⧸ pCore q (primeToResidual p A)) ≃*
      primeToResidual p (A ⧸ pCore q A) :=
  (coreQuotientEquivImage q (primeToResidual p A)).trans
    (MulEquiv.subgroupCongr (map_primeToResidual_of_surjective p _
      (QuotientGroup.mk'_surjective _)))

/-- The cubic core of this residual quotient has the same order as in A/O₂(A). -/
theorem card_cubicCore_residual_quotient :
    Nat.card (pCore 3 (primeToResidual 3 A ⧸ pCore 2 (primeToResidual 3 A))) =
      Nat.card (pCore 3 (A ⧸ pCore 2 A)) := by
  let e := primeToResidualCoreQuotientImage (A := A) 3 2
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,pCore_map_iso 3 e]
  rw [← card_map_of_injective (primeToResidual 3 (A ⧸ pCore 2 A)).subtype_injective,
    map_pCore_primeToResidual]

/-- The prime-to-three residual of O₂,₃(A) has the cubic core itself as
its two-core quotient, through the original projection. -/
noncomputable def cubicResidualQuotientEquiv :
    let C := (pCore 3 (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))
    (primeToResidual 3 C ⧸ pCore 2 (primeToResidual 3 C)) ≃*
      pCore 3 (A ⧸ pCore 2 A) := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 A)
  let B := pCore 3 (A ⧸ pCore 2 A)
  let C := B.comap q
  let f : C →* B := (q.comp C.subtype).codRestrict B (fun x => x.property)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b.val
    exact ⟨⟨a,show q a ∈ B from ha.symm ▸ b.property⟩,Subtype.ext ha⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 A).comap C.subtype := by
      ext x
      change (⟨q x.val,x.property⟩ : B) = 1 ↔ x.val ∈ pCore 2 A
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff x.val
    rw [he]
    exact pCore_isPGroup.comap_subtype
  have hres : primeToResidual 3 B = ⊤ :=
    top_unique (le_primeToResidual_of_isPGroup (pCore_isPGroup.of_equiv topEquiv.symm))
  have hbot : pCore 2 B = ⊥ := by
    have hB : IsPGroup 3 (⊤ : Subgroup B) := pCore_isPGroup.of_equiv topEquiv.symm
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 2) (G := B))
      hB (by decide : Nat.Coprime 2 3)
    simpa only [disjoint_top] using hd
  exact (f.primeToResidualCoreQuotientEquiv 3 2 hf hk hres).trans
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot (G := B)))

end Subgroup
