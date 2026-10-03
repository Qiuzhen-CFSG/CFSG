module
public import Theory.GroupTheory.QuaternionCentralProductDiagonal
public import Theory.GroupTheory.QuaternionCentralProductCommutator

/-!
# Membership in quaternion diagonals

For commuting quaternion factors with shared intersection of order two, an
actual factor isomorphism defines the elementary diagonal of order eight.
An element b*c belongs to it exactly when the discrepancy θ(b)⁻¹*c belongs
to the shared intersection. The ambient group is finite for the cardinal
product argument used here.

The diagonal and either factor generate the full central product. Their
orders8,8 and32 imply that their intersection has order2, and thus equals
the known shared intersection. Dividing b*c by the diagonal element b*θ(b)
reduces membership to this intersection calculation.

This precise membership criterion supplies the factor-automorphism action
on invariant diagonals in Stellmacher (9.1), Journal of Algebra190 (1997),
p.48. The actual diagonal definition and factor isomorphism are retained.

The companion normalization theorem applies without finite ambient hypotheses.
Conjugation by a central-product element changes each factor coordinate by an
element of the shared intersection. On a diagonal generator these two changes
multiply to another intersection element, which remains in the diagonal.
The factors also preserve the intersection, so they normalize the whole join.
-/

namespace Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A factor product lies in the diagonal exactly when its two coordinates
match modulo the shared intersection. -/
public theorem mem_quaternionDiagonal_mul_iff (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) (b : B) (c : C) :
    (b:G)*(c:G) ∈ quaternionDiagonal B C θ hcomm ↔
      (θ b:G)⁻¹*(c:G) ∈ B ⊓ C := by
  let D := quaternionDiagonal B C θ hcomm
  obtain ⟨_, hDcard, hID, hDV⟩ := quaternion_diagonal_elementary_eight B C model θ hinter hcomm
  have hdiag (a : B) : (a:G)*(θ a:G) ∈ D :=
    (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨a,rfl⟩
  have hBCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro a ha d hd
    exact (hcomm a ha d hd).symm
  have hVn : B ⊔ C ≤ normalizer (C : Set G) := sup_le hBCn C.le_normalizer
  have hsup : D ⊔ C = B ⊔ C := by
    apply le_antisymm (sup_le hDV le_sup_right)
    apply sup_le ?_ le_sup_right
    intro a ha
    have hh := (D ⊔ C).mul_mem (mem_sup_left (hdiag ⟨a,ha⟩))
      (mem_sup_right (C.inv_mem (θ ⟨a,ha⟩).property))
    simpa only [mul_inv_cancel_right] using hh
  have hBcard : Nat.card B = 8 := by
    rw [Nat.card_congr model.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hCcard : Nat.card C = 8 := (Nat.card_congr θ.symm.toEquiv).trans hBcard
  have hVcard : Nat.card (B ⊔ C : Subgroup G) = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBCn
    rw [hBcard, hCcard, inf_comm C B, hinter, sup_comm C B] at hh
    omega
  have hDCcard : Nat.card (D ⊓ C : Subgroup G) = 2 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C D (hDV.trans hVn)
    rw [hCcard, hDcard, inf_comm C D, sup_comm C D, hsup, hVcard] at hh
    omega
  have hDC : D ⊓ C = B ⊓ C :=
    (eq_of_le_of_card_ge (le_inf hID inf_le_right) (by rw [hinter,hDCcard])).symm
  have hresC : (θ b:G)⁻¹*(c:G) ∈ C := C.mul_mem (C.inv_mem (θ b).property) c.property
  constructor
  · intro hbc
    have hh := D.mul_mem (D.inv_mem (hdiag b)) hbc
    have hd : (θ b:G)⁻¹*(c:G) ∈ D := by
      have heq : ((b:G)*(θ b:G))⁻¹*((b:G)*(c:G)) = (θ b:G)⁻¹*(c:G) := by group
      rwa [heq] at hh
    exact hDC ▸ (show (θ b:G)⁻¹*(c:G) ∈ D ⊓ C from ⟨hd,hresC⟩)
  · intro hres
    have hh := D.mul_mem (hdiag b) (hID hres)
    simpa only [mul_assoc, mul_inv_cancel_left] using hh

/-- The central product normalizes every diagonal formed from its commuting
quaternion factors. No finite ambient-group hypothesis is needed. -/
public theorem sup_le_normalizer_quaternionDiagonal
    {G : Type*} [Group G] (B C : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (θ : B ≃* C)
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) :
    B ⊔ C ≤ normalizer (quaternionDiagonal B C θ hcomm : Set G) := by
  let D := quaternionDiagonal B C θ hcomm
  have hID : B ⊓ C ≤ D := le_sup_right
  have hdiffB (v : G) (hv : v ∈ B ⊔ C) (b : G) (hb : b ∈ B) :=
    factor_central_difference_of_mem_sup B C model hinter hcomm v hv b hb
  have hdiffC (v : G) (hv : v ∈ B ⊔ C) (c : G) (hc : c ∈ C) :
      c⁻¹*(v*c*v⁻¹) ∈ B ⊓ C := by
    rw [inf_comm]
    exact factor_central_difference_of_mem_sup C B (θ.symm.trans model)
      (by simpa only [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm) v (by simpa only [sup_comm] using hv) c hc
  apply le_normalizer_iff.mpr
  intro v hv d hd
  have hle : D ≤ D.comap (MulAut.conj v).toMonoidHom := by
    apply sup_le
    · intro x hx
      obtain ⟨b,rfl⟩ := hx
      let z := (b:G)⁻¹*(v*(b:G)*v⁻¹)
      let w := (θ b:G)⁻¹*(v*(θ b:G)*v⁻¹)
      have hz := hdiffB v hv b b.property
      have hw := hdiffC v hv (θ b) (θ b).property
      have hzcomm : z * (θ b:G) = (θ b:G) * z := hcomm z hz.1 (θ b) (θ b).property
      have hdiag : (b:G)*(θ b:G) ∈ D :=
        (show (quaternionDiagonalHom B C θ hcomm).range ≤ D from le_sup_left) ⟨b,rfl⟩
      have hh := D.mul_mem hdiag (D.mul_mem (hID hz) (hID hw))
      change v*((b:G)*(θ b:G))*v⁻¹ ∈ D
      have heq : v*((b:G)*(θ b:G))*v⁻¹ = ((b:G)*(θ b:G))*(z*w) := by
        calc
          v*((b:G)*(θ b:G))*v⁻¹ = ((b:G)*z)*((θ b:G)*w) := by dsimp [z,w]; group
          _ = ((b:G)*(θ b:G))*(z*w) := by rw [mul_assoc, ← mul_assoc z, hzcomm]; simp only [mul_assoc]
      rwa [heq]
    · intro x hx
      have hxb : v*x*v⁻¹ ∈ B := by
        simpa only [mul_inv_cancel_left] using B.mul_mem hx.1 (hdiffB v hv x hx.1).1
      have hxc : v*x*v⁻¹ ∈ C := by
        simpa only [mul_inv_cancel_left] using C.mul_mem hx.2 (hdiffC v hv x hx.2).2
      exact hID ⟨hxb,hxc⟩
  exact hle hd

end Subgroup
