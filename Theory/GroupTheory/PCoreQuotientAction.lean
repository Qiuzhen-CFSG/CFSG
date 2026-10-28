module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The kernel of the action on a normal subgroup modulo its prime core

If A is normal in H, H/A is a p-group, and A/O_p(A) has trivial center,
the kernel of conjugation on A/O_p(A) is exactly O_p(H). The intersection
of that kernel with A lies in O_p(A); its image in H/A is a p-group.
Conversely, [O_p(H), A] lies in O_p(H) ∩ A ≤ O_p(A).

The proof works without finiteness. Its source application identifies the
literal R_v in Aschbacher--Smith, Section 12.6, printed p.824, before lifting
the quotient normalizer in Lemma 12.6.5.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] (p : ℕ)

/-- The p-core acts trivially on a normal subgroup modulo its own p-core. -/
theorem pCore_le_quotientAction_ker (A : Subgroup G) [A.Normal] :
    pCore p G ≤ ((quotientAut (pCore p A)).comp
      (MulAut.conjNormal : G →* MulAut A)).ker := by
  intro r hr
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro w
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) w
  rw [MonoidHom.comp_apply, quotientAut_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  have hle : (pCore p G).subgroupOf A ≤ pCore p A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  apply hle
  change r * (a : G) * r⁻¹ / (a : G) ∈ pCore p G
  rw [div_eq_mul_inv]
  have hc := (commutator_le_left (pCore p G) A)
    (commutator_mem_commutator hr a.property)
  exact hc

/-- A centerless core quotient and a p-group outer quotient identify the action kernel. -/
theorem quotientAction_ker_eq_pCore (A : Subgroup G) [A.Normal]
    (hq : IsPGroup p (G ⧸ A)) (hz : center (A ⧸ pCore p A) = ⊥) :
    ((quotientAut (pCore p A)).comp
      (MulAut.conjNormal : G →* MulAut A)).ker = pCore p G := by
  let f := (quotientAut (pCore p A)).comp (MulAut.conjNormal : G →* MulAut A)
  let q := (QuotientGroup.mk' A).comp f.ker.subtype
  have hker : q.ker ≤ (A.pCoreIn p).subgroupOf f.ker := by
    intro x hx
    have hxA : (x : G) ∈ A := by
      apply (QuotientGroup.eq_one_iff (x : G)).mp
      exact hx
    let a : A := ⟨x, hxA⟩
    have hcentral : QuotientGroup.mk' (pCore p A) a ∈ center (A ⧸ pCore p A) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) w
      have he := congrArg (fun u : MulAut (A ⧸ pCore p A) =>
        u (QuotientGroup.mk' (pCore p A) b)) x.property
      simp only [f, MonoidHom.comp_apply, quotientAut_apply_mk] at he
      change QuotientGroup.mk' (pCore p A) (a * b * a⁻¹) =
        QuotientGroup.mk' (pCore p A) b at he
      rw [map_mul, map_mul, map_inv] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [hz, mem_bot] at hcentral
    exact ⟨a, (QuotientGroup.eq_one_iff a).mp hcentral, rfl⟩
  have hpker : IsPGroup p q.ker :=
    ((isPGroup_pCoreIn p A).comap_subtype).to_le hker
  have hpf : IsPGroup p f.ker := by
    have htop := (hq.to_subgroup (⊤ : Subgroup (G ⧸ A))).comap_of_ker_isPGroup q hpker
    rw [comap_top] at htop
    exact htop.of_equiv Subgroup.topEquiv
  exact le_antisymm (le_sSup ⟨inferInstance, hpf⟩) (pCore_le_quotientAction_ker p A)
end Subgroup
