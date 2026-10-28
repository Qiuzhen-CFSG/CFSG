module

public import Theory.GroupAction.CoprimeFixedConjugacy
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Fixed conjugators between invariant subgroups

The transporter between two invariant subgroups, restricted to a normalized
finite group, is a coset of a relative normalizer. A prime-power actor of
coprime order therefore fixes a transporter element. The subgroups need not
lie in the group of conjugators, as required for roots outside a local core.
-/

public section
open Subgroup
namespace Theory.GroupAction
variable {G : Type*} [Group G]

private def conjSubgroup (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

private theorem conjSubgroup_mul (A : Subgroup G) (g h : G) :
    conjSubgroup A (g*h)=conjSubgroup (conjSubgroup A h) g := by
  unfold conjSubgroup
  rw [map_map]
  congr 1
  ext x
  change (g*h)*x*(g*h)⁻¹=g*(h*x*h⁻¹)*g⁻¹
  group

private theorem conjSubgroup_one (A : Subgroup G) : conjSubgroup A 1=A := by
  unfold conjSubgroup
  have h : (MulAut.conj (1:G)).toMonoidHom=MonoidHom.id G := by ext x; simp
  rw [h,Subgroup.map_id]

/-- Two invariant subgroups conjugate by the specified coprime group have
a conjugator in that same group centralizing the prime-power actor. -/
theorem exists_centralizing_conjugator_of_invariant_subgroups
    (N C A B : Subgroup G) [Finite N]
    (hCN : C≤normalizer (N:Set G))
    (hCA : C≤normalizer (A:Set G)) (hCB : C≤normalizer (B:Set G))
    {p : ℕ} [Fact p.Prime] (hC : IsPGroup p C) (hp : ¬p∣Nat.card N)
    (hg : ∃ g∈N, A.map (MulAut.conj g).toMonoidHom=B) :
    ∃ g∈N⊓centralizer (C:Set G), A.map (MulAut.conj g).toMonoidHom=B := by
  obtain ⟨g,hgN,hg⟩ := hg
  change conjSubgroup A g=B at hg
  let T := {n : N // conjSubgroup A (n:G)=B}
  let D := (normalizer (A:Set G)).subgroupOf N
  have hnorm (n : D) : conjSubgroup A ((n:N):G)=A :=
    mem_normalizer_iff_map_conj_eq.mp n.property
  let e : D ≃ T := {
    toFun n := ⟨⟨g*(n:N),N.mul_mem hgN (n:N).property⟩,by
      rw [conjSubgroup_mul,hnorm]
      exact hg⟩
    invFun n := ⟨⟨g⁻¹*(n:N),N.mul_mem (N.inv_mem hgN) (n:N).property⟩,
      mem_normalizer_iff_map_conj_eq.mpr (by
        change conjSubgroup A (g⁻¹*(n:N))=A
        rw [conjSubgroup_mul,n.property,←hg,←conjSubgroup_mul,inv_mul_cancel,conjSubgroup_one])⟩
    left_inv n := Subtype.ext (Subtype.ext (inv_mul_cancel_left _ _))
    right_inv n := Subtype.ext (Subtype.ext (mul_inv_cancel_left _ _)) }
  let act (c : C) : MulAut N := N.normalizerMonoidHom ⟨c,hCN c.property⟩
  let _ : MulAction C T := {
    smul c n := ⟨act c n,by
      change conjSubgroup A ((c:G)*(n:N)*(c:G)⁻¹)=B
      rw [conjSubgroup_mul,conjSubgroup_mul]
      have hAc : conjSubgroup A (c:G)⁻¹=A :=
        mem_normalizer_iff_map_conj_eq.mp (hCA (C.inv_mem c.property))
      rw [hAc,n.property]
      exact mem_normalizer_iff_map_conj_eq.mp (hCB c.property)⟩
    one_smul n := by
      apply Subtype.ext
      apply Subtype.ext
      change (1:G)*(n:N)*(1:G)⁻¹=(n:N)
      simp
    mul_smul c d n := by
      apply Subtype.ext
      apply Subtype.ext
      change ((c:G)*(d:G))*(n:N)*((c:G)*(d:G))⁻¹=
        (c:G)*((d:G)*(n:N)*(d:G)⁻¹)*(c:G)⁻¹
      group }
  have hT : ¬p∣Nat.card T := by
    rw [←Nat.card_congr e]
    exact fun h => hp (h.trans D.card_subgroup_dvd_card)
  obtain ⟨n,hn⟩ := hC.nonempty_fixed_point_of_prime_not_dvd_card T hT
  refine ⟨(n:N),⟨(n:N).property,?_⟩,n.property⟩
  intro c hc
  have hh := congrArg (fun z : T => ((z:N):G)) (hn ⟨c,hc⟩)
  change c*(n:N)*c⁻¹=(n:N) at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

end Theory.GroupAction
