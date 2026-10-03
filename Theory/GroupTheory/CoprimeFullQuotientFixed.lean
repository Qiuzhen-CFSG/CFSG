module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Fixed elements of a full coprime quotient action

Let Q and D be normal in a finite group, with Q a two-group and T a
three-group. If [Q,Q] lies in D, Q=[Q,E]D, and E lies in Q join T, then
all T-fixed elements of Q lie in D. There is no faithfulness or special
module assumption; the quotient only needs to be abelian.

Pass to the quotient by D. The image U of Q is abelian and normal. Write
each E-image element as u*t with u in U and t in the T-image. The
commutator product identity and commutativity of U give [U,E]≤[U,T], so
U=[U,T]. On the same native conjugation action, the coprime fixed-point
and commutator subgroups are complementary. Full commutator therefore
makes the fixed subgroup trivial, and pulling back proves the claim.

This elementary coprime-action transfer is used for C_Q(T)≤D in
Stellmacher (8.6)(c), Journal of Algebra 190 (1997), printed pp.41 and 45.
The theorem is independent of the campaign's graph and model definitions.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative
universe u
public theorem centralizer_le_layer_of_full_coprime_quotient
    {G : Type u} [Group G] [Finite G]
    (Q D E T : Subgroup G) [Q.Normal] [D.Normal]
    (hQ : IsPGroup 2 Q) (hT : IsPGroup 3 T)
    (hcomm : ⁅Q,Q⁆ ≤ D) (hfull : Q = ⁅Q,E⁆ ⊔ D)
    (hE : E ≤ Q ⊔ T) : Q ⊓ centralizer (T : Set G) ≤ D := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let π : G →* G ⧸ D := QuotientGroup.mk' D
  let U := Q.map π
  let V := T.map π
  let F := E.map π
  let _ : U.Normal := (inferInstance : Q.Normal).map π (QuotientGroup.mk'_surjective D)
  have hUU : ⁅U,U⁆ = ⊥ := by
    have hh := Subgroup.map_mono (f := π) hcomm
    rw [Subgroup.map_commutator,QuotientGroup.map_mk'_self] at hh
    exact bot_unique hh
  let _ : IsMulCommutative U := Subgroup.commutator_self_eq_bot_iff.mp hUU
  have hUC : U ≤ centralizer (U : Set (G ⧸ D)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUU
  have hF : F ≤ U ⊔ V := by
    have hh := Subgroup.map_mono (f := π) hE
    rwa [Subgroup.map_sup] at hh
  have hUF : U = ⁅U,F⁆ := by
    have hh := congrArg (Subgroup.map π) hfull
    rw [Subgroup.map_sup,Subgroup.map_commutator,QuotientGroup.map_mk'_self,sup_bot_eq] at hh
    exact hh
  have hbound : ⁅U,F⁆ ≤ ⁅U,V⁆ := by
    apply Subgroup.commutator_le.mpr
    intro q hq e he
    obtain ⟨u,hu,t,ht,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hF he)
    have hqt : ⁅q,t⁆ ∈ ⁅U,V⁆ := Subgroup.commutator_mem_commutator hq ht
    have hqtU : ⁅q,t⁆ ∈ U := Subgroup.commutator_le_left U V hqt
    have hqu : Commute q u := (Subgroup.mem_centralizer_iff.mp (hUC hq) u hu).symm
    have hucomm : u * ⁅q,t⁆ * u⁻¹ = ⁅q,t⁆ := mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp (hUC hu) _ hqtU).symm
    rw [commutatorElement_mul_right_eq_mul_conj,hqu.commutator_eq,one_mul,hucomm]
    exact hqt
  have hUfull : ⁅U,V⁆ = U := le_antisymm (Subgroup.commutator_le_left _ _) (hUF.le.trans hbound)
  let norm : V ≤ Subgroup.normalizer (U : Set (G ⧸ D)) := Subgroup.le_normalizer_of_normal
  let _ : Subgroup.Normalizes V U := ⟨norm⟩
  have haction : commutatorAction V U = ⊤ := by
    apply Subgroup.map_injective U.subtype_injective
    rw [commutatorAction_subgroup_conj_map_eq_commutator U V norm,hUfull,
      ←MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hcop : Nat.Coprime (Nat.card V) (Nat.card U) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) V U (hT.map π) (hQ.map π)
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := U) (A := V) (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop inferInstance
  have hfix : FixedPoints.subgroup V U = ⊥ := by
    have hh := hcompl.disjoint
    rw [haction] at hh
    exact disjoint_top.mp hh
  intro x hx
  let xU : U := ⟨π x,Subgroup.mem_map_of_mem π hx.1⟩
  have hxfix : xU ∈ FixedPoints.subgroup V U := by
    intro t
    apply Subtype.ext
    change (t : G ⧸ D) * π x * (t : G ⧸ D)⁻¹ = π x
    obtain ⟨s,hs,hst⟩ := t.property
    rw [←hst,←map_inv,←map_mul,←map_mul]
    apply congrArg π
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hx.2 s hs)
  have hxone : xU = 1 := by simpa only [hfix,Subgroup.mem_bot] using hxfix
  exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hxone)
end Subgroup
