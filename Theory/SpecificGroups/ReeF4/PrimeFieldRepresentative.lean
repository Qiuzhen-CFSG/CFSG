module
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups
public import Theory.GroupAction.PrimeCoefficientRepresentative

/-!
# Prime field representatives in Ree automorphism overgroups

For the actual matrix group supplied by `LocalBlockInput`, inner–field
coverage and field separation extract a canonical field element from an
outer prime-order actor. Cancelling its inner factor retains membership in
the original automorphism overgroup. The coefficient degree is divisible by
that prime, and the extracted element has the same prime order.

Simplicity and perfectness are inherited hypotheses on the supplied group.
The source consumer in `NonblockEndgameSieveModelsFieldActors` applies this
to the literal transported action on the full component two-core quotient.
Source: Aschbacher–Smith A.3.18, printed pp.51–53; the matrix coverage and
separation references are recorded in the imported Ree modules.
-/

public section
noncomputable section
open Subgroup
namespace ReeF4.LocalBlockInput

/-- Extract a prime field representative inside the same automorphism overgroup. -/
theorem exists_prime_field_representative {m p : ℕ} [Fact p.Prime]
    (hm : 1≤m) (d : ReeF4.LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (A : Subgroup (MulAut d.fixedGroup)) (hinner : MulAut.innerSubgroup d.fixedGroup ≤ A)
    (a : MulAut d.fixedGroup) (ha : a∈A) (hp : orderOf a=p)
    (hout : a∉MulAut.innerSubgroup d.fixedGroup) :
    p ∣ 2*m+1 ∧ ∃ (g : d.fixedGroup) (σ : zpowers d.fieldAutomorphism),
      a=MulAut.conj g * σ.val ∧ orderOf σ=p ∧ σ.val∈A ∧
      orderOf σ.val=p ∧ σ.val∉MulAut.innerSubgroup d.fixedGroup := by
  have hfaithful : Function.Injective d.fieldOuterHom := by
    apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp (ReeF4.Cartan.field_disjoint_innerDiagonal d)
      σ.property (ReeF4.Cartan.inner_le_innerDiagonal d ((QuotientGroup.eq_one_iff _).mp hσ))
  have hcover (a : MulAut d.fixedGroup) : ∃ g : d.fixedGroup,
      ∃ σ : zpowers d.fieldAutomorphism, a=MulAut.conj g * σ.val := by
    obtain ⟨g,k,hk⟩ := ReeF4.LocalBlockInput.inner_field hm d a
    exact ⟨g,⟨d.fieldAutomorphism^k,zpow_mem_zpowers _ k⟩,hk⟩
  obtain ⟨g,σ,he,hσ,hA,ho,hi⟩ := MulAut.exists_prime_coefficient_in_overgroup
    (zpowers d.fieldAutomorphism).subtype hfaithful hcover A hinner a ha hp hout
  have hdiv : p ∣ 2*m+1 := by
    have hh := orderOf_dvd_natCard σ
    rw [hσ,Nat.card_zpowers] at hh
    exact hh.trans d.orderOf_fieldAutomorphism_dvd
  exact ⟨hdiv,g,σ,he,hσ,hA,ho,hi⟩

end ReeF4.LocalBlockInput
