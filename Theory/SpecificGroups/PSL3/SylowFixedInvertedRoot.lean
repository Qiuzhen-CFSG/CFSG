module
public import Theory.GroupAction.InvertedPrimeLift
public import Theory.GroupAction.PerfectCentralQuotientSylow
public import Theory.SpecificGroups.PSL3.SylowFixedActions.OddPrimeInner
public import Theory.SpecificGroups.PSL3.OddInvolutionRoot

/-!
# Prime-order witnesses for odd linear-three Sylow fixers

An involution of a perfect central cover of PSL₃(p) fixing a Sylow
2-subgroup induces an inner automorphism on the projective group when
p > 3. The actual inner involution inverts a root element of order p.
If the original action fixes the covering center, the equivariant
prime-inversion lift supplies an element of the same order upstairs.

The quotient isomorphism, automorphism, fixed Sylow and central kernel
are retained. Source application: Aschbacher--Smith 12.6.26, printed p.832;
the root calculation is the one used in E.2.17, printed p.230.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3
variable {B F : Type*} [Group B] [Finite B] [Group.IsPerfect B]
  [IsSimpleGroup (B ⧸ center B)] [Field F] [Finite F]

/-- A fixed-center Sylow fixer inverts an element of the defining prime order in the original cover. -/
theorem sylow_fixer_inverts_prime_of_fixes_center
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hl : 3 < p) (hF : Nat.card F = p)
    (e : B ⧸ center B ≃* PSL(3,F)) (a : MulAut B) (ha : orderOf a = 2)
    (P : Sylow 2 B) (hP : ∀ x ∈ P, a x = x)
    (hZ : ∀ x ∈ center B, a x = x) :
    ∃ x : B, orderOf x = p ∧ a x = x⁻¹ := by
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3,F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (center B)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let b := MulAut.centralQuotientAction e a
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans ha
  obtain ⟨Q,hQ⟩ := MulAut.centralQuotientAction_exists_fixed_sylow e a P hP
  obtain ⟨t,ht⟩ := SylowFixedActions.OddPrime.involution_mem_inner_of_fixes_sylow
    p hp ho hl hF Q b hb hQ
  have hc : center PSL(3,F) = ⊥ := by
    rcases (inferInstance : (center PSL(3,F)).Normal).eq_bot_or_eq_top with hc|hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hc)).elim
  have htc : orderOf t = 2 := by
    have hi := MulAut.conj_injective_of_center_eq_bot hc
    exact (orderOf_injective (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F)) hi t).symm.trans
      (ht ▸ hb)
  obtain ⟨y,hy,hi⟩ := OddInvolutionRoot.exists_inverted_root hp ho hF t htc
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  apply MulAut.exists_inverted_prime_of_fixed_kernel a b f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun x => (MulAut.centralQuotientAction_apply e a x).symm)
    (ha ▸ pow_orderOf_eq_one a) ?_ hp ho y hy ?_
  · intro x hx
    apply hZ x
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    exact hx.trans e.map_one.symm
  · rw [←ht]
    exact hi
end Matrix.PSL3
