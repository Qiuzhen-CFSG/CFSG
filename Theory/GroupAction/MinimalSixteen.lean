module
public import Theory.GroupTheory.MaximalSylowKernel
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupAction.Invariant
public import Mathlib.Data.Finite.Perm

/-!
# Simplicity of a sixteen-element module with a nine-element actor

Let a finite group with trivial two-core have a maximal Sylow two-subgroup.
If an order-nine subgroup has no fixed points on an elementary abelian
module of order sixteen, every invariant subgroup is trivial or the whole
module. No irreducibility or model identification is assumed.

On a nonzero invariant subgroup the nine-element actor retains a nontrivial
image. Maximal-Sylow kernel rigidity makes the restricted action faithful.
An invariant subgroup of order two or four cannot support even a faithful
permutation action of the nine-element actor; order eight is excluded by
its automorphism-group order168. Divisibility leaves order sixteen.

This elementary counting argument supplies the irreducibility needed for
the module comparison in Stellmacher (9.1), printed p48 of
`refs/files/stellmacher-n-group.pdf`. The result is independent of its graph
context and applies to the supplied action and invariance instance.
-/

open scoped IsMulCommutative

public theorem invariant_eq_bot_or_top_of_nine_actor_maximal_sylow
    {X V : Type*} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (S : Sylow 2 X) (hS : IsCoatom (S : Subgroup X))
    (hcore : pCore 2 X = ⊥) (F : Subgroup X) (hF : Nat.card F = 9)
    (hfixed : FixedPoints.subgroup F V = ⊥) (hV : Nat.card V = 16)
    (D : Subgroup V) [IsInvariant X V D] : D = ⊥ ∨ D = ⊤ := by
  by_cases hD : D = ⊥
  · exact Or.inl hD
  right
  let action := MulDistribMulAction.toMulAut X D
  have hnontrivial : F.map action ≠ ⊥ := by
    intro htrivial
    apply hD
    apply bot_unique
    intro point hpoint
    apply hfixed.le
    intro actor
    have heq : action actor = 1 := Subgroup.mem_bot.mp
      (htrivial ▸ Subgroup.mem_map_of_mem action actor.property)
    have heval := MulEquiv.congr_fun heq (⟨point, hpoint⟩ : D)
    exact congrArg Subtype.val heval
  have hinj : Function.Injective action :=
    action.injective_of_coatom_sylow_of_nontrivial_odd_image S hS hcore F
      (by rw [hF]; decide) hnontrivial
  let permutation := MulAction.toPermHom X D
  have hperm : Function.Injective permutation := by
    intro a b hab
    apply hinj
    ext point
    exact congrArg Subtype.val (Equiv.congr_fun hab point)
  have hdiv : 9 ∣ (Nat.card D).factorial := by
    have hd := Subgroup.card_dvd_of_injective (permutation.comp F.subtype)
      (hperm.comp F.subtype_injective)
    simpa only [hF, Nat.card_perm] using hd
  have hcardD : Nat.card D ∣ 2 ^ 4 := by
    simpa [hV] using D.card_subgroup_dvd_card
  obtain ⟨n, hn, heq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hcardD
  interval_cases n
  · exact (hD (Subgroup.card_eq_one.mp (by simpa using heq))).elim
  · norm_num [heq, Nat.factorial] at hdiv
  · norm_num [heq, Nat.factorial] at hdiv
  · let _ : IsElementaryAbelian 2 D := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro point
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 V) (point : V) }
    have hd := Subgroup.card_dvd_of_injective (action.comp F.subtype)
      (hinj.comp F.subtype_injective)
    rw [hF, card_mulAut_of_elementary_eight D (by simpa using heq)] at hd
    norm_num at hd
  · exact Subgroup.eq_top_of_card_eq D (by simpa [hV] using heq)
