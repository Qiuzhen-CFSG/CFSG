module
public import Theory.GroupAction.SymplecticSmallTwoSection
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.ElementaryAbelian.Basic

/-!
# Perfect actors on small prime-group sections

A perfect group with a simple quotient and solvable kernel acts trivially
on a two-section smaller than the binary degree of a prime dividing the
simple quotient. The kernel is retained, including any central covering
factor. This follows by excluding the simple section from the automorphism
group using orbit counting.

If the resulting displacement lies in a central elementary two-subgroup,
every square is fixed. A trivial fixed subgroup therefore makes the whole
two-group elementary. The literal Mathieu pushing-up consumer applies this
to its entire radical image, rather than a restricted displacement domain.

Source application: Aschbacher–Smith 4.2.13 and 4.4.14,
printed pp.611–612 and 624–625.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]

/-- A perfect soluble extension of a simple group fixes small two-sections. -/
theorem commutator_perfect_le_of_primitive_small_section
    (B U E : Subgroup G) [Finite U] [Group.IsPerfect B]
    [(E.subgroupOf U).Normal]
    (q : B →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    {p m : ℕ} (hp : p.Prime) (hS : p ∣ Nat.card S)
    (hU : IsPGroup 2 U) (hcard : E.relIndex U ≤ 2 ^ m)
    (horder : m < orderOf (2 : ZMod p))
    (hBU : B ≤ normalizer (U : Set G)) (hBE : B ≤ normalizer (E : Set G)) :
    ⁅U,B⁆ ≤ E := by
  let X := U ⧸ E.subgroupOf U
  have hX : IsPGroup 2 X := hU.to_quotient _
  obtain ⟨a,ha⟩ := exists_quotient_conjugation_action B U E hBU hBE inferInstance
  have haone : a = 1 := hom_eq_one_of_no_simple_section q hq (fun W f hf => by
    have hd := (card_dvd_of_surjective f hf).trans W.card_subgroup_dvd_card
    exact MulAut.not_prime_dvd_card_of_twoGroup_card_bound hp hX hcard horder
      (hS.trans hd)) a
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb u hu
  have hfix := ha ⟨b,hb⟩ ⟨u,hu⟩
  rw [haone] at hfix
  have he := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change b*u*b⁻¹/u ∈ E at he
  simpa only [div_eq_mul_inv,commutatorElement_def] using he

/-- Central binary displacement and no fixed points force exponent two. -/
theorem elementary_of_central_binary_displacement
    (U E B : Subgroup G) [IsElementaryAbelian 2 E]
    (hcent : U ≤ centralizer (E : Set G)) (hdisp : ⁅U,B⁆ ≤ E)
    (hfix : U ⊓ centralizer (B : Set G) = ⊥) : IsElementaryAbelian 2 U := by
  have hsq (u : U) : u ^ 2 = 1 := by
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfix]
    refine ⟨U.pow_mem u.property 2,?_⟩
    intro b hb
    let d := ⁅b,(u : G)⁆
    have hd : d ∈ E := hdisp (by rw [commutator_comm]; exact commutator_mem_commutator hb u.property)
    have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d hd
    have hdu : Commute d (u : G) := hcent u.property d hd
    have he : b*(u : G)*b⁻¹ = d*u := by dsimp [d]; group
    have hpow : b*(u : G)^2*b⁻¹ = (u : G)^2 := by
      calc
        _ = (b*(u : G)*b⁻¹)^2 := map_pow (MulAut.conj b) (u : G) 2
        _ = (d*(u : G))^2 := by rw [he]
        _ = _ := by rw [hdu.mul_pow,hd2,one_mul]
    exact mul_inv_eq_iff_eq_mul.mp hpow
  let : IsMulCommutative U := ⟨⟨fun u v =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) u v).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq⟩
end Subgroup
