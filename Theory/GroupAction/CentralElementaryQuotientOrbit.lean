module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction

/-!
# Elementary central extensions with involutory coset representatives

If a central elementary subgroup has an involutory representative in every
outside coset, the whole group has exponent two. We also record transitivity
of the actual S₄ core, obtained from its full automorphism action on the
three nonidentity elements. These are the extension and orbit steps in
Aschbacher–Smith J.4.4, printed p.441.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- An involutory orbit meeting every outside central coset forces elementarity. -/
theorem elementary_of_central_involution_cosets (N R : Subgroup G)
    (hc : N ≤ centralizer (R : Set G)) (hN : ∀ n∈N,n^2=1)
    (z : G) (hz : z^2=1)
    (hcover : ∀ x∈R,x∉N → ∃ g : G,x*(g*z*g⁻¹)⁻¹∈N) :
    IsElementaryAbelian 2 R := by
  have hp (x : R) : x^2=1 := by
    apply Subtype.ext
    change (x:G)^2=1
    by_cases hn : (x:G)∈N
    · exact hN x hn
    obtain ⟨g,hg⟩ := hcover x x.property hn
    let y := g*z*g⁻¹
    have hy : y^2=1 := by
      change (MulAut.conj g z)^2=1
      rw [← map_pow,hz,map_one]
    have hc' : Commute (x:G) ((x:G)*y⁻¹) := (hc hg) x x.property
    have he : Commute ((x:G)*y⁻¹) y := by
      have heq : y = ((x:G)*y⁻¹)⁻¹*(x:G) := by group
      conv_rhs => rw [heq]
      exact (Commute.refl ((x:G)*y⁻¹)).inv_right.mul_right hc'.symm
    have hh := he.mul_pow 2
    rw [hN _ hg,hy,one_mul,inv_mul_cancel_right] at hh
    exact hh
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp}
  intro a b
  exact Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b

end Subgroup

namespace Matrix.PSL3Two.ParabolicCoreModel
variable {G : Type*} [Group G] [Finite G]
/-- The full symmetric-four action is transitive on its nonidentity core elements. -/
theorem core_transitive (e : G ≃* Equiv.Perm (Fin 4))
    (x y : G) (hx : x∈pCore 2 G) (hy : y∈pCore 2 G) (hxn : x≠1) (hyn : y≠1) :
    ∃ g:G,g*x*g⁻¹=y := by
  classical
  let := (core_data e).1
  let : Nontrivial (pCore 2 G) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [(core_data e).2]; decide)
  let : IsKleinFour (pCore 2 G) := ⟨(core_data e).2,IsElementaryAbelian.exponent_eq_prime⟩
  let x' : pCore 2 G := ⟨x,hx⟩
  let y' : pCore 2 G := ⟨y,hy⟩
  have hx' : x'≠1 := fun h => hxn (congrArg Subtype.val h)
  have hy' : y'≠1 := fun h => hyn (congrArg Subtype.val h)
  let a : MulAut (pCore 2 G) := IsKleinFour.mulEquiv (Equiv.swap x' y')
    (Equiv.swap_apply_of_ne_of_ne (Ne.symm hx') (Ne.symm hy'))
  obtain ⟨q,hq⟩ := (coreQuotientAutEquiv e).surjective a
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) q
  refine ⟨g,?_⟩
  rw [← coreQuotientAutEquiv_mk e g x',hq]
  change (Equiv.swap x' y' x' : G)=y
  rw [Equiv.swap_apply_left]

end Matrix.PSL3Two.ParabolicCoreModel
