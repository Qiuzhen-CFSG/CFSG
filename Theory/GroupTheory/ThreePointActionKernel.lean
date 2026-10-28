module
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Fixed points for permutation actions on two or three points

The preimage of the alternating subgroup of a three-point action is a
normal three-group when its kernel is a three-group. If the three-core
already lies in the kernel, the permutation image embeds in the sign
group and hence fixes a point. On at most two points, a permutation with a
fixed point is the identity; this makes a conjugacy-invariant family of
at most two subgroups pointwise normal whenever every generator normalizes
a member.

These elementary permutation-action endpoints are used for the family of
cubic four-space actors in Aschbacher–Smith D.2.28–29, pp.191–192.
-/

public section
open Subgroup
namespace MonoidHom
variable {G X : Type*} [Group G] [Finite X]

/-- A three-point action whose kernel is a three-group containing the
three-core has a fixed point. -/
theorem exists_fixed_of_threeGroup_kernel
    (f : G →* Equiv.Perm X) (hX : Nat.card X = 3)
    (hker : IsPGroup 3 f.ker) (hcore : pCore 3 G ≤ f.ker) :
    ∃ x : X, ∀ g : G, f g x = x := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hX]; decide)
  have hA : IsPGroup 3 (alternatingGroup X) := IsPGroup.of_card (n := 1) (by
    rw [nat_card_alternatingGroup,hX]; norm_num [Nat.factorial])
  have hpre : (alternatingGroup X).comap f ≤ f.ker := by
    have hp := hA.comap_of_ker_isPGroup f hker
    exact (show (alternatingGroup X).comap f ≤ pCore 3 G from
      le_sSup ⟨inferInstance,hp⟩).trans hcore
  let s : f.range →* ℤˣ := Equiv.Perm.sign.comp f.range.subtype
  have hs : Function.Injective s := by
    apply (MonoidHom.ker_eq_bot_iff s).mp
    apply bot_unique
    intro a ha
    obtain ⟨g,hg⟩ := a.property
    have hsg : f g ∈ alternatingGroup X := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have hh : Equiv.Perm.sign (a : Equiv.Perm X) = 1 := ha
      simpa only [hg] using hh
    have hgker : f g = 1 := hpre hsg
    exact Subtype.ext (hg.symm.trans hgker)
  have htwo : IsPGroup 2 ℤˣ := by
    intro a
    refine ⟨1,?_⟩
    rcases Int.units_eq_one_or a with rfl|rfl <;> norm_num
  have hR : IsPGroup 2 f.range := htwo.of_injective s hs
  obtain ⟨x,hx⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card X (by rw [hX]; decide)
  refine ⟨x,fun g => ?_⟩
  exact hx ⟨f g,⟨g,rfl⟩⟩

/-- On at most two points, generators each having a fixed point make the
entire permutation action trivial. -/
theorem trivial_of_card_le_two_of_generators_fix_point
    (f : G →* Equiv.Perm X) (hX : Nat.card X ≤ 2)
    (S : Set G) (hS : closure S = ⊤)
    (hfix : ∀ g ∈ S, ∃ x : X, f g x = x) :
    ∀ g : G, f g = 1 := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have hgen : S ⊆ f.ker := by
    intro g hg
    obtain ⟨x,hx⟩ := hfix g hg
    change f g = 1
    ext y
    change f g y = y
    by_contra hy
    have hyx : y ≠ x := by
      intro he
      subst y
      exact hy hx
    have hxy : x ≠ f g y := by
      intro he
      exact hyx ((f g).injective (he.symm.trans hx.symm))
    have hc := Fintype.two_lt_card_iff.mpr ⟨x,y,f g y,hyx.symm,hxy,Ne.symm hy⟩
    rw [← Nat.card_eq_fintype_card] at hc
    omega
  have htop : (⊤ : Subgroup G) ≤ f.ker := hS ▸ (Subgroup.closure_le f.ker).mpr hgen
  exact fun g => htop (mem_top g)

end MonoidHom

namespace Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- An invariant family of at most two subgroups is pointwise normal if
each generator normalizes at least one member. -/
theorem normal_of_small_conjugacy_family
    (S : Set (Subgroup G))
    (hstable : ∀ D ∈ S, ∀ g : G, D.map (MulAut.conj g).toMonoidHom ∈ S)
    (hcard : Nat.card S ≤ 2)
    (T : Set G) (hT : closure T = ⊤)
    (hfix : ∀ t ∈ T, ∃ D ∈ S, t ∈ normalizer (D : Set G)) :
    ∀ D ∈ S, D.Normal := by
  let : MulAction G (Subgroup G) :=
    MulAction.compHom (Subgroup G) ConjAct.toConjAct.toMonoidHom
  let U : SubMulAction G (Subgroup G) := {
    carrier := S
    smul_mem' := fun g D hD => hstable D hD g }
  let f := MulAction.toPermHom G U
  have he : ∀ g : G, f g=1 := f.trivial_of_card_le_two_of_generators_fix_point
    hcard T hT (by
      intro t ht
      obtain ⟨D,hD,hDt⟩ := hfix t ht
      refine ⟨⟨D,hD⟩,?_⟩
      apply Subtype.ext
      exact mem_normalizer_iff_map_conj_eq.mp hDt)
  intro D hD
  apply normal_iff_map_conj_eq.mpr
  intro g
  have hh := congrArg (fun p : Equiv.Perm U => p ⟨D,hD⟩) (he g)
  exact congrArg Subtype.val hh
end Subgroup
