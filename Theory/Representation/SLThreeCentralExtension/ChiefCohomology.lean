module

public import Theory.Representation.SLThreeCentralExtension.Involutions
public import Theory.SpecificGroups.BinaryLinear.Perfect

/-!
# First cohomology of four-dimensional natural central covers

For a commutator-generated four-dimensional central cover of the natural
SL₃(2) module, every cocycle is principal. At an involution its value is
fixed, hence is a displacement by the rank-two involution calculation.
The projected natural cocycle therefore has zero spare coordinate at an
elementary transvection. The checked natural cocycle normal form makes it
principal. Subtracting a lift leaves a central-valued cocycle, which is
zero because SL₃(2) is perfect.

This gives a cohomological alternative to the five-dimensional exclusion
in Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4), printed
pp.91–92. It uses the previously proved B.4.8(1)–(2) calculations and does
not use the dimension bound or any result depending on it.
-/

public section

open Representation Representation.BinaryOffender
open Representation.OneCohomology
open Matrix.SpecialLinearGroup

namespace Representation.OneCohomology.SLThreeCentralExtension

/-- The actual actor of the natural binary three-space is perfect. -/
theorem actor_isPerfect : Group.IsPerfect BinaryLinearThree.Group := by
  let := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  exact Group.IsPerfect.ofSurjective
    (f := (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom)
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

private lemma cocycle_one (ρ : Representation (ZMod 2) D V) (f : cocycles ρ) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h

private lemma fixed_cocycle_zero [Group.IsPerfect D] (ρ : Representation (ZMod 2) D V)
    (f : cocycles ρ) (hf : ∀ g, f.val g ∈ OneCohomology.fixed ρ) : f = 0 := by
  let q : D →* Multiplicative V :=
    { toFun := fun g => Multiplicative.ofAdd (f.val g)
      map_one' := cocycle_one ρ f
      map_mul' := by
        intro g h
        change f.val (g*h) = f.val g + f.val h
        rw [f.property, hf h g, add_comm] }
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  apply Subtype.ext
  funext g
  have h := Subsingleton.elim (⟨q g, ⟨g,rfl⟩⟩ : q.range) 1
  exact congrArg (fun x : q.range => Multiplicative.toAdd x.val) h

variable [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) BinaryLinearThree.Group V)

/-- Every first cocycle of a four-dimensional central natural cover is principal. -/
theorem H1_subsingleton_of_four_dimensional_cover
    (p : σ.IntertwiningMap BinaryLinearThree.W) (hp : IsCover p)
    (hdim : Module.finrank (ZMod 2) V = 4) : Subsingleton (H1 σ) := by
  let : Group.IsPerfect BinaryLinearThree.Group := actor_isPerfect
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  let c : cocycles BinaryLinearThree.W := ⟨fun g => p (f.val g), by
    intro g h
    change p (f.val (g*h)) = _
    rw [f.property, map_add, p.isIntertwining]⟩
  let t : BinaryLinearThree.Group := transvection (show (0 : Fin 3) ≠ 1 by decide) 1
  have ht2 : t * t = 1 := by decide
  have htorder : orderOf t = 2 := by
    apply orderOf_eq_prime
    · simpa only [pow_two] using ht2
    · decide
  have hff : f.val t ∈ fixedSpace σ (Subgroup.zpowers t) := by
    rw [mem_fixedSpace_zpowers_iff]
    have he := f.property t t
    rw [ht2, cocycle_one] at he
    have hz : f.val t + f.val t = 0 := by
      rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact add_right_cancel (he.symm.trans hz.symm)
  have hr := (BinaryLinearThree.NaturalExtension.involution_range_eq_fixed σ hdim t htorder
    (BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top σ hdim hp.2.2 t htorder)).1
  rw [← hr] at hff
  obtain ⟨x,hx⟩ := hff
  have hct : c.val t 2 = 0 := by
    have he := congrArg p hx
    change p (σ t x - x) = p (f.val t) at he
    rw [map_sub, p.isIntertwining] at he
    have hcoord := congrArg (fun w : BinaryLinearThree.Vector => w 2) he
    change _ = c.val t 2 at hcoord
    rw [show BinaryLinearThree.W t (p x) = p x + Pi.single 0 ((p x) 1) from by
      simpa only [one_mul] using SLHigherNatural.action_transvection
        (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) (p x)] at hcoord
    simpa using hcoord.symm
  obtain ⟨a,v,hc⟩ := SLHigherNatural.SLThreeBinary.normal_form c
  have ha : a = 0 := by
    have hh := congrArg (fun z : cocycles BinaryLinearThree.W => z.val t 2) hc
    change c.val t 2 = a * SLHigherNatural.SLThreeBinary.exceptional.val t 2 +
      (principal BinaryLinearThree.W v).val t 2 at hh
    rw [hct, SLHigherNatural.SLThreeBinary.exceptional_spare 0 1 2
      (by decide) (by decide) (by decide), SLHigherNatural.principal_transvection] at hh
    simpa using hh.symm
  rw [ha, zero_smul, zero_add] at hc
  obtain ⟨w,hw⟩ := hp.1 v
  have hfixed : ∀ g, (f - principal σ w).val g ∈ OneCohomology.fixed σ := by
    intro g
    apply hp.2.1
    change p (f.val g - (σ g w - w)) = 0
    rw [map_sub, map_sub, p.isIntertwining, hw]
    have hh := congrArg (fun z : cocycles BinaryLinearThree.W => z.val g) hc
    exact sub_eq_zero.mpr hh
  have he := fixed_cocycle_zero σ (f - principal σ w) hfixed
  exact ⟨w, (sub_eq_zero.mp he).symm⟩

end Representation.OneCohomology.SLThreeCentralExtension
