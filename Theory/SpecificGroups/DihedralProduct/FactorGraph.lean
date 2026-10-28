module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Central graphs of marked dihedral factors

Two commuting dihedral factors in D8×D8 whose central involutions are the
ordered coordinate axes have only central cross-coordinates. The first
projection is consequently an isomorphism on the first factor. This is the
precise finite factor-comparison step used in quasithin 13.9.10; no general
Krull--Schmidt or subgroup enumeration is needed. The only finite facts are
centralizers of noncommuting pairs in the eight-element dihedral group.
-/

public section
namespace DihedralProduct
abbrev D := DihedralGroup 4

private theorem centralizer_noncommuting : ∀a b c:D,
    a*b*a⁻¹*b⁻¹=DihedralGroup.r 2→c*a=a*c→c*b=b*c→c=1 ∨ c=DihedralGroup.r 2 := by decide +kernel
private theorem center_coordinates : ∀c:D,(∀a:D,c*a=a*c)→c=1 ∨ c=DihedralGroup.r 2 := by decide +kernel
private theorem central_halfturn : ∀a:D,DihedralGroup.r 2*a=a*DihedralGroup.r 2 := by decide +kernel
private theorem generator_commutator :
    (DihedralGroup.r 1:D)*DihedralGroup.sr 0*(DihedralGroup.r 1)⁻¹*(DihedralGroup.sr 0)⁻¹=
      DihedralGroup.r 2 := by decide +kernel

/-- Commuting marked dihedral factors have only central cross-coordinates. -/
theorem second_coordinate_central (f g:D→*D×D)
    (hg:g (DihedralGroup.r 2)=(1,DihedralGroup.r 2))
    (hcomm:∀a b,Commute (f a) (g b)) (a:D) :
    (f a).2=1 ∨ (f a).2=DihedralGroup.r 2 := by
  have hprod : (g (DihedralGroup.r 1)).2*(g (DihedralGroup.sr 0)).2*
      ((g (DihedralGroup.r 1)).2)⁻¹*((g (DihedralGroup.sr 0)).2)⁻¹=DihedralGroup.r 2 := by
    have he:=congrArg (fun x:D×D=>x.2) (congrArg g generator_commutator)
    simpa only [map_mul,map_inv,Prod.snd_mul,Prod.snd_inv,hg] using he
  exact centralizer_noncommuting _ _ _ hprod
    (congrArg Prod.snd (hcomm a (DihedralGroup.r 1)).eq)
    (congrArg Prod.snd (hcomm a (DihedralGroup.sr 0)).eq)

/-- Projection onto the distinguished factor is an isomorphism on its actual
embedded dihedral factor, once the central axes are marked. -/
theorem first_projection_bijective (f g:D→*D×D) (hf:Function.Injective f)
    (hft:f (DihedralGroup.r 2)=(DihedralGroup.r 2,1))
    (hgt:g (DihedralGroup.r 2)=(1,DihedralGroup.r 2))
    (hcomm:∀a b,Commute (f a) (g b)) :
    Function.Bijective ((MonoidHom.fst D D).comp f) := by
  let p: D→*D := (MonoidHom.fst D D).comp f
  have hker:p.ker=⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hb1:(f b).1=1:=hb
    have hbc:∀a:D,b*a=a*b := by
      intro a
      apply hf
      rw [map_mul,map_mul]
      apply Prod.ext
      · simp only [Prod.fst_mul,hb1,one_mul,mul_one]
      · rcases second_coordinate_central f g hgt hcomm b with h|h
        · simp only [Prod.snd_mul,h,one_mul,mul_one]
        · simpa only [Prod.snd_mul,h] using central_halfturn (f a).2
    rcases center_coordinates b hbc with he|he
    · exact he
    · subst b
      rw [hft] at hb1
      exact (by decide : (DihedralGroup.r 2:D)≠1) hb1 |>.elim
  have hp:Function.Injective p:=p.ker_eq_bot_iff.mp hker
  exact ⟨hp,Finite.surjective_of_injective hp⟩

/-- Each element of the first coordinate differs from an element of the first
marked factor by at most the second central involution. -/
theorem first_axis_lift (f g:D→*D×D) (hf:Function.Injective f)
    (hft:f (DihedralGroup.r 2)=(DihedralGroup.r 2,1))
    (hgt:g (DihedralGroup.r 2)=(1,DihedralGroup.r 2))
    (hcomm:∀a b,Commute (f a) (g b)) (a:D) :
    ∃b:D,f b=(a,1) ∨ f b=(a,DihedralGroup.r 2) := by
  obtain ⟨b,hb⟩:=(first_projection_bijective f g hf hft hgt hcomm).2 a
  change (f b).1=a at hb
  refine ⟨b,?_⟩
  rcases second_coordinate_central f g hgt hcomm b with h|h
  · exact Or.inl (Prod.ext hb h)
  · exact Or.inr (Prod.ext hb h)
end DihedralProduct
