module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner action from the symmetric-three shadow

Every abelian image of a group with two-core quotient S₃ is a two-group:
each square in S₃ is a commutator, so the square of an abelian image lifts
to the two-core. The two-perfect subgroup Y₊ therefore has trivial image
in the actual outer group of L*. Relative normality defines conjugation
on L*, and triviality in Aut(L*)/Inn(L*) gives the literal inner action.

The model outer-group calculation is separate; this module does not assume
Y₊ ≤ L or identify the whole star quotient with its Thompson subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(2), printed p.1131, case (i).
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison

private theorem commutative_image_two_group
    {H A : Type*} [Group H] [Group A] [IsMulCommutative A]
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) (f : H →* A) :
    IsPGroup 2 f.range := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : ∀ s : Equiv.Perm (Fin 3), ∃ a b : Equiv.Perm (Fin 3), s ^ 2 = ⁅a, b⁆ := by
    decide +kernel
  rintro ⟨z, g, rfl⟩
  obtain ⟨a, b, hab⟩ := hs (q g)
  obtain ⟨x, rfl⟩ := hq a
  obtain ⟨y, rfl⟩ := hq b
  have hk : g ^ 2 * ⁅x, y⁆⁻¹ ∈ pCore 2 H := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change q (g ^ 2 * ⁅x, y⁆⁻¹) = e 1
    rw [map_mul, map_pow, map_inv, map_commutatorElement, hab, mul_inv_cancel, map_one]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨_, hk⟩
  have hpow : (g ^ 2 * ⁅x, y⁆⁻¹) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hfxy : f ⁅x, y⁆ = 1 := by rw [map_commutatorElement]; exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hf := congrArg f hpow
  simp only [map_pow, map_mul, map_inv, hfxy, inv_one, mul_one, map_one] at hf
  refine ⟨n + 1, Subtype.ext ?_⟩
  change f g ^ (2 ^ (n + 1)) = 1
  rw [pow_succ, mul_comm (2 ^ n) 2, pow_mul]
  exact hf

private theorem hom_eq_one_of_twoPerfect {Y A : Type*} [Group Y] [Group A]
    (hp : IsPPerfect 2 Y) (f : Y →* A) (hA : IsPGroup 2 A) (y : Y) : f y = 1 := by
  have hq : IsPGroup 2 (Y ⧸ f.ker) :=
    (hA.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk := hp f.ker inferInstance hq
  exact (show y ∈ f.ker from hk ▸ mem_top y)

/-- Abelian outer automorphisms of the actual star component, together with
its genuine S₃ shadow, force the displayed conjugations to be inner. -/
theorem inner_action_of_shadow {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hn : (c.L.subgroupOf I).Normal)
    (ho : IsMulCommutative (MulAut.Outer (d.starImage I c.L))) :
    ∀ y : d.starImage I d.Yplus, ∃ l : d.starImage I c.L,
      ∀ x : d.starImage I c.L,
        (l : d.Star I) * x * l⁻¹ = y * x * y⁻¹ := by
  let L := d.starImage I c.L
  let : L.Normal := hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  let := ho
  let f : (d.Yplus ⊔ d.S : Subgroup G) →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp
      (MulAut.conjNormal.comp ((d.starMap I).comp (inclusion hI.1.2)))
  obtain ⟨e⟩ := h.shadow
  have hp := commutative_image_two_group e f
  have hY : IsPPerfect 2 d.Yplus := by
    rw [h.choice.2, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact isPPerfect_embedded_pResidual 2 _
  let j : d.Yplus →* f.range := f.rangeRestrict.comp (inclusion le_sup_left)
  intro y
  obtain ⟨i, hi, hy⟩ := y.property
  let a : d.Yplus := ⟨i, hi⟩
  have hja : j a = 1 := hom_eq_one_of_twoPerfect hY j hp a
  have hf : f ⟨i, mem_sup_left hi⟩ = 1 := congrArg Subtype.val hja
  have hs : MulAut.conjNormal (H := L) (y : d.Star I) ∈ MulAut.innerSubgroup L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (MulAut.innerSubgroup L)
      (MulAut.conjNormal ((d.starMap I) i)) = 1 at hf
    rwa [hy] at hf
  obtain ⟨l, hl⟩ := hs
  refine ⟨l, fun x => ?_⟩
  exact congrArg (fun a : MulAut L => ((a x : L) : d.Star I)) hl


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison
