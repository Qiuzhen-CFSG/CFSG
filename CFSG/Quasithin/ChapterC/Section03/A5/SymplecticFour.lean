module
public import CFSG.Quasithin.ChapterC.Section03.A5.NaturalExtension
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover

/-!
# Deleted-five blocks do not embed in symplectic four-space

The normalizer of the block's nontrivial elementary commutator layer is a
two-local. The radical of its common fixed space puts that normalizer in a
conjugate point or plane parabolic. Perfectness places the block inside the
determinant kernel, where the actual natural-extension action contradicts
the deleted-five module's cubic fixed vector.

The argument works over every field of order 2^n with n > 1. It does not
assume a bound on an ambient Sylow subgroup, self-centralization of the
block layer, or normalizer control. The final containing-subgroup theorem
uses the original subgroup inclusion and the catalogue's projective model.
Source: Aschbacher--Smith 2.4.25, printed p.543, the general Sp₄(2^n) row.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
variable {F A : Type*} [Field F] [Finite F] [Group A]

/-- No actual alternating-five block injects into the symplectic four-space model. -/
theorem no_alternatingFive_in_symplecticFour
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hA : IsAlternatingBlock A 5) (i : A →* Sp F) (hi : Function.Injective i) : False := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let := hA.2.1.elementary
  let := hA.perfect_five
  let U := (blockU A).map i
  let N := normalizer (U : Set (Sp F))
  have hU : U ≠ ⊥ := by
    intro he
    have hb := ((blockU A).map_eq_bot_iff_of_injective hi).mp he
    have hh := hA.2.1.irreducible.1
    simp only [hb,bot_inf_eq,lt_self_iff_false] at hh
  have h2 : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 (blockU A)).map i
  have hN : IsTwoLocal N := ⟨U,hU,h2,rfl⟩
  have hiN : i.range ≤ N := by
    have h := Subgroup.le_normalizer_map (H := blockU A) i
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] using h
  obtain ⟨g,hg⟩ := twoLocal_parabolic_cover_of_charTwo N hN
  let j := (MulAut.conj g).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hi
  have hjN : j.range ≤ N.map (MulAut.conj g).toMonoidHom := by
    rintro _ ⟨x,rfl⟩
    exact mem_map_of_mem _ (hiN ⟨x,rfl⟩)
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hpt | hpl
  · have hl : j.range ≤ pointLocal :=
      (le_map_solvableResidual_of_isPerfect j.range pointParabolic (hjN.trans hpt)).trans
        (determinantKernel_solvableResidual_le (point F))
    let k := j.codRestrict pointLocal (fun x => hl ⟨x,rfl⟩)
    exact no_alternatingFive_in_naturalExtension (pointNaturalExtension hF hn) hA k
      (fun x y h => hj (congrArg Subtype.val h))
  · have hl : j.range ≤ planeLocal :=
      (le_map_solvableResidual_of_isPerfect j.range planeParabolic (hjN.trans hpl)).trans
        (determinantKernel_solvableResidual_le (plane F))
    let k := j.codRestrict planeLocal (fun x => hl ⟨x,rfl⟩)
    exact no_alternatingFive_in_naturalExtension (planeNaturalExtension hF hn) hA k
      (fun x y h => hj (congrArg Subtype.val h))

/-- The intrinsic subgroup obstruction is unchanged by a group isomorphism. -/
theorem no_alternatingFive_of_symplecticFour_equiv
    {G : Type*} [Group G] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : G ≃* Sp F) (A : Subgroup G) (hA : IsAlternatingBlock A 5) : False :=
  no_alternatingFive_in_symplecticFour hF hn hA (e.toMonoidHom.comp A.subtype)
    (e.injective.comp A.subtype_injective)

/-- An actual containing subgroup cannot carry the symplectic four-space model. -/
theorem no_symplecticFour_subgroup_containing_alternatingFive
    {G : Type*} [Group G] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (A X : Subgroup G) (hA : IsAlternatingBlock A 5) (hAX : A ≤ X)
    (e : X ≃* Sp F) : False :=
  no_alternatingFive_in_symplecticFour hF hn hA ((e.toMonoidHom).comp (inclusion hAX))
    (e.injective.comp (inclusion_injective hAX))
end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
open Theory.SpecificGroups.SymplecticFour

/-- The catalogue's projective symplectic model has the same obstruction. -/
theorem no_alternatingFive_of_isPSp
    {G : Type*} [Group G] {n : ℕ} (hn : 1 < n)
    (hG : ClassicalGroup.IsPSp G 2 (2 ^ n))
    (A : Subgroup G) (hA : IsAlternatingBlock A 5) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hG
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact no_alternatingFive_of_symplecticFour_equiv hF hn
    (e.trans (EvenProjective.equiv (F := F)).symm) A hA

/-- Source application to the original block inside an actual containing subgroup. -/
theorem no_isPSp_subgroup_containing_alternatingFive
    {G : Type*} [Group G] {n : ℕ} (hn : 1 < n)
    (A X : Subgroup G) (hA : IsAlternatingBlock A 5) (hAX : A ≤ X)
    (hX : ClassicalGroup.IsPSp X 2 (2 ^ n)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hX
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact no_symplecticFour_subgroup_containing_alternatingFive hF hn A X hA hAX
    (e.trans (EvenProjective.equiv (F := F)).symm)
end CFSG.Quasithin.ChapterC
