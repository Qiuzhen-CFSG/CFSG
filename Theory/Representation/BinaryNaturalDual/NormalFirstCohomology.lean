module
public import Theory.Representation.BinaryNaturalDual.FirstCohomology
public import Theory.Representation.FirstCohomologyNormalRestriction
public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Cohomology on normal subgroups of the exceptional full-four actor

The actual exceptional comparison with S₈ puts its alternating subgroup
inside every nontrivial normal subgroup. Transporting back places the inner
GL₄(2) in that subgroup. Its natural-plus-dual action has zero fixed space
and zero first cohomology, so normal restriction proves vanishing on the
original subgroup, retaining the specified coordinate action.

Source: Aschbacher--Smith I.1.5--6 and the exceptional G.10.15 source correction.
The ambient consumer is the literal layer-closure image in Chapter 6,
`RankOneModuleRecognitionIdentificationStrictExceptionalCohomology`.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology BinaryLinear.OuterCyclic
namespace BinaryNaturalDual

theorem inner_le_of_normal_ne_bot (N : Subgroup (MulAut (LinearGroup 4)))
    [N.Normal] (hN : N ≠ ⊥) : MulAut.innerSubgroup (LinearGroup 4) ≤ N := by
  let e := FourActors.permutationEquiv
  let P := N.map e.toMonoidHom
  let : P.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hp : P ≠ ⊥ := by
    intro hh
    apply hN
    apply le_bot_iff.mp
    intro g hg
    have he : e g = 1 := (mem_bot.mp (hh ▸ mem_map_of_mem e.toMonoidHom hg))
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have ha : alternatingGroup (Fin 8) ≤ P := Equiv.Perm.alternatingGroup_le_of_normal
    (by norm_num) ((Subgroup.nontrivial_iff_ne_bot P).mpr hp)
  intro g hg
  obtain ⟨k,hk,hkg⟩ := ha ((FourActors.permutationEquiv_mem_alternating g).mpr hg)
  exact e.injective hkg ▸ hk

theorem coordinateAction_normal_dual_H1_subsingleton
    (d : CoordinateAction 4) (N : Subgroup (MulAut (LinearGroup 4)))
    [N.Normal] (hN : N ≠ ⊥) :
    Subsingleton (H1 (Representation.dual (d.representation.comp N.subtype))) := by
  have hinner := inner_le_of_normal_ne_bot N hN
  let φ : LinearGroup 4 →* N := (MulAut.conj : LinearGroup 4 →* MulAut (LinearGroup 4)).codRestrict
    N (fun g => hinner ⟨g,rfl⟩)
  have hφ : φ.range = (MulAut.innerSubgroup (LinearGroup 4)).subgroupOf N := by
    ext a
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨g,rfl⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,Subtype.ext hg⟩
  let : φ.range.Normal := hφ ▸ inferInstance
  have he : ((Representation.dual (d.representation.comp N.subtype))).comp φ =
      (naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space 4)).dual := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (d.representation (φ g⁻¹).val v) = f (naturalDualRepresentation g⁻¹ v)
    rw [show (φ g⁻¹).val = MulAut.conj g⁻¹ from rfl, d.on_inner]
  let : Subsingleton (H1 (((Representation.dual (d.representation.comp N.subtype))).comp φ)) :=
    he ▸ naturalDual_dual_H1_subsingleton (by decide : 4 ≤ 4)
  apply H1_subsingleton_of_normal_range _ φ
  rw [he]
  exact naturalDual_dual_fixed_eq_bot (by decide : 2 ≤ 4)
end BinaryNaturalDual
