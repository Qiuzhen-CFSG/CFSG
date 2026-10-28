module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Movement

/-!
# The specified natural module is moved by the original component

The A6 action has no nonzero fixed vector, so its commutator is nontrivial.
The same A6 action is transitive on nonzero vectors; normality of the
commutator then makes it the entire marked module. Both equalities retain
the source subgroup and the given quotient map, also after replacement.

Source: the natural symplectic case of MS93 (3.2), printed p.863.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

omit [Finite M] in
theorem module_commutator_ne_bot : ⁅W,L⁆ ≠ ⊥ := by
  intro hbot
  have hv : (s.coordinates s.w).toAdd ∈ Representation.BinaryOffender.fixedSpace
      Model.rho (alternatingGroup (Fin 6)) := by
    intro a
    obtain ⟨l,hl,he⟩ := s.component_image.ge a.property
    have hc : MulAut.conjNormal l s.w = s.w := by
      apply Subtype.ext
      change l * (s.w : M) * l⁻¹ = s.w
      rw [commutator_eq_bot_iff_le_centralizer.mp hbot s.w.property l hl,
        mul_inv_cancel_right]
    have hh := s.action l s.w
    rw [hc,he] at hh
    exact hh.symm
  rw [Model.fixedSpace_alternating_eq_bot] at hv
  apply s.w_ne
  apply s.coordinates.injective
  apply Multiplicative.toAdd.injective
  rw [map_one]
  exact hv

omit [Finite M] in
theorem module_eq_commutator : ⁅W,L⁆ = W := by
  apply le_antisymm (commutator_le_left W L)
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp s.module_commutator_ne_bot
  let uW : W := ⟨u,commutator_le_left W L u.property⟩
  have hu0 : (s.coordinates uW).toAdd ≠ 0 := by
    intro hh
    apply hu
    have he : uW = 1 := s.coordinates.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact hh)
    exact Subtype.ext (congrArg (fun x : W => (x : M)) he)
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact one_mem _
  let xW : W := ⟨x,hx⟩
  have hx0 : (s.coordinates xW).toAdd ≠ 0 := by
    intro hh
    apply hx1
    have he : xW = 1 := s.coordinates.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact hh)
    exact congrArg Subtype.val he
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (s.coordinates uW).toAdd (s.coordinates xW).toAdd hu0 hx0
  obtain ⟨l,hl,hql⟩ := s.component_image.ge a.property
  have he : MulAut.conjNormal l uW = xW := by
    apply s.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [s.action,hql]
    exact ha
  have hv : l * (u:M) * l⁻¹ = x := congrArg Subtype.val he
  rw [← hv]
  exact (inferInstance : (⁅W,L⁆ : Subgroup M).Normal).conj_mem _ u.property l

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
