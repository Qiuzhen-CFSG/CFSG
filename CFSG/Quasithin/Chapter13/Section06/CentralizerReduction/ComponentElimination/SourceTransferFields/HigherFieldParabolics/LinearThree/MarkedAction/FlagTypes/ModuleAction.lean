module

public import Theory.Representation.SL3RepeatedNaturalFlagTypes
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation

/-!
# The repeated-natural module excludes interchange of the source flags

The canonical moved quotient retains the action of the entire plus group. Its
binary action supplies the intertwiner for conjugation on the normal component;
transport through the actual module identification then applies the intrinsic
SL₃ flag theorem. The group coordinates are the specified marking followed by
the classifier's actual group equivalence, with no orientation requirement.

Only the repeated-natural identification of that quotient remains an explicit
premise. Its extraction from the full B.5.6 alternatives and final source assembly
belong to the independent component-action and FlagTypes branches.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the B.5.6
application before 13.6.14 and the parabolic step of 13.6.19, printed pp.929–931.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
open ComponentSelection Matrix.PSL3.LinearThree ChapterB.QuasisimpleSource

private theorem normal_action_flags
    {H V F : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [Field F] [Finite F] [CharP F 2]
    (C : Subgroup H) [C.Normal] (ρ : Representation (ZMod 2) H V)
    (e : C ≃* SL(3, F)) (h : H)
    (hU : (unipotentSL F).map (MulAut.congr e (MulAut.conjNormal h)).toMonoidHom =
      unipotentSL F)
    (hmodule : ∃ E : BinaryField, ∃ r : ℕ, 0 < r ∧
      IsRepeatedLinearNatural (ρ.comp C.subtype) E 3 r) :
    (pointParabolicSL F).map (MulAut.congr e (MulAut.conjNormal h)).toMonoidHom =
      pointParabolicSL F ∧
    (lineParabolicSL F).map (MulAut.congr e (MulAut.conjNormal h)).toMonoidHom =
      lineParabolicSL F := by
  obtain ⟨E, r, hr, ⟨c⟩⟩ := hmodule
  let d := c.linearEquiv
  let A := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom h)
  let b := d.symm.trans (A.trans d)
  let f := e.symm.trans c.groupEquiv
  have hnat (k : C) (w : V) :
      d (ρ (k : H) w) = fun i => (c.groupEquiv k).val.mulVec ((d w) i) :=
    c.intertwines k w
  have hA (w : V) : A w = ρ h w := rfl
  apply Representation.SL3RepeatedNaturalFlagTypes.flags_of_intertwiner _ hU f hr b
  intro g w
  let k := e.symm g
  have he : c.groupEquiv ((MulAut.conjNormal h) k) =
      f ((MulAut.congr e (MulAut.conjNormal h)) g) := by
    change _ = c.groupEquiv (e.symm (e ((MulAut.conjNormal h) (e.symm g))))
    rw [e.symm_apply_apply]
  calc
    b (fun i => (f g).val.mulVec (w i)) =
        d (ρ h (ρ (k : H) (d.symm w))) := by
      change d (A (d.symm (fun i => (f g).val.mulVec (w i)))) = _
      rw [hA]
      congr 2
      apply d.injective
      rw [d.apply_symm_apply, hnat, d.apply_symm_apply]
      rfl
    _ = d (ρ (((MulAut.conjNormal h) k : C) : H) (ρ h (d.symm w))) := by
      congr 1
      rw [MulAut.conjNormal_apply]
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel,
        mul_one]
    _ = fun i => (f ((MulAut.congr e (MulAut.conjNormal h)) g)).val.mulVec ((b w) i) := by
      rw [hnat, he]
      rfl

variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The module identification on the canonical moved quotient forces both exact
flag equalities for the literal Tᵥ action. The binary intertwiner comes from the
whole plus-group action on that quotient. -/
theorem modelAction_flags_of_repeated_natural
    [IsElementaryAbelian 2 (WK K L T z v)]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(3, F))
    (hmark : ((Tv T v).subgroupOf K).map
      (e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)) = unipotentSL F)
    (hmodule : ∃ E : BinaryField, ∃ r : ℕ, 0 < r ∧
      IsRepeatedLinearNatural
        ((plusComponentSection K L T z v hL hz hK hn).action.comp
          (plusImage K L T z v hL hz K).subtype) E 3 r)
    (t : Tv T v) :
    (pointParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
      pointParabolicSL F ∧
    (lineParabolicSL F).map (modelAction K L T z v hL hz hn e t).toMonoidHom =
      lineParabolicSL F := by
  let := plus_component_normal K L T z v hL hz hK hn
  have hu := modelAction_unipotentSL K L T z v hL hz hn e hmark t
  rw [modelAction_eq_conjugation K L T z v hL hz hK hn e t] at hu ⊢
  exact normal_action_flags _ (plusComponentSection K L T z v hL hz hK hn).action
    e (plusTvMap K L T z v hL hz t) hu hmodule

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction
