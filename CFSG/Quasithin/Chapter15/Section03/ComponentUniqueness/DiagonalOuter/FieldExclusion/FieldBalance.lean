module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Representative
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Source

/-!
# Field-residual balance from the marked center

The representative-centralizer bound makes the actual PSL₃(2) residual
an ordinary component in the representative centralizer inside C_G(f).
The proved two-layer balance theorem puts it in the ambient odd extended
two-layer. This discharges the balance premise of component selection.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137, applying I.3.2.
-/

public section

open Subgroup Theory.GroupTheory MulAut
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

theorem fieldResidual_balance_of_marked_center
    (I L V : Subgroup G) (f v : G)
    (hIL : I ≤ normalizer (L : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I)
    (hZ : (center L).map L.subtype = V) (hv : v ∈ V)
    (hvf : v ∈ centralizer ({f} : Set G)) (hvo : orderOf v = 2)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    fieldResidual L f ≤ oddExtendedTwoComponentLayer (centralizer ({f} : Set G)) := by
  let H := centralizer ({f} : Set G)
  let vH : H := ⟨v, hvf⟩
  let A := (fieldResidual L f).map H.subtype
  let C := H ⊓ centralizer ({v} : Set G)
  let D := centralizer ({vH} : Set H)
  obtain ⟨hAC, _, hcomp⟩ := fieldResidual_component_of_marked_center I L H V f v
    hIL hCv hZ hv le_rfl (by rw [subgroupOf_self]; exact le_top) e
  let eqC : C ≃* D := {
    toFun := fun x => ⟨⟨x, x.property.1⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
    invFun := fun x => ⟨(x : H), (x : H).property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let J := (A.subgroupOf C).map eqC.toMonoidHom
  have hJ : IsComponent D J := hcomp.map_equiv eqC
  have hmap : J.map D.subtype = fieldResidual L f := by
    apply map_injective H.subtype_injective
    rw [map_map]
    change ((A.subgroupOf C).map eqC.toMonoidHom).map
      (H.subtype.comp D.subtype) = A
    rw [map_map]
    change (A.subgroupOf C).map C.subtype = A
    exact map_subgroupOf_eq_of_le hAC
  have hp : IsPGroup 2 (zpowers vH) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hvo, pow_one])
  have hb := ChapterI.GeneralTwoOrbit.Source.twoLayerCentralizerBalance H
    (ChapterI.SylowAutomorphisms.hasTwoSchreier H) (zpowers vH) hp
  have hc : centralizer (zpowers vH : Set H) = D := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hc] at hb
  have hle := (map_mono (f := D.subtype)
    (ChapterI.Balance.ordinary_isTwoComponent hJ).le_twoComponentLayer).trans hb
  rw [hmap] at hle
  exact hle.trans le_sup_right

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
