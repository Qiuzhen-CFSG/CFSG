module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The actual offender branch in Theorem 3.1.8

If the elementary Thompson subgroup of T moves a normal elementary
module V, a maximum elementary subgroup supplies an FF-offender. We
apply the original cardinal inequality inside H, then identify its
centralizer-quotient action with the literal conjugation image on V.
No qrc rank bound or Baumann alternative is assumed in this branch.

Source: Aschbacher–Smith, Theorem 3.1.8(3i), by B.2.7, combined manuscript
of 1 March 2004, printed p.576.
-/

public section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G]

theorem internalActionImage_isFFModule_of_thompson_not_le
    (T : Sylow 2 G) (H V : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hVT : V ≤ (T : Subgroup G))
    (hn : H ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V]
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    IsFFModule (ChapterD.UniqueFactor.imageRepresentation H V hn) := by
  let W := V.subgroupOf H
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf (hVT.trans hTH)
  let f := ChapterD.UniqueFactor.actionHom H V hn
  let q := f.rangeRestrict
  have hq : Function.Surjective q := MonoidHom.rangeRestrict_surjective f
  have hk : q.ker = centralizer (W : Set H) := by
    rw [MonoidHom.ker_rangeRestrict, ChapterD.UniqueFactor.actionHom_ker]
    ext g
    constructor
    · intro hg v hv
      exact Subtype.ext (hg v hv)
    · intro hg v hv
      exact congrArg H.subtype (hg ⟨v, hTH (hVT hv)⟩ hv)
  let S : Sylow 2 H := T.subtype hTH
  have hJS : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤ q.ker := by
    intro hh
    apply hJ
    have hm := map_mono hh (f := H.subtype)
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      show (S : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le hTH] at hm
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hm hx
    change g ∈ f.rangeRestrict.ker at hg
    rw [MonoidHom.ker_rangeRestrict] at hg
    rw [ChapterD.UniqueFactor.actionHom_ker] at hg
    exact hg
  let ρ := Representation.NormalElementaryQuotient.representation W q hq hk
  have hff : IsFFModule ρ :=
    Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le W q hq hk
      (S : Subgroup H) (fun v hv => hVT hv) hJS
  let e := subgroupOfEquivOfLe (hVT.trans hTH)
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  apply hff.map_equivariant ρ (ChapterD.UniqueFactor.imageRepresentation H V hn)
    (MonoidHom.id _) Function.injective_id E
  intro a v
  obtain ⟨g, rfl⟩ := hq a
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((ρ (q g) v).toMul.val : G) =
    (g : G) * (v.toMul.val : G) * (g : G)⁻¹
  exact congrArg H.subtype
    (Representation.NormalElementaryQuotient.representation_apply W q hq hk g v)

end CFSG.Quasithin.Chapter3
