module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.CoreGeometry
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionCensus.OuterModel


/-!
# Reducing the action-overgroup census to the marked outer quotient

Every candidate image contains the actual inner automorphism group, of order
256. A surjection with exactly that kernel therefore sends candidates of
order 1536 to subgroups of order six. The original Sylow action puts the same
marked transposition in both the candidate and the model image. Conjugacy in
the small quotient lifts through the surjection and gives equality of the
full subgroups, since both contain its kernel.

The marked quotient construction and the order-six subgroup calculation are
explicit, independent premises. This reduction neither constructs them nor
assumes an isomorphism of the original parabolic endpoints.

Source context: Aschbacher--Smith F.1.12 and14.2.21, printed pp.263 and988--989.
-/

@[expose] public section

noncomputable section
namespace Tits.ExceptionalParabolics.SecondCoreAction
open Subgroup

private theorem card_map_six (q : MulAut Core →* OuterModel)
    (hk : q.ker = MulAut.innerSubgroup Core) (A : Subgroup (MulAut Core))
    (hA : MulAut.innerSubgroup Core ≤ A) (hc : Nat.card A = 1536) :
    Nat.card (A.map q) = 6 := by
  have hle : q.ker ≤ A := by simpa only [hk] using hA
  have h := (q.ker.subgroupOf A).index_mul_card
  change q.ker.relIndex A * Nat.card (q.ker.subgroupOf A) = Nat.card A at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    hk,inner_card,hc] at h
  omega

/-- A marked outer quotient and its small order-six census give conjugacy of
 the original embedded action images. All extra inputs remain explicit. -/
theorem action_census_of_marked_outer_quotient
    (q : MulAut Core →* OuterModel) (hq : Function.Surjective q)
    (hk : q.ker = MulAut.innerSubgroup Core)
    (v : BinaryPair) (hv : markedTransposition v ∈ sylow.range.map q)
    (hsmall : ∀ (w : BinaryPair) (U V : Subgroup OuterModel),
      markedTransposition w ∈ U → markedTransposition w ∈ V →
      Nat.card U = 6 → Nat.card V = 6 →
      ∃ b : OuterModel, U.map (MulAut.conj b).toMonoidHom = V)
    (A : Subgroup (MulAut Core)) (hA : sylow.range ≤ A)
    (hc : Nat.card (center Core) * Nat.card A = 6144) :
    ∃ α : MulAut Core,
      A.map (MulAut.congr α).toMonoidHom = model.range := by
  have hAc : Nat.card A = 1536 := by rw [center_card] at hc; omega
  have hIA := inner_le_sylow_range.trans hA
  have hIM := inner_le_sylow_range.trans sylow_range_le_model_range
  obtain ⟨b,hb⟩ := hsmall v (A.map q) (model.range.map q)
    (map_mono hA hv) (map_mono sylow_range_le_model_range hv)
    (card_map_six q hk A hIA hAc)
    (card_map_six q hk model.range hIM model_range_card)
  obtain ⟨α,rfl⟩ := hq b
  refine ⟨α,?_⟩
  have himage : (A.map (MulAut.congr α).toMonoidHom).map q = model.range.map q := by
    rw [map_map]
    rw [map_map] at hb
    have he : q.comp (MulAut.congr α).toMonoidHom =
        (MulAut.conj (q α)).toMonoidHom.comp q := by
      apply MonoidHom.ext
      intro a
      change q (α * a * α⁻¹) = q α * q a * (q α)⁻¹
      simp only [map_mul,map_inv]
    rw [he]
    exact hb
  have hker : q.ker ≤ A.map (MulAut.congr α).toMonoidHom := by
    rw [hk,← MulAut.map_innerSubgroup_congr α]
    exact map_mono hIA
  have he := congrArg (Subgroup.comap q) himage
  rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hker,
    sup_eq_left.mpr (show q.ker ≤ model.range from by simpa only [hk] using hIM)] at he
  exact he

end Tits.ExceptionalParabolics.SecondCoreAction
